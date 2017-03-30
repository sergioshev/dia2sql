#!/usr/bin/perl
#
# dia2sql.pl - version 1.2 - 2001/03/20
# Entity-relationship with UML diagrams from Dia
#
# Copyright (c) 2001 by Alexander Troppmann
# http://www.cocktaildreams.de - talex@karyopse.de
# 
# Copyright (c) 2003, 2004, 2005 Hugo J. Curti
#
# This program releases under the GNU Public License;
# You can redistribute it or modify it under the terms of GPL.
#
# Featurelist:
# - Creates a table for each UML class
# - All attributes of a Dia UML class will be converted to SQL statements:
#   "Name" = SQL column name,
#   "Type" = SQL datatype and also additional attributes,
#   "Visibility" = if set to "protected" the attribute will be a primary key
#   "Value" = if set a default value will be defined for this column
# - DROP TABLE statement can be created
# - For each column starting with "FK_" a foreign key constraint will be
#   created (PostgreSQL only). Do not use "REFERENCES" attributes in the UML
#   diagram!
# - Support for indexed columns (PostgreSQL only)
#
# Required stuff:
# - First get the expat library (> v1.95.0) as RPM package or from
#   http://www.jclark.com/xml/expat.html which is a XML1.0 parser written in C.
# - Second install XML::Parser from CPAN, just type in at your shell prompt:
#
#      root@localhost:~ > perl -MCPAN -e 'install XML::Parser'
#
# That's all! :-)

use XML::Parser;

$VERSION = 'dia2sql.pl v1.2_local';


###########################################################
## CONFIG - MAKE ANY CHANGES HERE

$DEBUG = 1;		# 1 if you want to get debug messages to STDERR
$CREATECOMMENTS = 0;	# 1 if you want to get comments like mysqldump does

$MYSQL = 0;		# choose either MySQL or PostgreSQL support
$POSTGRESQL = 1;	# by setting 0 and 1 values here

$CREATEDROPTABLES = 0;	# 1 if you want to have "DROP TABLE" statements

if($MYSQL) {
	$DROPTABLE = "DROP TABLE IF EXISTS"; # DROP TABLE statement to be used
} elsif($POSTGRESQL) {
	$DROPTABLE = "DROP TABLE";
	$CREATEFKSFROMDBNAMING = 1;  # creates REFERENCE for FK_ columns
} else {
	die "ERROR: You didn't choose a database!\n";
}


###########################################################
## VARIABLES

$table = 0;				# 1 if inside table
$tablename = 0;			# 1 if tablename tag detected
$column = 0;			# 1 if inside column
$columnname = 0;		# 1 if columnname detected
$columntype = 0;		# 1 if datatype for column detected
$columnvi = 0;			# 1 if "visibility" for primary key definitions
$columnvalue = 0;		# 1 if value attribute detected

undef($myTablename);		     # current table
undef(%myTableContents);	     # hash with columns for a certain table
undef(%myKeyMarker);		     # marker for primary keys
undef(%myIndexMarker);		     # marker for indexed column
undef(%myPrimaryKeys);		     # hash with primary keys for a
                                     # certain table
undef(%mySimpleForeigns);            # hash with fields for foreign keys for
                                     # the indexed tables (simple keys).
                                     # list of (column, table, actions).
undef(%myCompositeCardinalForeigns); # hash of ((list of columns), table,
                                     # (list of dest columns), actions)
                                     # indexed by ortable,desttable,cardinal
                                     # (complex isn't it?).
undef(%myCompositeForeigns);         # hash of list of references to the
                                     # previous structure indexed by
                                     # table.

undef(%myIndexColumns);		     # columns for index
undef($myColumnvalue);		     # default value for datatype
undef($myTableUsesIndizes);	     # is my current table using 
                                     # indexed columns?
undef(@myTables);		     # list of tables to build

undef(%myInheritance);               # hash indexed by table that saves the
                                     # list of parents of each table.

undef(%myUCInheritance);             # hash indexed by normalized table name 
                                     # that saves the list of parents of 
                                     # each table.

undef(%myInheritConstraints);        # Hash indexed by "from,to" where from
                                     # and to are normalized table names
                                     # and defines wether the key constraints
                                     # are inherited or not.


undef(%myMarkedForBuildTables);      # hash indexed by normalized table name
                                     # that saves the 'Builded' flag for the
                                     # buildPostOrder sub.

sub addColumnConstraints {
    # We search for the 'not null', 'unique' and 'check()' clauses. The check()
    # should be at the end. If anything beyond spaces is present after the
    # parse, the 'DEFAULT' clause is generated.

    my $valueText = shift ;
    my $result = "" ;

    if( $valueText =~ 
	s/^(.*[[:space:]]+)?(not[[:space:]]+null)([[:space:]]+(.*))?$/\1\4/gi ) {

	$result = " NOT NULL" ;
    }

    if( $valueText =~ 
	s/^(.*[[:space:]]+)?(unique)([[:space:]]+(.*))?$/\1\4/gi ) {

	$result = " UNIQUE".$result ;
    }

    if( $valueText =~ 
	s/^((.*)[[:space:]]+)?check[[:space:]]*\((.*)\).*$/\2/gi ) {

	$result = " CHECK(".$3.")".$result ;
    }

    $valueText =~ s/^[[:space:]]*// ;
    $valueText =~ s/[[:space:]]*$// ;

    if( length $valueText ) {
	$result = " DEFAULT ".$valueText.$result ;
    }

    $result =~ s/\\\'/\'/g ;
    $result =~ s/\\\"/\"/g ;
    return $result ;
}

sub parseAction {

    my $FK = $_[0] ;

    $FK =~ /^(.)/ ;
    my $action= $1 ;

    return $action =~ /u/i ? "UPDATE" : "DELETE" ;
}

sub parseRestriction {
    my $FK = $_[0] ;

    $FK =~ /^.(.)/ ;
    my $restriction = $1 ;

    $restriction =~ /c/i && return "CASCADE" ;
    $restriction =~ /d/i && return "SET DEFAULT" ;
    $restriction =~ /n/i && return "SET NULL" ;
    $restriction =~ /r/i && return "RESTRICT" ;
    return "NO ACTION" ;
}

sub parseFK {

    my ( $ORIGTABLE , $DESTTABLE , $FK1 , $FK2 ) = @_ ;

    my $action1 ="N";
    my $action2 ="NN" ;

    if( defined $FK1 ) { $action1 = &parseAction($FK1) ; }
    if( defined $FK2 ) { $action2 = &parseAction($FK2) ; }

    if ( $action1 eq $action2 ) {
	print STDERR "WARNING: Same action specified twice in a reference " ,
	"$ORIGTABLE => $DESTTABLE\n" ;
	return undef ;
    }

    my $textResult ;

    unless( $action1 eq "N" ) {
	$textResult = " ON $action1 ".&parseRestriction($FK1) ;
    }

    unless( $action2 eq "NN" ) {
	$textResult .= " ON $action2 ".&parseRestriction($FK2) ;
    }

    return $textResult ;

}

sub addForeign {

    my ( $myTablename , $myColumnname ) = @_ ;

    my $fktext ;
    my $fktable ;
    my $fkcardinal ;
    my $fkdestfield ;
    my $fkfield ;
    my $fkc1 ;
    my $fkc2 ;

    if ( $myColumnname =~ 
	 /^FK_([a-z0-9._]+)((\#([0-9]+))?\#([a-z0-9_]+))?(!([a-z0-9_]+))?(@([ud][ircnd])([ud][ircnd])?)?$/i ) {
	( $fktable, $fkcardinal, $fkdestfield, $fkfield, $fkc1, $fkc2 ) = 
	    ($1,$4,$5,$7,$9,$10) ;

	$fktext = &parseFK( $myTablenname , $fktable , 
			    $fkc1 , $fkc2 ) ;

	if($DEBUG) {
	    print STDERR "ADDFOREIGN: table=$fktable, ".
		"cardinal=$fkcardinal, ".
		"destfield=$fkdestfield, ".
		"field=$fkfield, ".
		"fkc1=$fkc1, fkc2=$fkc2, fktext=$fktext\n" ;
	}


	if( $fkdestfield ) {
	    # Detination field provided, assume a composed foreign key.
	    # Multiple references to one table applies to the same
	    # foreign key unless a different cardinal is specified.

	    unless( $fkfield ) {
		$fkfield = $fktable.$fkcardinal."_".$fkdestfield ;
	    }

	    my $fkindex = uc "$myTablename,$fktable,$fkcardinal" ;

	    print STDERR "ADDFOREIGN: index=$fkindex\n" ;

	    my $listref = \$myCompositeCardinalForeigns{$fkindex} ;

	    if ( $$listref ) {
		push @{$$$listref[0]} , $fkfield ;
	        push @{$$$listref[2]} , $fkdestfield ;
		if ( $fktext ) {
		    $$$listref[3] = $fktext ;
		    print STDERR "WARNING: Duplicate integrity constraint".
			"in $myTablename.$fkfield => $fktable.$fkdestfield".
			" reference.\n   Previous declaration ignored.\n" ;
		}

	    } else {
		# No previous reference.
		push @{$myCompositeForeigns{uc $myTablename}}, $listref ;

		@{$$listref} = ( [$fkfield] , $fktable , 
				 [$fkdestfield] , $fktext ) ;
	    }

	    if($DEBUG) {
		print STDERR "ADDFOREIGN: Adding Composite Foreign key ".
		    "$fkfield => $fktable with $fktext to $myTablename.\n" ;
	    }

	} else {
	    # Destination field not provided, assume a single foreign key.
	    # Different references to the same table applies to different
	    # foreign keys.

	    unless( $fkfield ) { 
	      $fkfield = $fktable ;
	      $fkfield =~ s/\./_/g;
	    }

	    push @{$mySimpleForeigns{uc $myTablename}} ,
	        [ $fkfield , $fktable , $fktext ] ;

	    if( $DEBUG ) {
		print STDERR "ADDFOREIGN: Adding Simple Foreign key ".
		    "$fkfield => $fktable with $fktext to $myTablename.\n" ;
	    }
	}

    } else {
	print STDERR "WARNING: Foreign key constraint ".
	    "parsing error at '$myColumnname'\n" ;
    }

    return $fkfield ;

}


###########################################################
## INIT

## get infile (and outfile) from command line
#
if(@ARGV < 1) {

	die <<"_USAGE_END_"
Usage: dia2sql.pl file.dia [file.sql]

$VERSION - (c) 2001 by Alexander Troppmann

Converts xml data input from Dia to sql statements. If file.sql is not
specified the sql statements will be printed to STDOUT.

Edit dia2sql.pl and change the configuration at top of the Perl script.
Make sure you have defined the right database (MySQL or PostgreSQL) for
SQL output.

_USAGE_END_

} else {

	$infile = shift;	# input file, Dia XML formatted
	$outfile = shift;	# output file, filled with SQL statements
	
	if($outfile) {
		open(STDOUT, ">$outfile") or die "$outfile: $!n";
	}
	
}

if($MYSQL) {
	if($DEBUG) { print STDERR "Creating SQL output for MySQL\n"; }
} elsif($POSTGRESQL) {
	if($DEBUG) { print STDERR "Creating SQL output for PostgreSQL\n"; }
}


## init xml parser and parse input file
#
$parser = new XML::Parser(Style => 'Stream');
$parser->parsefile($infile);


## create sql output
#
&createSql();


## cleanup and exit
#
if($outfile) {
	close(STDOUT);
}

exit;


###########################################################
## SUB ROUTINES

## called if parser enters new tag
#
$prefix = '';	# patch for Dia v0.83 by Georges Khaznadar

sub StartTag {
	
    my $p = shift;			# parser context
    $ctag = shift;			# name of this tag element
    %attr = %_;			# hash with attributes
	
    if($ctag eq 'dia:diagram') {
	# then all other tags will be prefixed with dia:
	# (patch for Dia v0.83 by Georges Khaznadar)
	$prefix = 'dia:';
	if($DEBUG) { print STDERR "dia: patch enabled!\n"; }
    }
	
    if($ctag eq $prefix.'object' and $attr{'type'} eq 'UML - Class') {
	$table = 1;
	$myTableUsesIndizes = 0;
    } elsif($ctag eq $prefix.'composite' and
	    $attr{'type'} eq 'umlattribute' and $table) {
	$column = 1;
    } elsif($table and $ctag eq $prefix.'attribute' and
	    $attr{'name'} eq 'name' and !$column) {
	$tablename = 1;
    } elsif($column and $ctag eq $prefix.'attribute' and
	    $attr{'name'} eq 'name' and !$tablename) {
	$columnname = 1;
    } elsif($column and $ctag eq $prefix.'attribute' and
	    $attr{'name'} eq 'value' and $column) {
	$columnvalue = 1;
    } elsif($column and $ctag eq $prefix.'attribute' and
	    $attr{'name'} eq 'type') {
	$columntype = 1;
    } elsif($column and $ctag eq $prefix.'attribute' and 
	    $attr{'name'} eq 'visibility') {
	$columnvi = 1;
    } elsif($columnvi and $ctag eq $prefix.'enum') {
	if($attr{'val'} == 2) { 
	    $myKeyMarker = 1; 
	} else { 
	    $myKeyMarker = 0; }
	if($attr{'val'} == 1) { 
	    $myIndexMarker = 1; }	# index column found
	else { $myIndexMarker = 0; }
    }

}

## called if parser leaves a tag
#
sub EndTag {
    
    my $p = shift;
    $ctag = shift;

    if($ctag eq $prefix.'object' and $table) {

	$table = 0;
	$myTableUsesIndizes = 0;
	push @myTables, $myTablename;
	
    } elsif($ctag eq $prefix.'composite' and $column) {
	
	$column = 0;

	if($CREATEFKSFROMDBNAMING and $myColumnname =~ /^FK_/) {
	    $myColumnname = &addForeign( $myTablename ,
					 $myColumnname) ;
	    if($DEBUG) { print STDERR "Foreign key found!\n".
			     "REF: Input reference: '$treference'\n"; }
	}

	my $sql = "$myColumnname $myColumntype";
	
	if($myKeyMarker) {
	    push @{$myPrimaryKeys{uc $myTablename}}, "$myColumnname";
	    if($MYSQL) {
		$sql .= " NOT NULL";
	    }
	}
	
	if($myIndexMarker and $POSTGRESQL) {
	    push @{$myIndexColumns{$myTablename}}, "$myColumnname";
	    $myTableUsesIndizes = 1;
	    if($DEBUG) { print STDERR "Indexed column found!\n"; }
	}
	
	if(not $myColumnvalue eq "" ) {
	    $sql .= &addColumnConstraints($myColumnvalue) ;
	}

	undef($myColumnvalue);
	
	push @{$myTableContents{$myTablename}}, $sql;
	if($DEBUG) { print STDERR "Added new column data \"$sql\"\n"; }
	
    } elsif($ctag eq $prefix.'attribute' and $tablename) {
	$tablename = 0;
    } elsif($ctag eq $prefix.'attribute' and $column and $columnname) {
	$columnname = 0;
    } elsif($ctag eq $prefix.'attribute' and $column and $columnvalue) {
	$columnvalue = 0;
    } elsif($ctag eq $prefix.'attribute' and $column and $columntype) {
	$columntype = 0;
    } elsif($ctag eq $prefix.'enum' and $column and $columnvi) {
	$columnvi = 0;
    }
    
}


## called for text between any tags
#
sub Text {
	
    $text = $_;
	
    if($text =~ /^\s+$/) { return; }	# skip whitespaces

    if( $ctag eq $prefix.'string' and $tablename ) {
	my @inheritanceList ;
	my @inheritsConstraintsList ;

	# remove hash characters
	$text =~ s/(^\#|\#$)//g ;
	while( $text =~ s/^(.+)@(\*)?([^@]+)$/\1/g ) {
	    my ( $noInheritsConstraints , $parentTable ) = ( $2 , $3 ) ;

	    unless ( $noInheritsConstraints ) {
		unshift @inheritsConstraintsList , $parentTable ;
	    }

	    unshift @inheritanceList , $parentTable ;
	}

	$myTablename = $text ;
	$myInheritance{$myTablename} = \@inheritanceList ;
	$myUCInheritance{uc $myTablename} = \@inheritanceList ;
	$myInheritsConstraints{uc $myTablename} = \@inheritsConstraintsList ;

	if($DEBUG) { 
	    print STDERR "\nTABLE: Table: $myTablename\n"; 
	    print STDERR "TABLE: Inherits: ".
		join( "," , @{$myInheritance{$myTablename}})."\n" ;
	    print STDERR "TABLE: Inherits constraints: ".
		join( "," , @{$myInheritsConstraints{uc $myTablename}})."\n" ;
	}

    } elsif($ctag eq $prefix.'string' and $columnname) {
	$text =~ s/(^\#|\#$)//g;        # remove hash characters
	$myColumnname = $text;
	if($DEBUG) { print STDERR "Columnname: $myColumnname\n"; }
    } elsif($ctag eq $prefix.'string' and $columnvalue) {
	$text =~ s/(^\#|\#$)//g;
	$text =~ s/(\'|\")/\\$1/sg;
	$myColumnvalue = $text;
	if($DEBUG) { print STDERR "Columnvalue: $myColumnvalue\n"; }
    } elsif($ctag eq $prefix.'string' and $columntype) {
	$text =~ s/(^\#|\#$)//g;        # remove hash characters
	$myColumntype = $text;
	if($DEBUG) { print STDERR "Columntype: $myColumntype\n"; }
    }
	
}

## create sql output
#
sub createSql {
	
  my($columns,$keys,$sql,$date);

  if($DEBUG) { print STDERR "\nWriting SQL statements...\n"; }
  if($CREATECOMMENTS) {
    $date = `date`; chop($date);
    print "# Created by $VERSION (".$date.")\n\n";
  }

  if($DEBUG) { print STDERR "\nBuild tables in postorder.\n" }
  &buildPostOrder(@myTables) ;

  if($DEBUG) { print STDERR "\nBuild foreign keys.\n" }
  foreach my $I ( @myTables ) {
    # Build my inherited references.
    &buildRecursiveForeign( $I , $I ) ;
    # Now build my own references.
    &buildForeigns($I) ;
  }

  if($DEBUG) { print STDERR "Done!\n\n"; }
}

sub buildRecursiveForeign() {
  my $originalTablename = shift ;
  my $tablename = shift ;

  foreach my $I (@{$myInheritsConstraints{uc $tablename}}) {
    &buildRecursiveForeign( $originalTablename , $I ) ;
    &buildForeigns( $I , $originalTablename ) ;
  }
}

## build in postorder according to the inheritance order.
sub buildPostOrder {
    my @listOfTables = @_ ;

    foreach my $I ( @listOfTables ) {
	unless ( $myMarkedForBuildTables{uc $I} ) {
	    $myMarkedForBuildTables{uc $I} = 1 ;
	    if( $DEBUG ) {
		print stderr "POSTORDER: Building $I\n" ;
	    }
	    &buildPostOrder( @{$myUCInheritance{uc $I}} ) ;
	    &buildTable( $I ) ;
	}
    }
}

## build sql table
#
sub buildTable {
	
	my $tablename = shift ;
	undef($sql);
	
	if($DEBUG) { print STDERR "Working on '$tablename':\n"; }
	
	if($CREATECOMMENTS) {
		print "#\n# Table structure for table '$tablename'\n#\n\n";
	}
	
	if($CREATEDROPTABLES) {
		if($DEBUG) {
                  print STDERR "-> Creating DROP TABLE statement\n";
                }
		print "$DROPTABLE $tablename;\n";
	}
	
	if($DEBUG) { print STDERR "-> Collect table columns\n"; }

	my $primaryKey = &buildPrimaryKey($tablename) ;

	if( $primaryKey ) {
		push @{$myTableContents{$tablename}} , $primaryKey ;
	}

	my $columns = join(",\n\t",@{$myTableContents{$tablename}});

	if($DEBUG) { print STDERR "-> Create CREATE TABLE statement\n"; }
	my $sql = "CREATE TABLE $tablename (\n\t".$columns.")" ;

	my $inheritance = join( "," , @{$myInheritance{$tablename}}) ;

	if( $inheritance ) {
	    $sql .= " INHERITS( $inheritance )" ;
	}

	$sql .= " ;\n\n";

	print $sql;
	undef($sql);
	
	if(@{$myIndexColumns{$tablename}}) { # add indexed columns
	    foreach $column (@{$myIndexColumns{$tablename}}) {
		if($DEBUG) {
		    print STDERR "-> Adding INDEX for $tablename ($column)\n";
		}
		$sql .= "CREATE INDEX ".$column.
		    "_idx ON $tablename ($column);\n";
	    }
	}
	
	print "$sql\n";
	
}

sub buildRecursivePrimaryKey() {
    my $originalTablename = shift ;
    my $tablename = shift ;
    my $primaryKeys = shift ;

    foreach my $I (@{$myInheritsConstraints{uc $tablename}}) {
      &buildRecursivePrimaryKey( $originalTablename , $I , $primaryKeys ) ;
      if( $DEBUG and @{$myPrimaryKeys{uc $I}} ) {
        print STDERR "PKEY: Found extra keys for $originalTablename: ".
	  join(",",@{$myPrimaryKeys{uc $I}})."\n" ;
      }
    }

    push @{$primaryKeys} , @{$myPrimaryKeys{uc $tablename}} ;
}

sub buildPrimaryKey {
    my $tablename = shift ;

    my @primaryKeys = () ;

    &buildRecursivePrimaryKey( $tablename , $tablename , \@primaryKeys ) ;

    if( @primaryKeys ) {
	if($DEBUG) {
	    print STDERR "PKEY: adding primary key for table $tablename\n";
	}

	$tablename =~ s/\./_/g;
	return "CONSTRAINT pkey_$tablename PRIMARY KEY(".
	    join(",",@primaryKeys).")\n" ;
    }

    return "" ;
}

sub buildForeigns() {

    my $myTablename = shift ;
    my $mySubTablename = shift ;

    unless( $mySubTablename ) { $mySubTablename = $myTablename } ;

    if($DEBUG) { print STDERR "-> Create ALTER TABLE statement\n"; }

    foreach my $colspec (@{$mySimpleForeigns{uc $myTablename}}) {
	( my $column , my $table , my $restrictions ) = @{$colspec} ;

	if( $DEBUG ) {
	    print STDERR "BUILDFOREIGNS2: $myTablename: ";
	    print STDERR "$column," ;
	    print STDERR "$table," ;
	    print STDERR "$restrictions\n" ;
	}

	my $mySubConstraintTablename = $mySubTablename;
	$mySubConstraintTablename =~ s/\./_/g;

	print "ALTER TABLE $mySubTablename ".
	    "ADD CONSTRAINT fkey_".$column."_".$mySubConstraintTablename.
	    " FOREIGN KEY( $column )\n" ;
	print "\tREFERENCES $table\n" ;
	print "\t$restrictions ;\n\n" ;

	if( $DEBUG ) {
	    print STDERROR "BUILDFOREIGNS: Simple foreign found '$column'".
		" => $table $restrictions\n" ;
	}

    }

    foreach my $colspec (@{$myCompositeForeigns{uc $myTablename}}) {
	( my $columns , my $table , my $destcolumns , 
	     my $restrictions ) = @{$$colspec} ;

	my $columnList = join( "," , @{$columns} ) ;
	my $destcolumnList = join( "," , @{$destcolumns} ) ;
	my $mySubConstraintTablename = $mySubTablename;
	$mySubConstraintTablename =~ s/\./_/g;

	print "ALTER TABLE $mySubTablename ".
	    "ADD CONSTRAINT fkey_".${$columns}[0]."_".$mySubConstraintTablename.
	    " FOREIGN KEY( $columnList )\n" ;
	print "\tREFERENCES $table( $destcolumnList )\n" ;
	print "\t$restrictions ;\n\n" ;
    }

    if($DEBUG) { print STDERR "-> Adding FOREIGN KEY definitions\n"; }

}
