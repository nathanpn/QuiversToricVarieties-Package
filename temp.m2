pullbackCones = (nn,L) -> (
 X := smoothFanoToricVariety(nn,L#0);
--the 'maximal' variety
 LLength := #L;
 oldL := L;
 pbDetails := new MutableHashTable;
 while #L > 1 do (
   tDiv := tDivisorMap(nn,L);
   excDivs := select(numgens tDiv.source, i -> (
	 tDiv_i == vector(toList(numgens tDiv.target :0))));
   perm := select(
      (0,0)..(numgens tDiv.target -1, numgens tDiv.source -1), i -> 
      tDiv_i == 1);
--permutation of the divisors
   Perm := hashTable(toList perm); 
   Y := smoothFanoToricVariety(nn, last L);
   A1:= forbiddenSets Y;
--the forbidden sets for Y using the enumeration for Y
   forbiddens0 := apply(
       flatten values A1, i -> sort apply(i, j -> Perm#j));
--the forbidden sets for Y using the enumeration for X
   forbiddens := forbiddens0;
   scan(forbiddens0, i -> (if (any(keys pbDetails, j -> (
		   rmExc := sort toList(set i - pbDetails#j#0);
		   any(pbDetails#j#1, k -> (
			   k == rmExc))))) then
       forbiddens = delete(i,forbiddens)));
--removes forbidden sets covered by those from previous varieties
   pbDetails#(LLength - #L) = (excDivs, forbiddens);
   L = delete(last L, L);
	    );
 gamma0 := flatten values forbiddenSets X;
 gamma := gamma0;
 apply(gamma0, i -> (if (any(keys pbDetails, j -> (
		   rmExc := sort toList(set i - pbDetails#j#0);
		   any(pbDetails#j#1, k -> (
			   k == rmExc))))) then
       gamma = delete(i,gamma)));
--removes forbidden sets covered by those from previous varieties
pbDetails#(LLength-1) = ({},gamma);
--the unaffected nonvanishing cones for X 
 d := #rays X;
 A := fromWDivToCl X;      
--to calculate the nonvanishing cones in the Picard lattice  
 cones := new MutableHashTable;
     	scan(keys pbDetails, i -> cones#(oldL#(LLength-1-i)) = apply(
	  pbDetails#i#1, s -> (
	    translation := - sum(s, j -> A_{j});
	    M0 := matrix table(d, d, (p,q) -> if member(
		    p,pbDetails#i#0) then 0
	      else if p == q then 
	         (if member(p,s) then -1 else 1) else 0);
	    M := transpose matrix({toList (d:0)});
	    apply(d, i -> if M0_i == vector(toList(d:0)) then
		M = M|((id_(ZZ^d))_{i})|(-((id_(ZZ^d))_{i}))
		else
		M = M|(M0_{i}));
	  outerNorm := (fourierMotzkin (A*M))#0;
    {translation, outerNorm})));
  X.cache.preImageCones = new HashTable from pairs cones;
  X.cache.preImageCones)

--WILL NEED TO CHANGE OTHER CODE TO USE PREIMAGECONES - in particular, use KEYS
--instead of 1..d as hash table X.cahce.preimageCones will be size of LIST L
CHECK M IS CREATED PROPERLY