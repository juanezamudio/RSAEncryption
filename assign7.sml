(*
 *
 * Juan Zamudio
 * April 4, 2016
 * Assignment 07
 *
 *)

(*Problem 1
 *
 *powermod computes b^e mod m
 *
 *)
fun powermod  b (CS52Int 0) m = one
  | powermod  b e           m = if ((less one e) andalso (isOdd e = false))
				then
				    rem (square (powermod b (quo e two) m)) m
				else
				    rem
				    (prod b (square
						 (powermod b (quo e two) m))) m;
(*Problem 2
 *
 *block and unblock convert between CS52ints and their base-n representations
 *block converts to a base-n representation list of the second CS52int
 *unblock converts from a base-n representation list to a CS52int
 *
 *)
fun block n (CS52Int 0) = []
  | block n m           = (rem m n)::(block n (quo m n));

fun unblock n []      = zero
  | unblock n (m::ms) = sum m (prod n (unblock n ms));

(*Problem 3
 *
 *using the ascii representation of characters, stringToCS52Int converts from
 *a string to a CS52int. cs52IntToString takes a CS52int and converts it into
 *a string according to the ascii representation of characters
 *
 *)
fun stringToCS52Int ""  = zero
  | stringToCS52Int a   =
    let
	val ascii = CS52Int 256
	val (x::xs) = map fromInt (map ord (explode a))
    in
	unblock ascii (x::xs)
    end;

fun cs52IntToString (CS52Int 0) = ""
  | cs52IntToString n           =
    let
	val ascii = CS52Int 256
	val (x::xs) = map chr (map toInt (block ascii n))
    in
	implode (x::xs)
    end;

(*Problem 4
 *
 *rsaEncode takes a public key and a cs52int less than n and returns the
 *encrypted integer. The result is an cs52int less than n
 *
 *)
exception BadValue;

fun rsaEncode (e,n) m = if (greater n m)
			then
			    powermod m e n
			else
			    raise BadValue;

(*Problem 5
 *
 *encryptString takes a public key and a message of type string and encrypts
 *the message
 *decryptString takes a private key and a cs52int that represents an
 *encrypted string and decrypts the string
 *
 *) 
fun encryptString (e,n) m = unblock n (map (rsaEncode (e,n))
					   (block n (stringToCS52Int m)));

fun decryptString (d,n) c = cs52IntToString
				(unblock n (map (rsaEncode (d,n)) (block n c)));

(*Problem 6
 *
 *a value enc is declared and contains an encrypted message
 *this value is then inputed into a new val dec that decrypts enc
 *we can then see that enc is decrypted correctly because we get the string
 *back in val dec
 *
 *)
val enc = encryptString (CS52Int 7, CS52Int 111) "Don't panic and always carry your towel";
val dec = decryptString (CS52Int 31, CS52Int 111) enc;

(*Problem 7
 *
 *industrialStrengthPrime takes an integer k and produces a k-bit industrial
 *strength prime number. The k-bit means that the number uses at most k-bits
 *
 *)
val seed = (45, 44);
val generator = Random.rand seed;

local 
    fun checkLess k p =
      let
	  val a = randomCs52Int k generator
      in
	  if (less a p)
	  then
	      a
	  else
	      checkLess k p
      end
	  
in

fun industrialStrengthPrime k =
  let
      val testp = randomCs52Int k generator
				
      fun checkMod a p 0 = p
	| checkMod a p i = if ((compare (powermod a p p) a) = EQUAL
			       andalso greater p one)
			   then
			       checkMod (checkLess k p) p (i-1)
			   else
			       industrialStrengthPrime k;
  in
      checkMod (checkLess k testp) testp 20
  end;
end;

(*Problem 8
 *
 *newRSAKeys take an integer k and produces two RSA keys based on two
 *k-bit primes
 *
 *)
fun newRSAKeys k =
  let
      val p = industrialStrengthPrime k;
      val q = industrialStrengthPrime k;
      val n = prod p q;
      val phi = prod (diff p one) (diff q one);
      val d = randomCs52Int k generator;
      val e = getOpt (inversemod d phi, zero);
  in
      if ((compare e zero) = EQUAL)
      then
	  newRSAKeys k
      else
	  if (less d n)
	  then
	      ((e,n),(d,n))
	  else
	      newRSAKeys k
  end;

(*Problem 10a
 *
 *bruteForceCracker takes as input a public RSA key and returns the
 *corresponding private key
 *
 *)
fun bruteForceCracker (e,n) =
  let
      fun findp n p = if ((compare (rem n p) zero) = EQUAL)
		      then
			  p
		      else
			  findp n (sum p one);
      
      val q =  quo n (findp n two);
      val phi = prod (diff (findp n two) one) (diff q one);
      val d = getOpt (inversemod e phi, zero);
  in
      if ((compare d zero) = EQUAL)
      then
	  bruteForceCracker (e,n)
      else
	  (d,n)
  end;

(*Problem 10b
 *
 *The private key is (701, 52753), if the public key is (22821, 52753)
 *
 *)

(*Problem 10c
 *
 *Since we only have to count up to 2^(k/2) to find p, 
 *the time it takes to crack a 16-bit code is 2^(16/2) or 2^8. The time
 *it takes to crack a 160-bit code is 2^(160/2) or 2^80. If we let x be the
 *time it takes to crack a 16-bit code (2^8), then in terms of x, the time
 *it takes to crack a 160-bit code is x^10
 *
 *)

