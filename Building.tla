------------------------------ MODULE Building ------------------------------
CONSTANT
  PERSON,
  BUILDING
  
  OUTSIDE == CHOOSE x : x \notin PERSON \union BUILDING
  
VARIABLE
  register,
  permission,
  location
  
TypeOk ==
  /\ register \subseteq PERSON
  /\ permission \in [register -> SUBSET BUILDING]
  /\ location \in [register -> (BUILDING \union {OUTSIDE})]
                         
----

Init ==
  /\ register = {}
  /\ permission = << >>
  /\ location = << >>
    
Register(p) ==
  /\ p \in PERSON \ register
  /\ register' = register \union {p}
  /\ permission' = [x \in DOMAIN permission \union {p} |->
                    IF x \in DOMAIN permission THEN permission[x] ELSE {}]
  /\ location' = [x \in DOMAIN location \union {p} |-> 
                  IF x \in DOMAIN location THEN location[x] ELSE OUTSIDE]
  
Enter(p, b) ==
  /\ p \in register
  /\ b \in permission[p]
  /\ location' = [location EXCEPT ![p] = b]
  /\ UNCHANGED <<register, permission>>
  
Leave(p, b) ==
  /\ p \in register
  /\ location[p] = b
  /\ location' = [location EXCEPT ![p] = OUTSIDE]
  /\ UNCHANGED <<register, permission>>
  
----

Next == \E p \in PERSON, b \in BUILDING : 
          \/ Register(p) 
          \/ Enter(p, b)
          \/ Leave(p, b)

=============================================================================
\* Modification History
\* Last modified Fri Oct 12 09:39:31 BST 2018 by cgdk2
\* Created Mon Jun 04 15:17:18 BST 2018 by cgdk2
