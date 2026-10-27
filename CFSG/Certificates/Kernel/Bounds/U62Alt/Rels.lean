module

public import Init

public section

namespace CFSG.KC.U62Alt

@[expose] noncomputable def rel (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
  (nat_lit 77836853849085169002744971319464155897418756241399035270819940) (Nat.beq k (nat_lit 19)))
  (nat_lit 5061623942902543224069698869077466963351079784146301105688853631084) (Nat.beq k (nat_lit 18)))
  (nat_lit 7397571239751341009524292469682574185200990222524006483045053878526538300973555518367135308580977153866687933591740)
    (Nat.beq k (nat_lit 17)))
  (nat_lit 19277132236245804053417268677825745333543113965099667758881058841845759775799971740386151180872846338692999024828)
    (Nat.beq k (nat_lit 16)))
  (nat_lit 3802990940543551056606230765616) (Nat.beq k (nat_lit 15)))
  (nat_lit 301697805700382119533515414736133587214809680550569862783072) (Nat.beq k (nat_lit 14)))
  (nat_lit 46860112663848798561497103467153121899484909953104) (Nat.beq k (nat_lit 13)))
  (nat_lit 10931655088918177617904494562199666188352) (Nat.beq k (nat_lit 12)))
  (nat_lit 3817826575682180956646667214896) (Nat.beq k (nat_lit 11)))
  (nat_lit 591462348352753000480) (Nat.beq k (nat_lit 10)))
  (nat_lit 70330114064) (Nat.beq k (nat_lit 9)))
  (nat_lit 6316040) (Nat.beq k (nat_lit 8)))
  (nat_lit 207502721040) (Nat.beq k (nat_lit 7)))
  (nat_lit 70061670416) (Nat.beq k (nat_lit 6)))
  (nat_lit 1077952524) (Nat.beq k (nat_lit 5)))
  (nat_lit 16355070817440708117330634953367354343488) (Nat.beq k (nat_lit 4)))
  (nat_lit 3807942247354663038171645739056) (Nat.beq k (nat_lit 3)))
  (nat_lit 713634735554877445372974969816450089707634760) (Nat.beq k (nat_lit 2)))
  (nat_lit 35322350018580) (Nat.beq k (nat_lit 1)))
  (nat_lit 8) (Nat.beq k (nat_lit 0))

@[expose] noncomputable def sub (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 2113544) (Nat.beq j (nat_lit 0))

end CFSG.KC.U62Alt

end
