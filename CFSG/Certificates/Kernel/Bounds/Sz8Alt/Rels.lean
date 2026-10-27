module

public import Init

public section

namespace CFSG.KC.Sz8Alt

@[expose] noncomputable def rel (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
  (nat_lit 77234247460962462004563492926615201299870897627480871277703268) (Nat.beq k (nat_lit 7)))
  (nat_lit 221292303893225017386869481961529258017485533616102364853616880528658548)
    (Nat.beq k (nat_lit 6)))
  (nat_lit 324042127818333026486480149898520724396365556302423046661577673121760717814756381340754239933400017676275040064968327364)
    (Nat.beq k (nat_lit 5)))
  (nat_lit 123949259937696118411080016125534105824634230933135213421420417091689099635469005132866734351075604077733594804712992932040)
    (Nat.beq k (nat_lit 4)))
  (nat_lit 12019390181820827803555282281388554871430578236817492) (Nat.beq k (nat_lit 3)))
  (nat_lit 38686216532485828992041000) (Nat.beq k (nat_lit 2)))
  (nat_lit 137977929744) (Nat.beq k (nat_lit 1)))
  (nat_lit 8) (Nat.beq k (nat_lit 0))

@[expose] noncomputable def sub (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 2097160) (Nat.beq j (nat_lit 0))

end CFSG.KC.Sz8Alt

end
