module

public import CFSG.Certificates.Kernel.YModel.Y432F.Data
public import CFSG.Certificates.Kernel.Orders.Fi24p.Rels

public section

namespace CFSG.KD.C24053

open CFSG.KC.YModel

@[expose] def imgs : List (List Nat) :=
  [[3, 2], [3, 1], [3, 0], [3, 5], [3, 6], [3, 7], [3, 8], [3, 9], [3, 4],
    3 :: (List.replicate 9 [3, 2, 1, 0, 5, 6, 8]).flatten]

@[expose] def pos (x : Nat) : Nat := if x < 8 then x else x - 1

@[expose] def expL (l : Nat × Bool) : List Nat :=
  if l.2 then imgs.getD (pos l.1) [] else (imgs.getD (pos l.1) []).reverse

@[expose] def word (j : Nat) : List (Nat × Bool) := CFSG.KD.OrdFi24p.rels.getD j []

@[expose] def keep (j : Nat) : Bool := !(word j).any fun l => l.1 == 8

@[expose] def rel (j : Nat) : List Nat := (word j).flatMap expL

@[expose] def invW (w : List (Nat × Bool)) : List (Nat × Bool) := w.reverse.map fun l => (l.1, !l.2)

@[expose] def rot1 (w : List (Nat × Bool)) : List (Nat × Bool) := w.drop 1 ++ w.take 1

@[expose] def pairOK (j : Nat) : Bool :=
  j % 2 == 1 && keep (j - 1) &&
    (decide (word j = invW (word (j - 1))) || decide (word j = rot1 (invW (word (j - 1)))))

@[expose] noncomputable def x1Chk24053_ (j : Nat) : Bool :=
  !keep j || pairOK j || weqK 15 10 CFSG.KD.YMY432F.Nf (rel j) []

end CFSG.KD.C24053

end
