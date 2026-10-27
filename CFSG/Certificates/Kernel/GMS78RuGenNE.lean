module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.KC.GMS.Gen

section NE

variable (conjTab : List (List ℕ)) (L : List (Fin 7))

@[expose] def neConjPermG (l : Fin 7) (i : ℕ) : ℕ := (conjTab.getD (L.idxOf l) []).getD i 0

@[expose] def neActPermG (u : List (Fin 7)) : List ℕ :=
  (List.range 64).map fun i => u.foldr (neConjPermG conjTab L) i

@[expose] def neActCheckG (mulTab : List (List ℕ)) (actWords orbitWords : List (List (Fin 7)))
    (wit : List (ℕ × ℕ × ℕ)) : Bool :=
  ((List.range 6).all fun j => (List.range 64).all fun i =>
      decide ((mulTab.getD j []).getD i 0 < 64) &&
        decide ((conjTab.getD j []).getD i 0 < 64)) &&
    ((List.range 6).all fun k => (List.range 64).all fun j =>
      (List.range 64).any fun i => (conjTab.getD k []).getD i 0 == j) &&
    actWords.all (fun u => u.all fun l => l ∈ ([0, 1, 2, 3, 5] : List (Fin 7))) &&
    orbitWords.all (fun u => u.all fun l => l ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 7))) &&
    (actWords.map (neActPermG conjTab L)).Nodup && actWords.length == 192 &&
    orbitWords.length == 20 &&
    ((List.range 20).all fun k => (List.range 20).all fun l =>
      !decide (k < l) || wit.any fun t => t.1 == k && t.2.1 == l)

@[expose] def neW0CheckG (w : List (Fin 7)) : Bool :=
  (List.range 64).all fun i => (neActPermG conjTab L w).getD i 0 != i || i == 0

end NE

end CFSG.KC.GMS.Gen

end
