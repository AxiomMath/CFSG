module

public import CFSG.GH74.Generic.BProg.B3.S45EvenN3Core
public import CFSG.GH74.Generic.BProg.B3.S45TableA

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG.GH74.Generic.BProg.B3.S45TableA

theorem N3_alt {X : Type} [Group X] [Finite X] (hXp : Group.IsPerfect X)
    (hZ2 : IsPGroup 2 ↥(Subgroup.center X)) (hZ : Subgroup.center X ≠ ⊥)
    (hZc : Nat.card ↥(Subgroup.center X) ≤ 2) {n : ℕ} (hn8 : 8 ≤ n)
    (hn11 : n ≤ 11) (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n)) {y : MulAut X}
    (hy : orderOf y = 2) (hd : Datum X y)
    (hab : ∀ T : Subgroup X, IsPGroup 2 ↥T → (∀ t ∈ T, y t = t) → ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    False := by
  have _ := hZc
  have _ := hn11
  have _ := hd
  exact S45EvenN3Core.n3_alt_core hXp hZ2 hZ hn8 e hy hab

end CFSG.GH74.Generic.BProg.B3
