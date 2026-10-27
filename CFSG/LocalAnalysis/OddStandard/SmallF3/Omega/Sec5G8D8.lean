module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutOrder8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec5g8_nonempty_dihedral_of_card_eight {D : Type} [Group D] [Finite D]
    (h8 : Nat.card D = 8) {V : Subgroup D} (hV : Nat.card ↥V = 4) (hsq : ∀ v ∈ V, v * v = 1)
    (hnc : ∃ x y : D, x * y ≠ y * x) : Nonempty (D ≃* DihedralGroup 4) := by
  rcases CFSG.OddStandard.SmallF3.HarrisU33.Outside.order8_nonabelian h8 hnc with h | hQ
  · exact h
  · exfalso
    obtain ⟨e⟩ := hQ
    let f : ↥V → {q : QuaternionGroup 2 // q * q = 1} := fun v =>
      ⟨e (v : D), by rw [← map_mul, hsq (v : D) v.2, map_one]⟩
    have hf : Function.Injective f := by
      intro v w hvw
      exact Subtype.ext (e.injective (Subtype.ext_iff.mp hvw))
    have hle := Nat.card_le_card_of_injective f hf
    have hcard : Nat.card {q : QuaternionGroup 2 // q * q = 1} = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [hV, hcard] at hle
    omega

end CFSG.OddStandard.SmallF3.Omega
