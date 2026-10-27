module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FGraph2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FGF3

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank

theorem graphWitInput : GraphWitInput := by
  intro n K _ _ h2 hn h3 h4 A hα
  classical
  have : Fintype K := Fintype.ofFinite K
  have hAT : (A : Matrix (Fin n) (Fin n) K)ᵀ = A := by
    rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut hn A hα with h | h
    · exact h
    · rw [h]
      ext i j
      rw [Matrix.neg_apply, neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]
  set R := ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hRdef
  have hAR : (A : Matrix (Fin n) (Fin n) K) * R = 1 := by
    rw [hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRT : Rᵀ = R := by
    calc Rᵀ = Rᵀ * ((A : Matrix (Fin n) (Fin n) K) * R) := by rw [hAR, Matrix.mul_one]
      _ = (Rᵀ * (A : Matrix (Fin n) (Fin n) K)ᵀ) * R := by rw [hAT, Matrix.mul_assoc]
      _ = R := by rw [← transpose_mul, hAR, transpose_one, Matrix.one_mul]
  choose d hd using fun i => FiniteField.isSquare_of_char_two (ringChar_eq_two h2) (R i i)
  have hQ := form_self_eq h2 hRT (d := d) fun i => (hd i).symm
  have hiso : ∀ v : Fin n → K, d ⬝ᵥ v = 0 → (R *ᵥ v) ⬝ᵥ v = 0 := fun v hv => by
    rw [hQ, hv, mul_zero]
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_hyp_pair (by simpa using hn) hAR d
  by_cases hK : 4 ≤ Nat.card K
  ·
    obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, 1} : Finset K)) (t := Finset.univ) (by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact lt_of_le_of_lt Finset.card_le_two (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    exact hasWit_graph_torus h2 hRdef.symm hRT (hiso x hx) (hiso y hy) hxy hl.1 hl.2
  · have hn5 : 5 ≤ n := by
      rcases Nat.lt_or_ge n 5 with h5 | h5
      · interval_cases n
        · exact absurd ((h3 rfl).trans' (by norm_num)) hK
        · exact absurd (h4 rfl) hK
      · exact h5
    obtain ⟨x₂, y₂, hx₂, hy₂, hxy₂, hx₁x₂, hy₁x₂, hx₁y₂, hy₁y₂⟩ :=
      exists_hyp_pair_perp (by simpa using hn5) hRT hAR hx hy (hiso x hx) (hiso y hy) hxy
    exact hasWit_graph_double h2 hRdef.symm hRT (hiso x hx) (hiso x₂ hx₂) (hiso y hy)
      (hiso y₂ hy₂) hxy hxy₂ hx₁x₂ hx₁y₂ hy₁x₂ hy₁y₂

theorem twoNilpFor_psl
    (hA : TwoNilpFor fun Y _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (Y ≃* alternatingGroup (Fin n))) :
    TwoNilpFor fun Y _ => ∃ n f : ℕ, StatedClassicalModel Y .PSL n 2 f :=
  twoNilpFor_psl_of_inputs hA graphWitInput graphField3WitInput

end CFSG.ComponentClassification.HarrisLit.L33.C2
