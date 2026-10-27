module

public import CFSG.GH74.Generic.BProg.B3.L2CompL3b
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint Subgroup CFSG.GH74.Generic.S45
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification
open scoped MatrixGroups Matrix

namespace L2CompL3

open L2CompL3b

theorem psl_three_fixed_D8 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel S .PSL 3 r f) {ya : MulAut S} (hsq : ya * ya = 1)
    (hne : ya ≠ 1) :
    ∃ a b : S, ya a = a ∧ ya b = b ∧ a ^ 4 = 1 ∧ a ^ 2 ≠ 1 ∧ b * b = 1 ∧ b * a * b⁻¹ = a⁻¹ := by
  classical
  obtain ⟨F, _, _, hF, hr, hf, hk2, ψ, ρ, hinj, hψ⟩ :=
    exists_projective_rep hS hnab hr2 (le_refl 3) hmodel
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hk2
  have ha : orderOf ya = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
  have hm3 : 3 ≤ 3 := le_refl 3
  have hρ1 : ρ ya ≠ 1 := fun h => hne (hinj (by rw [h, map_one]))
  have hρ2 : (ρ ya) ^ 2 = 1 := by rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have key : ∀ p q : LinearFlag.projectiveSL 3 F, ρ ya p = p → ρ ya q = q → IsD8 p q →
      ∃ a b : S, ya a = a ∧ ya b = b ∧ a ^ 4 = 1 ∧ a ^ 2 ≠ 1 ∧ b * b = 1 ∧
        b * a * b⁻¹ = a⁻¹ := by
    intro p q hp hq hD
    obtain ⟨h4, h2, hb2, hba⟩ := hD.map ψ.symm
    refine ⟨ψ.symm p, ψ.symm q, ?_, ?_, h4, h2, hb2, hba⟩
    · apply ψ.injective
      rw [hψ, MulEquiv.apply_symm_apply, hp]
    · apply ψ.injective
      rw [hψ, MulEquiv.apply_symm_apply, hq]
  obtain ⟨-, hform⟩ := LinearFlag.automorphism_generation (K := F) hm3
  obtain ⟨B, τ, ε, hε, hρa⟩ := hform (ρ ya)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hτ : τ = 1
    ·
      subst hτ
      rw [map_one, mul_one] at hρa
      obtain ⟨p, q, hp, hq, hD⟩ := psl_three_fixed_inner_D8 hk2 (B := B)
        (by rw [← hρa]; exact hρ2) (by rw [← hρa]; exact hρ1)
      exact key p q (by rw [hρa]; exact hp) (by rw [hρa]; exact hq) hD
    ·
      have hα2 : (LinearFlag.conjAut 3 F B * LinearFlag.fieldAut 3 F τ) ^ 2 = 1 := by
        rw [← hρa]; exact hρ2
      obtain ⟨-, -, H, hH⟩ := LinearFlag.linear_field_involution_descent hr hf hF hm3 B τ hτ hα2
      refine key (LinearFlag.conjAut 3 F H (LinearFlag.proj 3 F (g0SL F)))
        (LinearFlag.conjAut 3 F H (LinearFlag.proj 3 F (b0SL F))) ?_ ?_
        ((isD8_proj_g0_b0 htwo).map (LinearFlag.conjAut 3 F H))
      · rw [hρa, hH]
        simp only [MulAut.mul_apply, MulAut.inv_apply_self, LinearFlag.fieldAut_proj, map_g0SL]
      · rw [hρa, hH]
        simp only [MulAut.mul_apply, MulAut.inv_apply_self, LinearFlag.fieldAut_proj, map_b0SL]
  · rw [pow_one] at hρa
    by_cases hτ : τ = 1
    ·
      subst hτ
      rw [map_one, mul_one] at hρa
      have hα2 : (LinearFlag.conjAut 3 F B * LinearFlag.dualAut 3 F) ^ 2 = 1 := by
        rw [← hρa]; exact hρ2
      rcases OddSelector.transpose_eq_or_eq_neg_of_pureGraph hm3 B hα2 with hB | hB
      · obtain ⟨p, q, hp, hq, hD⟩ := exists_symmetric_graph_D8_proj hk2 B hB
        exact key p q (by rw [hρa]; exact hp) (by rw [hρa]; exact hq) hD
      · exfalso
        have hdet : (B : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
          ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
        have h1 := congrArg Matrix.det hB
        rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at h1
        apply hdet
        have h2' : (2 : F) * (B : Matrix (Fin 3) (Fin 3) F).det = 0 := by
          linear_combination h1
        exact (mul_eq_zero.1 h2').resolve_left htwo
    ·
      have hα2 : (LinearFlag.conjAut 3 F B * LinearFlag.fieldAut 3 F τ *
          LinearFlag.dualAut 3 F) ^ 2 = 1 := by
        rw [← hρa]; exact hρ2
      obtain ⟨-, -, H, hH⟩ :=
        UnitaryHigher.linear_graph_field_involution_descent hr hf hF hm3 B τ hτ hα2
      refine key (LinearFlag.conjAut 3 F H (LinearFlag.proj 3 F (g0SL F)))
        (LinearFlag.conjAut 3 F H (LinearFlag.proj 3 F (b0SL F))) ?_ ?_
        ((isD8_proj_g0_b0 htwo).map (LinearFlag.conjAut 3 F H))
      · rw [hρa, hH]
        simp only [MulAut.mul_apply, MulAut.inv_apply_self, LinearFlag.dualAut_proj,
          graphAut_g0SL, LinearFlag.fieldAut_proj, map_g0SL]
      · rw [hρa, hH]
        simp only [MulAut.mul_apply, MulAut.inv_apply_self, LinearFlag.dualAut_proj,
          graphAut_b0SL, LinearFlag.fieldAut_proj, map_b0SL]

end L2CompL3

end CFSG.GH74.Generic.BProg.B3
