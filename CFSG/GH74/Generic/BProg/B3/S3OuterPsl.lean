module

public import CFSG.GH74.Generic.BProg.B3.S3OuterGraph
public import CFSG.GH74.Generic.BProg.B3.S3OuterGF

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3OuterPsl

open CFSG CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix Subgroup S3OuterCore
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem outerCore_psl3 [Finite F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hp2 : p ≠ 2)
    (hFc : Nat.card F = p ^ f) (hF2 : ringChar F ≠ 2) (h5 : 5 ≤ p ^ f)
    {α : MulAut (projectiveSL 3 F)} (hα2 : α * α = 1)
    (hout : α ∉ OuterAutomorphisms.inner (projectiveSL 3 F)) : OuterCore α := by
  classical
  have hm3 : 3 ≤ 3 := le_refl 3
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have hα2' : α ^ 2 = 1 := by rw [pow_two]; exact hα2
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) hm3
  obtain ⟨B, τ, ε, hε, hαe⟩ := hform α
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hαe
    by_cases hτ : τ = 1
    ·
      subst hτ
      rw [map_one, mul_one] at hαe
      exfalso
      apply hout
      have hsq : conjAut 3 F B * conjAut 3 F B = 1 := by rw [← hαe]; exact hα2
      have h1 : conjAut 3 F (B * B) * fieldAut 3 F 1 = 1 := by
        rw [map_one, mul_one, map_mul]
        exact hsq
      obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl (B * B) 1 h1
      have hscal :
          ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          (u : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
        rw [smul_one_eq_diagonal]
        rfl
      have hAA : (B : Matrix (Fin 3) (Fin 3) F) * B = (u : F) • 1 := by
        rw [← hscal, hu, Units.val_mul]
      rw [hαe]
      exact KGroups.L3Eps.conjAut_mem_inner_of_sq_scalar B u hAA
    ·
      have hα2'' : (conjAut 3 F B * fieldAut 3 F τ) ^ 2 = 1 := by rw [← hαe]; exact hα2'
      obtain ⟨hev, hτf, H, hH⟩ := linear_field_involution_descent hp hf hFc hm3 B τ hτ hα2''
      have hττ : ∀ a, τ (τ a) = a := by
        intro a
        have hfm : p ^ (f / 2) * p ^ (f / 2) = p ^ f := by
          rw [← pow_add]
          congr 1
          obtain ⟨m, hm⟩ := hev
          omega
        have : Fintype F := Fintype.ofFinite F
        rw [hτf, hτf, ← pow_mul, hfm, ← hFc, Nat.card_eq_fintype_card]
        exact FiniteField.pow_card a
      have hτne : ∃ a, τ a ≠ a := by
        by_contra hcon
        push Not at hcon
        exact hτ (RingEquiv.ext hcon)
      exact OuterCore.of_conj (conjAut 3 F H) (by rw [hαe, hH])
        (S3OuterField.outerCore_field h2 hτne hττ)
  · rw [pow_one] at hαe
    by_cases hτ : τ = 1
    ·
      subst hτ
      rw [map_one, mul_one] at hαe
      have hα2'' : (conjAut 3 F B * dualAut 3 F) ^ 2 = 1 := by rw [← hαe]; exact hα2'
      rcases OddSelector.transpose_eq_or_eq_neg_of_pureGraph hm3 B hα2'' with hB | hB
      · rw [hαe]
        exact S3OuterGraph.outerCore_graph hF2 (hFc ▸ h5) B hB
      · exfalso
        have hdet : (B : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
          ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
        have h1 := congrArg Matrix.det hB
        rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at h1
        apply hdet
        have h2' : (2 : F) * (B : Matrix (Fin 3) (Fin 3) F).det = 0 := by
          linear_combination h1
        exact (mul_eq_zero.1 h2').resolve_left h2
    ·
      have hα2'' : (conjAut 3 F B * fieldAut 3 F τ * dualAut 3 F) ^ 2 = 1 := by
        rw [← hαe]; exact hα2'
      obtain ⟨hev, hτf, H, hH⟩ :=
        UnitaryHigher.linear_graph_field_involution_descent hp hf hFc hm3 B τ hτ hα2''
      obtain ⟨m, hm⟩ := hev
      have hf2 : f / 2 = m := by omega
      have hm1 : 1 ≤ m := by
        by_contra hm0
        have : m = 0 := by omega
        omega
      have hud : UnitaryFieldData p m F := ⟨hp, hm1, by rw [hFc, hm]; ring_nf⟩
      have hσ : ∀ a, τ a = hud.bar a := by
        intro a
        rw [hτf, hf2, UnitaryFieldData.bar_apply]
      exact OuterCore.of_conj (conjAut 3 F H) (by rw [hαe, hH])
        (S3OuterGF.outerCore_graphField hud hp2 hσ)

end S3OuterPsl

end CFSG.GH74.Generic.BProg.B3
