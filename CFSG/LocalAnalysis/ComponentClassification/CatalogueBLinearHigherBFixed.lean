module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBPureGraph
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphField
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBLinearHigherB

open Matrix CFSG.LocalAnalysis.ComponentInitial

universe u

theorem exists_odd_prime_pow_card (K : Type u) [Field K] [Finite K] (hodd : ringChar K ≠ 2) :
    ∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ Nat.card K = p ^ f := by
  let := Fintype.ofFinite K
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  exact ⟨ringChar K, f, hp, hp.odd_of_ne_two hodd, f.pos,
    by rw [Nat.card_eq_fintype_card, hcard]⟩

theorem odd_higher_linear_involution_fixed_p_components (n : ℕ) (K : Type u) [Field K]
    [Finite K] (hodd : ringChar K ≠ 2) (hn : 3 ≤ n)
    (α : MulAut (LinearFlag.projectiveSL n K)) (hne : α ≠ 1) (hsq : α ^ 2 = 1) :
    ∀ r : ℕ, r.Prime → ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup α),
      CFSG.IsPComponent r L → CFSG.IsQuasisimple L := by
  intro r hr
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen α
  interval_cases ε
  ·
    have h : MulAut.congr (nativeEquiv n K)
        (LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ * LinearFlag.dualAut n K ^ 0) =
        CatalogueBLinearSemilinear.semilinearAction n K A σ := by
      rw [pow_zero, mul_one, congr_semilinear]
    obtain ⟨hne', hsq'⟩ := congr_involution (nativeEquiv n K) hne hsq
    rw [h] at hne' hsq'
    exact fixed_pComponent_quasisimple_of_congr (nativeEquiv n K) h r
      (CatalogueBLinearSemilinear.odd_linear_semilinear_involution_fixed_p_components n K
        (by omega) (odd_card_of_ringChar_ne_two K hodd) (Or.inl hn) A σ hne' hsq' r hr)
  · by_cases hσ : σ = 1
    ·
      subst hσ
      have h : LinearFlag.conjAut n K A * LinearFlag.fieldAut n K 1 * LinearFlag.dualAut n K ^ 1 =
          LinearFlag.conjAut n K A * LinearFlag.dualAut n K := by
        rw [pow_one, map_one, mul_one]
      rw [h] at hne hsq
      exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv r
        (MulEquiv.subgroupCongr (congrArg FixedCommutingProduct.fixedSubgroup h))
        (odd_linear_pure_graph_involution_fixed_p_components n K hodd hn A hne hsq r hr)
    ·
      have h : MulAut.congr (nativeEquiv n K)
          (LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ * LinearFlag.dualAut n K ^ 1) =
          CatalogueBGraphField.graphFieldAction n K A σ := by
        rw [pow_one, congr_graphField]
      obtain ⟨hne', hsq'⟩ := congr_involution (nativeEquiv n K) hne hsq
      rw [h] at hne' hsq'
      obtain ⟨p, f, hp, hpodd, hf, hcard⟩ := exists_odd_prime_pow_card K hodd
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨-, -, hunitary, -, -, -, hfixed⟩ :=
        CatalogueBGraphField.odd_linear_graph_field_involution_fixed_p_components_native n K p f
          hpodd hf hcard hn A σ hσ hne' hsq'
      exact fixed_pComponent_quasisimple_of_congr (nativeEquiv n K) h r
        fun L hL => (hfixed r hr L hL).1

end CFSG.ComponentClassification.CatalogueBLinearHigherB
