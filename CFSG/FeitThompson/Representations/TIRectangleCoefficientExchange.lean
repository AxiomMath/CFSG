module

public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues
public import CFSG.FeitThompson.Representations.ProductCharactersFullBasis
import CFSG.FeitThompson.Representations.RectangleDifferencesBasisSupportedFunctions

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

variable {G : Type*} [Group G] {W W1 W2 : Subgroup G}

namespace IsCyclicTIPair

noncomputable def prodCharEta (hW : IsCyclicTIPair W W1 W2)
    (σ : classFun ↥W →ₗ[ℂ] classFun G) (i : Irr ↥W1) (j : Irr ↥W2) : G → ℂ :=
  (σ (hW.basisProdIrr (i, j)) : G → ℂ)

variable {σ : classFun ↥W →ₗ[ℂ] classFun G}

theorem prodCharEta_eq_coe_apply (hW : IsCyclicTIPair W W1 W2) (i : Irr ↥W1) (j : Irr ↥W2) :
    hW.prodCharEta σ i j = (σ (hW.basisProdIrr (i, j)) : G → ℂ) := (rfl)

theorem prodCharEta_mem_classFun (hW : IsCyclicTIPair W W1 W2) (i : Irr ↥W1) (j : Irr ↥W2) :
    hW.prodCharEta σ i j ∈ classFun G := (σ (hW.basisProdIrr (i, j))).2

theorem prodCharEta_mem_virtualChars [Fintype G] [Fintype ↥W] (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (i : Irr ↥W1) (j : Irr ↥W2) :
    hW.prodCharEta σ i j ∈ virtualChars G := by
  refine hσ.map_virtualChars _ ?_
  rw [coe_basisProdIrr_apply]
  exact Irr_subset_virtualChars (hW.prodChar_mem_Irr i.2 j.2)

theorem basisProdIrr_principal (hW : IsCyclicTIPair W W1 W2) :
    hW.basisProdIrr (principalIrr ↥W1, principalIrr ↥W2) = principalClassFun ↥W := by
  refine Subtype.ext ?_
  rw [coe_basisProdIrr_apply, coe_principalClassFun, coe_principalIrr, coe_principalIrr,
    hW.prodChar_one_one]

theorem prodCharEta_principal [Fintype G] [Fintype ↥W] (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) :
    hW.prodCharEta σ (principalIrr ↥W1) (principalIrr ↥W2) = 1 := by
  rw [prodCharEta, hW.basisProdIrr_principal, hσ.map_principalClassFun, coe_principalClassFun]

open scoped Classical in
theorem cfInner_prodCharEta [Fintype G] [Fintype ↥W] (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (i i' : Irr ↥W1) (j j' : Irr ↥W2) :
    cfInner (hW.prodCharEta σ i j) (hW.prodCharEta σ i' j') =
      if i = i' ∧ j = j' then 1 else 0 := by
  rw [prodCharEta, prodCharEta, hσ.inner_eq, coe_basisProdIrr_apply, coe_basisProdIrr_apply,
    hW.cfInner_prodChar_eq_ite_and]
  simp

theorem cfInner_prodCharEta_exchange [Fintype G] [Fintype ↥W] (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {f : G → ℂ} (hf : f ∈ classFun G)
    (hf0 : ∀ x ∈ cyclicTIDiff W W1 W2, f x = 0) (i : Irr ↥W1) (j : Irr ↥W2) :
    cfInner f (hW.prodCharEta σ i j) +
        cfInner f (hW.prodCharEta σ (principalIrr ↥W1) (principalIrr ↥W2)) =
      cfInner f (hW.prodCharEta σ i (principalIrr ↥W2)) +
        cfInner f (hW.prodCharEta σ (principalIrr ↥W1) j) := by
  set A : classFun ↥W := hW.basisProdIrr (principalIrr ↥W1, principalIrr ↥W2)
      - hW.basisProdIrr (i, principalIrr ↥W2) - hW.basisProdIrr (principalIrr ↥W1, j)
      + hW.basisProdIrr (i, j) with hA
  have hAcoe : (A : ↥W → ℂ) = hW.prodCharAlpha (i : ↥W1 → ℂ) (j : ↥W2 → ℂ) := by
    simp only [hA, AddSubgroupClass.coe_sub, AddMemClass.coe_add, coe_basisProdIrr_apply,
      coe_principalIrr, hW.prodChar_one_one, prodCharAlpha_eq]
  have hA0 : ∀ x : ↥W, (x : G) ∉ cyclicTIDiff W W1 W2 → (A : ↥W → ℂ) x = 0 := by
    rw [hAcoe]
    exact (mem_dadeDomain.1 (hW.prodCharAlpha_mem_dadeDomain i.2 j.2)).2
  have hzero : cfInner (A : ↥W → ℂ) (resClassFun W f) = 0 := by
    have hterm : ∀ x : ↥W, (A : ↥W → ℂ) x * conj (resClassFun W f x) = 0 := by
      intro x
      by_cases hx : (x : G) ∈ cyclicTIDiff W W1 W2
      · rw [resClassFun_apply, hf0 _ hx, map_zero, mul_zero]
      · rw [hA0 x hx, zero_mul]
    rw [cfInner_def, Finset.sum_eq_zero fun x _ => hterm x, mul_zero]
  have h1 : cfInner f (σ A : G → ℂ) = 0 := by
    rw [hσ.eq_indClassFun A hA0, ← conj_cfInner, cfInner_indClassFun W _ hf, hzero, map_zero]
  have hexp : (σ A : G → ℂ) =
      hW.prodCharEta σ (principalIrr ↥W1) (principalIrr ↥W2) -
        hW.prodCharEta σ i (principalIrr ↥W2) - hW.prodCharEta σ (principalIrr ↥W1) j +
        hW.prodCharEta σ i j := by
    simp [hA, prodCharEta]
  rw [hexp, cfInner_add_right, cfInner_sub_right, cfInner_sub_right] at h1
  linear_combination h1

end IsCyclicTIPair

end CFSG.FeitThompson

end
