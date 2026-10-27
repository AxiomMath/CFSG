module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInner

public section

namespace CFSG.ComponentClassification.CatalogueBLinearSemilinear

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearField

universe u

theorem congr_eq_conjugation {G : Type*} [Group G] (e f : MulAut G) :
    MulAut.congr e f = e * f * e⁻¹ := by
  apply MulEquiv.ext
  intro x
  rfl

@[expose] def fieldConjugateFixedEquiv
    (n : ℕ) (K : Type u) [Field K]
    (A H : GL (Fin n) K) (sigma : K ≃+* K)
    (hconjugacy : semilinearAction n K A sigma =
      innerDiagonalAction n K H * pslFieldAut (Fin n) K sigma *
        (innerDiagonalAction n K H)⁻¹) :
    fixedPSL n K sigma ≃*
      FixedCommutingProduct.fixedSubgroup (semilinearAction n K A sigma) :=
  (CatalogueRelativeB.fixedSubgroupEquivalence (innerDiagonalAction n K H)
    (pslFieldAut (Fin n) K sigma)).trans
      (MulEquiv.subgroupCongr (congrArg FixedCommutingProduct.fixedSubgroup
        ((congr_eq_conjugation _ _).trans hconjugacy.symm)))

theorem semilinear_involution_fixed_pComponent_quasisimple
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hodd : Odd (Nat.card K))
    (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : GL (Fin n) K) (sigma : K ≃+* K)
    (hne : semilinearAction n K A sigma ≠ 1)
    (hsquare : semilinearAction n K A sigma ^ 2 = 1)
    (p : ℕ) (hp : p.Prime)
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup (semilinearAction n K A sigma)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hsigma : sigma = 1
  · subst sigma
    rw [semilinearAction_one_field] at hne hsquare
    exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
      (MulEquiv.subgroupCongr (congrArg FixedCommutingProduct.fixedSubgroup
        (semilinearAction_one_field n K A)))
      (CatalogueBHigherLinearInner.innerDiagonal_involution_fixed_pComponent_quasisimple
        n K hn hodd hparameter A hne hsquare p hp) L hL
  · have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero
      (CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd)
    obtain ⟨_, H, hconjugacy⟩ := field_involution_conjugacy n K hn (by omega) htwo
      A sigma hsigma hsquare
    let : NeZero n := ⟨by omega⟩
    exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
      (fieldConjugateFixedEquiv n K A H sigma hconjugacy).symm
      (field_fixed_pComponent_quasisimple n K (by omega) sigma p) L hL

theorem odd_linear_semilinear_involution_fixed_p_components
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hodd : Odd (Nat.card K))
    (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : GL (Fin n) K) (sigma : K ≃+* K)
    (hne : semilinearAction n K A sigma ≠ 1)
    (hsquare : semilinearAction n K A sigma ^ 2 = 1) :
    ∀ p : ℕ, p.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (semilinearAction n K A sigma)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L :=
  semilinear_involution_fixed_pComponent_quasisimple n K hn hodd hparameter A sigma hne hsquare

end

end CFSG.ComponentClassification.CatalogueBLinearSemilinear
