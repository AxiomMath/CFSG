module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerParameters
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionComponents

public section

namespace CFSG.ComponentClassification.CatalogueBHigherLinearInner

noncomputable section

open CatalogueBHigherLinearAction

universe u

theorem innerDiagonal_involution_fixed_pComponent_quasisimple
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hodd : Odd (Nat.card K))
    (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hne : innerDiagonalAction n K A ≠ 1)
    (hsq : innerDiagonalAction n K A ^ 2 = 1)
    (p : ℕ) (hp : p.Prime)
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup (innerDiagonalAction n K A)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨ha, ha2, _⟩ := inner_involution_projective_data n K hn hparameter A hne hsq
  let a := Matrix.ProjGenLinGroup.mk A
  let e := fixedPSLCentralizerEquiv n K a
  let M := L.map e.toMonoidHom
  have hcomponent := pComponent_fixed_extend n K a p L hL
  have hquasi := CatalogueBProjectiveInvolution.projective_involution_centralizer_pComponent_quasisimple
    n hn A (Ring.two_ne_zero (ringChar_ne_two_of_odd_card K hodd)) ha ha2 p hp
    (M.map (localPSLRange n K a).subtype) hcomponent
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv
      ((L.equivMapOfInjective e.toMonoidHom e.injective).trans
        (M.equivMapOfInjective (localPSLRange n K a).subtype
          (localPSLRange n K a).subtype_injective))
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

theorem odd_linear_inner_diagonal_involution_fixed_p_components
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hodd : Odd (Nat.card K))
    (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hne : innerDiagonalAction n K A ≠ 1)
    (hsq : innerDiagonalAction n K A ^ 2 = 1) :
    ∀ (p : ℕ), p.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (innerDiagonalAction n K A)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L :=
  innerDiagonal_involution_fixed_pComponent_quasisimple n K hn hodd hparameter A hne hsq

@[expose] def scalarInnerDiagonalAction (n : ℕ) (K : Type u) [Field K] :
    Matrix.GeneralLinearGroup (Fin n) K →* MulAut (ScalarProjectiveSpecialLinear n K) :=
  (MulAut.congr (scalarProjectiveSpecialLinearEquiv n K).symm).toMonoidHom.comp
    (innerDiagonalAction n K)

theorem scalarInnerDiagonalAction_mk (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    scalarInnerDiagonalAction n K A ((QuotientGroup.mk' (slScalarCenter n K)) g) =
      (QuotientGroup.mk' (slScalarCenter n K)) (slConjugation n K A g) := by
  apply (scalarProjectiveSpecialLinearEquiv n K).injective
  change scalarProjectiveSpecialLinearEquiv n K
      ((scalarProjectiveSpecialLinearEquiv n K).symm
        (innerDiagonalAction n K A (scalarProjectiveSpecialLinearEquiv n K
          ((QuotientGroup.mk' (slScalarCenter n K)) g)))) = _
  rw [MulEquiv.apply_symm_apply, scalarProjectiveSpecialLinearEquiv_mk,
    scalarProjectiveSpecialLinearEquiv_mk, innerDiagonalAction_mk]

theorem scalarInnerDiagonalAction_congr (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    MulAut.congr (scalarProjectiveSpecialLinearEquiv n K) (scalarInnerDiagonalAction n K A) =
      innerDiagonalAction n K A := by
  apply MulEquiv.ext
  intro x
  change scalarProjectiveSpecialLinearEquiv n K
      ((scalarProjectiveSpecialLinearEquiv n K).symm
        (innerDiagonalAction n K A (scalarProjectiveSpecialLinearEquiv n K
          ((scalarProjectiveSpecialLinearEquiv n K).symm x)))) =
    innerDiagonalAction n K A x
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

@[expose] def scalarInnerFixedEquiv (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    FixedCommutingProduct.fixedSubgroup (scalarInnerDiagonalAction n K A) ≃*
      FixedCommutingProduct.fixedSubgroup (innerDiagonalAction n K A) :=
  (CatalogueRelativeB.fixedSubgroupEquivalence (scalarProjectiveSpecialLinearEquiv n K)
    (scalarInnerDiagonalAction n K A)).trans
      (MulEquiv.subgroupCongr (congrArg FixedCommutingProduct.fixedSubgroup
        (scalarInnerDiagonalAction_congr n K A)))

theorem scalarInnerFixedEquiv_val (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (x : FixedCommutingProduct.fixedSubgroup (scalarInnerDiagonalAction n K A)) :
    (scalarInnerFixedEquiv n K A x).val = scalarProjectiveSpecialLinearEquiv n K x.val := rfl

theorem scalarInnerDiagonalAction_involution_data (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hne : scalarInnerDiagonalAction n K A ≠ 1)
    (hsq : scalarInnerDiagonalAction n K A ^ 2 = 1) :
    innerDiagonalAction n K A ≠ 1 ∧ innerDiagonalAction n K A ^ 2 = 1 := by
  let e := MulAut.congr (scalarProjectiveSpecialLinearEquiv n K)
  have haction : e (scalarInnerDiagonalAction n K A) = innerDiagonalAction n K A :=
    scalarInnerDiagonalAction_congr n K A
  constructor
  · intro h
    apply hne
    apply e.injective
    rw [haction, h, map_one]
  · rw [← haction, ← map_pow, hsq, map_one]

theorem odd_linear_scalar_inner_diagonal_involution_fixed_p_components
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hodd : Odd (Nat.card K))
    (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hne : scalarInnerDiagonalAction n K A ≠ 1)
    (hsq : scalarInnerDiagonalAction n K A ^ 2 = 1) :
    ∀ (p : ℕ), p.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (scalarInnerDiagonalAction n K A)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  obtain ⟨hne', hsq'⟩ := scalarInnerDiagonalAction_involution_data n K A hne hsq
  intro p hp L hL
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (scalarInnerFixedEquiv n K A)
    (odd_linear_inner_diagonal_involution_fixed_p_components n K hn hodd hparameter A hne' hsq'
      p hp) L hL

end

end CFSG.ComponentClassification.CatalogueBHigherLinearInner
