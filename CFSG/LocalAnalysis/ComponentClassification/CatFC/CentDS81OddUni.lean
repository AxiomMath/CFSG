module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddIsom
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.DS81

open CFSG Subgroup Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem hasCompOrSolv_sesqCentralizer {p f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2) :
    HasCompOrSolv (Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B))) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨l, -, -, hN, hP, hM, -, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hA
  have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
    ⟨fun x y => hB.eq (x : V) (y : V)⟩
  obtain ⟨hsig2, hsig1, -⟩ :=
    CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f h.card_eq_sq
  have hsig := CatalogueBUnitaryTwo.unitaryFieldConjugation_apply p f h.card_eq_sq
  have hq3 : 3 ≤ p ^ f := CatLeafProof.OddInner.three_le_pow h.prime hp h.one_le
  have hfix := CatLeafProof.OddInner.card_fixedSubfield hsig2 hsig1 h.card_eq_sq
  have hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E
      (CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq)) ≠ 2 := by
    rw [hfix]; omega
  rcases hN with hN | hN
  ·
    obtain ⟨-, hlP, hlM, e, -⟩ := hsplit hN
    exact HasCompOrSolv.of_mulEquiv
      (e.trans (MulEquiv.prodCongr (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h _)
        (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h _))).symm
      (HasCompOrSolv.prod
        (hasCompOrSolv_isometry_unitary _ (hsymm _)
          (CatalogueBUnitaryB.nondegenerate_of_isSymm (hsymm _) hlP) hsig2 hsig1
          (Submodule.one_le_finrank_iff.mpr hP) hq2)
        (hasCompOrSolv_isometry_unitary _ (hsymm _)
          (CatalogueBUnitaryB.nondegenerate_of_isSymm (hsymm _) hlM) hsig2 hsig1
          (Submodule.one_le_finrank_iff.mpr hM) hq2))
  ·
    obtain ⟨-, -, -, hdim2, -, -, e, -⟩ := hpaired hN
    exact HasCompOrSolv.of_mulEquiv
      (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
        (Module.finBasis E (eigenPlus l (unitaryOp A)))).toMulEquiv)).symm
      (hasCompOrSolv_GL _ E (by omega))

end CFSG.ComponentClassification.CatFC.DS81
