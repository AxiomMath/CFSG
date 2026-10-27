module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.OddInner

open CFSG Subgroup Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem oddLie_unitary_pos {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {sigma : E ≃+* E} {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : 1 ≤ finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e))
    {L : Subgroup (CatalogueBUnitaryIsometry.isometryGroup h)} (hL : IsComponent L) :
    OddLieCentralQuotient ℓ L := by
  rcases Nat.lt_or_ge (finrank E W) 2 with h1 | h2
  · have := CatalogueBUnitaryIsometry.isometry_one_solvable h (by omega)
    exact absurd hL (not_isComponent_of_isSolvable L)
  · exact oddLie_unitary hℓ hℓ2 he hE h2 h hsym hnd hsigma hne hsig hL

theorem oddLie_sesqCentralizer {p f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2)
    {L : Subgroup (Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B)))}
    (hL : IsComponent L) : OddLieCentralQuotient p L := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨l, -, -, hN, hP, hM, -, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hA
  have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
    ⟨fun x y => hB.eq (x : V) (y : V)⟩
  obtain ⟨hsig2, hsig1, -⟩ :=
    CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f h.card_eq_sq
  have hsig := CatalogueBUnitaryTwo.unitaryFieldConjugation_apply p f h.card_eq_sq
  rcases hN with hN | hN
  ·
    obtain ⟨-, hlP, hlM, e, -⟩ := hsplit hN
    exact oddLieCentralQuotient_of_component_equiv
      (e.trans (MulEquiv.prodCongr (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h _)
        (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h _)))
      (fun M hMc => oddLie_prod
        (fun M₁ hM₁ => oddLie_unitary_pos h.prime hp h.one_le h.card_eq_sq
          (Submodule.one_le_finrank_iff.mpr hP) _ (hsymm _)
          (CatalogueBUnitaryB.nondegenerate_of_isSymm (hsymm _) hlP) hsig2 hsig1 hsig hM₁)
        (fun M₂ hM₂ => oddLie_unitary_pos h.prime hp h.one_le h.card_eq_sq
          (Submodule.one_le_finrank_iff.mpr hM) _ (hsymm _)
          (CatalogueBUnitaryB.nondegenerate_of_isSymm (hsymm _) hlM) hsig2 hsig1 hsig hM₂)
        hMc) hL
  ·
    obtain ⟨-, -, -, hdim2, -, -, e, -⟩ := hpaired hN
    exact oddLieCentralQuotient_of_component_equiv
      (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
        (Module.finBasis E (eigenPlus l (unitaryOp A)))).toMulEquiv))
      (fun M hMc => oddLie_GL h.prime (j := 2 * f) (by have := h.one_le; omega) h.card
        (by omega) hMc) hL

end CFSG.ComponentClassification.CatLeafProof.OddInner
