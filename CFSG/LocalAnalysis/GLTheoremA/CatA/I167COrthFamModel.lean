module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFamDesc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthPlus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthMinus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth
  CFSG.SeitzReduction.OmegaPilot

@[expose] def FieldModel (p : ℕ) {S : Type} [Group S] (β : MulAut S) (N a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (k : Subfield K) (Q₀ : QuadraticForm k (Fin (2 * N) → k))
    (Q : QuadraticForm K (Fin (2 * N) → K)) (σ : K ≃+* K) (SS : SubfieldSetup k Q₀ Q σ p)
    (ψ : S ≃* matrixProjectiveDerived Q),
    Nat.card K = 2 ^ a ∧ Nat.card K = Nat.card k ^ p ∧ MulAut.congr ψ β = fieldAutT Q σ SS.hQσ

theorem i167COrth_card_pow {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
    {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}
    (SS : SubfieldSetup k Q₀ Q σ p) : Nat.card K = Nat.card k ^ p := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hK⟩ := FiniteField.card K (ringChar K)
  have hK' : Nat.card K = ringChar K ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hK]
  have hk : k = CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ :=
    Subfield.ext fun x => (SS.hσk x).trans (RingHom.mem_eqLocusField
      (f := (σ : K →+* K)) (g := RingHom.id K)).symm
  obtain ⟨hdvd, hfix⟩ :=
    CFSG.RankThree.PartOne.card_semilinearFixedSubfield hℓ n.2 hK' SS.hσ
  rw [hK', hk, hfix, ← pow_mul, Nat.div_mul_cancel hdvd]
  rfl

theorem i167COrth_fieldModel_plus {S : Type} [Group S] {labK : GLALabel} {β : MulAut S} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥) (ht : labK.tag = .D)
    (hr3 : labK.rank ≠ 3) (hfld : FieldKind S labK β) (hβ : β ^ p = 1) :
    FieldModel p β labK.rank labK.n := by
  obtain ⟨hm4, hn1, K, hKf, hKfin, hcard, hs, hna, e, i, f, hi, hf, hcongr, hout⟩ :=
    fieldKind_omegaPlus_data hcen ht hr3 hfld
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hcard
  obtain ⟨σ, ψ, hσ, hψ⟩ := FOC.exists_congr_eq_fieldAutT (m := labK.rank) (p := p)
    (by omega) hp hp2 hs hna e hi hf hcongr hout hβ
  obtain ⟨hpn, k, hk, SS⟩ := FOC.exists_subfieldSetup_plus (m := labK.rank) (n := labK.n)
    (by omega) hn1 hp hp2 hcard hσ
  refine ⟨K, hKf, hKfin, k, coordinateQuadPlus labK.rank k, coordinateQuadPlus labK.rank K,
    σ, SS, ψ, hcard, ?_, ?_⟩
  · rw [hk, ← pow_mul, Nat.div_mul_cancel hpn]
    exact hcard
  · exact hψ

theorem i167COrth_fieldModel_minus {S : Type} [Group S] {labK : GLALabel} {β : MulAut S} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥) (ht : labK.tag = .twD)
    (hr2 : labK.rank ≠ 2) (hr3 : labK.rank ≠ 3) (hfld : FieldKind S labK β) (hβ : β ^ p = 1) :
    FieldModel p β labK.rank labK.n := by
  obtain ⟨hm4, hS, hout⟩ := fieldKind_omegaMinus_model hcen ht hr2 hr3 hfld
  have hm1 : 1 ≤ labK.rank := by omega
  obtain ⟨hpf, K, _, _, k, b, c, hirr, σ, SS, φ, hk, hφ⟩ :=
    FOD.orthFieldDatum_minus hm1 hS hp hp2 hβ hout
  have hcardK : Nat.card K = 2 ^ labK.n := by
    rw [i167COrth_card_pow SS, hk, ← pow_mul, Nat.div_mul_cancel hpf]
  exact ⟨K, inferInstance, inferInstance, k, coordinateQuadMinus labK.rank k hm1 b c,
    coordinateQuadMinus labK.rank K hm1 (b : K) (c : K), σ, SS, φ, hcardK,
    i167COrth_card_pow SS, hφ⟩

theorem i167COrth_fieldAutT_fix_iff {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (σ : K ≃+* K)
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) (hQ : ∃ v, Q v ≠ 0)
    (g : ↥(orthDerived Q)) :
    fieldAutT Q σ hQσ (orthDerivedProjEquiv Q hQ g) = orthDerivedProjEquiv Q hQ g ↔
      SigmaEquivariant σ (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
  set y : matrixDerived Q := (derivedEquiv Q).symm g with hy
  have hgy : derivedEquiv Q y = g := by rw [hy]; exact MulEquiv.apply_symm_apply (derivedEquiv Q) g
  have hproj : orthDerivedProjEquiv Q hQ g = projHom Q g := rfl
  have hfield : projHom Q g = matrixProjectiveProjection Q y := by
    change matrixProjectiveProjection Q ((derivedEquiv Q).symm g) = matrixProjectiveProjection Q y
    rw [← hy]
  set w : matrixDerived Q := matrixDerivedConjugation Q (fieldPair Q σ hQσ) y with hw
  have hval : (w : GL (Fin d) K) = CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K σ y.val := by
    rw [hw]; exact matrixDerivedConjugation_fieldPair_val Q σ hQσ y
  have hFA : fieldAutT Q σ hQσ (orthDerivedProjEquiv Q hQ g) = projHom Q (derivedEquiv Q w) := by
    rw [hproj, hfield, fieldAutT_mk, ← hw]; simp [projHom]
  have hkey : fieldAutT Q σ hQσ (orthDerivedProjEquiv Q hQ g) = orthDerivedProjEquiv Q hQ g ↔ w = y := by
    rw [hFA, hproj]
    constructor
    · intro h
      exact (derivedEquiv Q).injective ((projHom_injective hQ h).trans hgy.symm)
    · intro h; rw [h, hgy]
  have hgcoe : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) = matrixLinearEquiv y.val := by
    rw [← hgy, coe_derivedEquiv, matrixLinearIso_apply_eq]
  have hB : SigmaEquivariant σ (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ↔ CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K σ y.val = y.val := by
    rw [hgcoe]
    change (∀ v, matrixLinearEquiv y.val (coordinateFieldMap d σ v) = coordinateFieldMap d σ (matrixLinearEquiv y.val v)) ↔ CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K σ y.val = y.val
    constructor
    · intro h
      apply matrixLinearIso.injective
      apply LinearEquiv.ext
      intro u
      obtain ⟨v, rfl⟩ := (coordinateFieldMap d σ).surjective u
      rw [matrixLinearIso_apply_eq, matrixLinearIso_apply_eq, ← coordinateFieldMap_matrix σ y.val v]
      exact (h v).symm
    · intro h v; rw [coordinateFieldMap_matrix σ y.val v, h]
  have hwy : w = y ↔ CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K σ y.val = y.val := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← hval]; exact congrArg Subtype.val h
    · exact Subtype.ext (by rw [hval, h])
  exact hkey.trans (hwy.trans hB.symm)

theorem i167COrth_fieldModel_fix_iff {S : Type} [Group S] {β : MulAut S} {K : Type} [Field K]
    [Finite K] [CharP K 2] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) (σ : K ≃+* K)
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) (hQ : ∃ v, Q v ≠ 0)
    (ψ : S ≃* matrixProjectiveDerived Q) (hψ : MulAut.congr ψ β = fieldAutT Q σ hQσ) (s : S) :
    β s = s ↔
      SigmaEquivariant σ (((orthDerivedProjEquiv Q hQ).symm (ψ s) : ↥(orthDerived Q)) :
        (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
  rw [← i167COrth_fieldAutT_fix_iff Q σ hQσ hQ ((orthDerivedProjEquiv Q hQ).symm (ψ s))]
  rw [MulEquiv.apply_symm_apply, ← hψ]
  have h1 : (MulAut.congr ψ β) (ψ s) = ψ (β s) := by
    show ψ (β (ψ.symm (ψ s))) = ψ (β s)
    rw [MulEquiv.symm_apply_apply]
  rw [h1]
  exact ⟨fun h => congrArg ψ h, fun h => ψ.injective h⟩

end CFSG.LocalAnalysis.GLTheoremA.I167

end
