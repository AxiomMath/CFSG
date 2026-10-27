module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRRee
import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInn2
import CFSG.RankThree.PartOne.RF4.Descent
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI
  CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.LocalAnalysis.GLTheoremA.FR
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions
    large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.HardMathSupport.Lang.Coordinator

section Witness

set_option linter.unusedSectionVars false


private theorem twF4FixedData {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpa : p ≠ 2 * a + 1) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    IsSimpleGroup (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) ∧
      (∃ x y : signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ), x * y ≠ y * x) ∧
      CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalized
        (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) := by
  classical
  obtain ⟨b, hbp, hkcard, hfixed⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK hp hp2 σ hσ
  have hb1 : 1 ≤ b := by
    by_contra h0
    obtain rfl : b = 0 := by omega
    exact hpa (by omega)
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (fixSubfield σ) ReeTag.F4.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hFix : signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) =
      (ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) :=
    Subgroup.ext fun _ => Iff.rfl
  let eC : signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) ≃*
      ReeTag.F4.reeGamma (fixSubfield σ) b :=
    (((signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)).equivMapOfInjective
      (ReeTag.F4.reeGamma K a).subtype (ReeTag.F4.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hfixed))).trans
    ((ReeTag.F4.reeGamma (fixSubfield σ) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype)).symm
  have : IsSimpleGroup (ReeTag.F4.reeGamma (fixSubfield σ) b) :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb1 hkcard
  have hsC : IsSimpleGroup (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) :=
    eC.isSimpleGroup
  have hcardC : 2 ^ 36 ∣ Nat.card (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) := by
    rw [Nat.card_congr eC.toEquiv,
      (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion b
        (fixSubfield σ) hkcard).1]
    set q := 2 ^ (2 * b + 1) with hq
    have h12 : 2 ^ 36 ∣ q ^ 12 := by
      rw [hq, ← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    exact h12.trans (Dvd.intro ((q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
      (q ^ 4 - q ^ 2 + 1)) (by ring))
  have hnp : ¬ (Nat.card (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ))).Prime := by
    intro hpr
    have h2 : 2 ∣ Nat.card (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) :=
      (dvd_pow_self 2 (by norm_num)).trans hcardC
    have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).1 h2
    rw [← h3] at hcardC
    have := Nat.le_of_dvd (by norm_num) hcardC
    norm_num at this
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  exact ⟨hsC, FR.Res.nonab_of_simple hsC hnp,
    CFSG.SignalizerFunctorTheorem.CatalogBridge.nonLocalized_largeRee_of_simple hK σ hsC hcardC⟩

theorem twF4Lang {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K))} (hord : orderOf f = p)
    (hnot : f ∉ (MulAut.conj : LargeEvenCenterQuot (LargeEvenTwF4H a K) →* _).range) :
    ∃ (β : K ≃+* K) (eT : LargeEvenCenterQuot (LargeEvenTwF4H a K) ≃* F4.reeGamma K a),
      orderOf β = p ∧ ∀ y, eT (f y) = F4.reeGammaFieldAut K a β (eT y) := by
  have hR : ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H a K)) .twistedF4 2 (2 * a + 1) :=
    ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩, a, rfl,
      CFSG.StandardType.reeTitsRelationModel_largeEven a hK⟩
  obtain ⟨-, -, -, -, -, -, hmain⟩ := large_Ree_model_field_outer_group_and_inner_involutions _ 2
    (2 * a + 1) hR
  obtain ⟨⟨e⟩, -⟩ := hmain a K rfl hK (CFSG.StandardType.centerQuot_twF4H_equiv K a)
  have : Fact p.Prime := ⟨hp⟩
  have hfp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  set α' : MulAut (F4.reeGamma K a) := MulAut.congr e f with hα'
  have hα'p : α' ^ p = 1 := by rw [hα', ← map_pow, hfp, map_one]
  have hα'inn : α' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (F4.reeGamma K a) :=
    fun h => hnot (((congr_mem_inner_iff e f).mp h))
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α'
  have hΨα : Ψ ⟨x, β⟩ = α' := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut (F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ α' = β := by
    show SemidirectProduct.rightHom (Ψ.symm α') = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ p = 1 := by rw [← hΘα, ← map_pow, hα'p, map_one]
  have hone : F4.reeGammaFieldAut K a 1 = 1 := by rw [← reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα'inn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hp β hβord α'
    hα'p ⟨x, hxβ⟩
  refine ⟨β, e.trans (MulAut.conj g)⁻¹, hβord, fun y => ?_⟩
  have h1 := congrArg (fun φ : MulAut (F4.reeGamma K a) => (MulAut.conj g)⁻¹ (φ (e y))) hg
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hα',
    MulAut.congr_apply, MulEquiv.trans_apply] at h1
  exact h1

theorem twF4NLWitness {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpa : p ≠ 2 * a + 1) {f : MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K))}
    (hord : orderOf f = p)
    (hnot : f ∉ (MulAut.conj : LargeEvenCenterQuot (LargeEvenTwF4H a K) →* _).range) :
    NLWitness f := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K F4.prime := charP_of_card_eq_prime_pow (p := 2) (f := 2 * a + 1) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨β, eT, hβord, key⟩ := twF4Lang ha hK hp hord hnot
  obtain ⟨hsC, hnaC, hNL⟩ := twF4FixedData hK hp hp2 hpa β hβord
  haveI : Finite (ModGL F4.tag K) := finite_modGL
  refine nlWitness_of_nonLocalized eT hsC hnaC hNL ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : F4.reeGammaFieldAut K a β x = x := hx
  show f (eT.symm x) = eT.symm x
  apply eT.injective
  rw [key, MulEquiv.apply_symm_apply]
  exact hx'

end Witness

section Family

set_option linter.unusedSectionVars false


theorem twF4WitnessAt {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twF4) : I2015NLWitnessAt (fun lab p => ¬ regN lab p) lab := by
  intro p hp hp2 _ _ hC
  have hInn := canonRawInnAny hp.ne_one hlab
  have h₁ : CAll lab fun R _ I F => GGRawInnField p R I F →
      LargeEvenSimpleGuard (fun R _ I F => SubfieldBody p lab R I F → ∀ f ∈ F, orderOf f = p →
        Finite R → (∃ J, GLAPComponent p (fixSub f) J) → NLWitness f) R I F := by
    obtain ⟨t, r, n⟩ := lab
    obtain ⟨hn, hl⟩ := hlab
    dsimp only [regN] at ht hn hl hC
    subst ht
    obtain ⟨rfl, ⟨k, hk⟩, hn3⟩ := hl
    subst hk
    have e : (2 * k + 1 - 1) / 2 = k := by omega
    intro Q hQ
    unfold CFSG.Assembly.LargeEvenRawDatum at hQ ⊢
    dsimp only at hQ ⊢
    rw [e] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hF, hfin, hK, hQ', ?_⟩
    intro hinn hs hna _ f hf hord _ _
    obtain ⟨-, -, hconj, hFI⟩ := hinn hs hna
    exact twF4NLWitness (by omega) hK hp hp2 (fun h => hC h.symm) hord
      fun ⟨r, hr⟩ => hFI f hf hord (hr ▸ hconj r)
  exact (h₁.and hInn).mono fun R _ I F ⟨h1, h2⟩ => h1 h2

theorem i2015NLOnTwF4_holds : I2015NLOnTwF4 := by
  intro lab hlab ht
  have ht' : lab.tag = .twF4 := ht
  exact atLabelWhen_of_witness hlab (twF4WitnessAt hlab ht') fun p hC h => hC h.2

end Family

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
