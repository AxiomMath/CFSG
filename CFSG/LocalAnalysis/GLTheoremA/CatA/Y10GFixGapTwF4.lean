module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapGlue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRRee
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestReeF4
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixReeMark
public import CFSG.LieType.Simplicity.TitsModel
public import CFSG.RankThree.PartTwo.KFacts.KS14SzRee
public import CFSG.LieType.BorelTits.DerivedQuotient
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQRee
public import CFSG.RankThree.PartOne.RF4.FinalSec66

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions
    large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.HardMathSupport.Lang.Coordinator CFSG.Assembly
open scoped commutatorElement


theorem exists_fixSub_equiv_reeGamma {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (F : Set (MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K)))) (hF : InnFree p F) :
    ∀ f ∈ F, orderOf f = p → ∃ b : ℕ, (2 * b + 1) * p = 2 * a + 1 ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k F4.prime),
        Nat.card k = 2 ^ (2 * b + 1) ∧ Nonempty (↥(FP.fixSub f) ≃* ↥(F4.reeGamma k b)) := by
  intro f hf hord
  have hR : ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H a K)) .twistedF4 2 (2 * a + 1) :=
    ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩, a, rfl,
      CFSG.StandardType.reeTitsRelationModel_largeEven a hK⟩
  obtain ⟨-, -, -, -, -, -, hmain⟩ := large_Ree_model_field_outer_group_and_inner_involutions _ 2
    (2 * a + 1) hR
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K F4.prime := charP_of_card_eq_prime_pow (p := 2) (f := 2 * a + 1) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨⟨e⟩, -⟩ := hmain a K rfl hK (CFSG.StandardType.centerQuot_twF4H_equiv K a)
  have : Fact p.Prime := ⟨hp⟩
  have hfp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  set α' : MulAut (F4.reeGamma K a) := MulAut.congr e f with hα'
  have hα'p : α' ^ p = 1 := by rw [hα', ← map_pow, hfp, map_one]
  have hα'inn : α' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (F4.reeGamma K a) :=
    fun h => hF f hf hord (((congr_mem_inner_iff e f).mp h))
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
  obtain ⟨b, hbp, hbcard, hfix⟩ := largeRee_fixed_data_of_odd hK hp hp2 β hβord
  have e₂ : ↥(FP.fixSub α') ≃* ↥(FP.fixSub (F4.reeGammaFieldAut K a β)) :=
    (MulEquiv.subgroupCongr (congrArg FP.fixSub hg)).trans
      (fixSubEquivConj (MulAut.conj g) (F4.reeGammaFieldAut K a β)).symm
  have e₃ : ↥(FP.fixSub (F4.reeGammaFieldAut K a β)) ≃* ↥(F4.reeGamma (fixSubfield β) b) :=
    ((((F4.reeGammaFieldAut K a β).toMonoidHom.eqLocus (MonoidHom.id _)).equivMapOfInjective
      (F4.reeGamma K a).subtype (F4.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr hfix)).trans
      ((F4.reeGamma (fixSubfield β) b).equivMapOfInjective _
        (baseChangeGL_injective (τ := F4.tag) (fixSubfield β).subtype)).symm
  have : Finite (fixSubfield β) := Subtype.finite
  haveI : Fintype (fixSubfield β) := Fintype.ofFinite _
  haveI : CharP (fixSubfield β) F4.prime := charP_of_card_eq_prime_pow (p := 2) (f := 2 * b + 1) (by
    rw [← Nat.card_eq_fintype_card, hbcard])
  exact ⟨b, hbp, fixSubfield β, inferInstance, inferInstance, inferInstance, hbcard,
    ⟨((fixSubEquivCongr e f).trans e₂).trans e₃⟩⟩

end FR

namespace Y10GField

open CFSG.Assembly CFSG.StandardType CFSG.Blueprint CFSG.LieType.Ree


theorem twF4Quot_simple {b : ℕ} (hb : 1 ≤ b) {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    IsSimpleGroup (LargeEvenCenterQuot (LargeEvenTwF4H b k)) ∧
      ∃ x y : LargeEvenCenterQuot (LargeEvenTwF4H b k), x * y ≠ y * x := by
  obtain ⟨eR⟩ := gff_nonempty_centerQuot_equiv_reeGamma hb hk
  haveI := gff_isSimpleGroup_reeGamma hb hk
  haveI : Group.IsPerfect ↥(ReeTag.F4.reeGamma k b) :=
    ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hk⟩
  obtain ⟨x, y, hxy⟩ := exists_mul_ne_of_isPerfect ↥(ReeTag.F4.reeGamma k b)
  refine ⟨eR.isSimpleGroup, eR.symm x, eR.symm y, fun h => hxy ?_⟩
  simpa using congrArg eR h

theorem nonempty_titsQuot_equiv {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]
    (hk : Nat.card k = 2) :
    Nonempty (LargeEvenCenterQuot (LargeEvenTwF4H 0 k) ≃*
      ↥(commutator ↥(reeFixed ReeTag.F4 k 0))) := by
  obtain ⟨e₁⟩ := centerQuot_twF4H_equiv k 0
  have e₂ := CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 k 0)).trans
      ((reeFixed ReeTag.F4 k 0).equivMapOfInjective _ Subtype.val_injective).symm)
  exact ⟨(e₁.trans e₂).trans ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.RankThree.PartTwo.KFacts.KS14.center_commutator_reeFixed_tits_eq_bot hk)).trans
      QuotientGroup.quotientBot)⟩

theorem fixGapTwF4_holds : FixGapTwF4 := by
  intro a p K _ _ ha hK hp hp2 f hf hord
  haveI : CharP K ReeTag.F4.prime := charP_two_of_card hK
  obtain ⟨hs, hna⟩ := twF4Quot_simple ha hK
  have hF : FQ.InnFree p (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) :=
    innFree_of_ggRawInnField (RawAutReeF4.ggRawInnField_twF4_of_diag ha hK
      (ggTwistedF4DiagInput_holds a ha K hK hs) hp.one_lt.ne') hs hna
  obtain ⟨b, hbp, k, _, _, _, hk, ⟨φ⟩⟩ :=
    FR.exists_fixSub_equiv_reeGamma ha hK hp hp2 _ hF f hf hord
  have hpn : p ∣ 2 * a + 1 := ⟨2 * b + 1, by rw [← hbp, mul_comm]⟩
  have hdiv : (2 * a + 1) / p = 2 * b + 1 := by rw [← hbp, Nat.mul_div_cancel _ hp.pos]
  have hD : FR.SubfieldGrp f (FP.fixSub f) :=
    ⟨le_rfl, Subgroup.commutator_le_of_le le_rfl le_rfl, by
      rw [Subgroup.relIndex_self]; exact odd_one⟩
  refine ⟨hpn, ?_⟩
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  ·
    subst hb0
    have hk2 : Nat.card k = 2 := by simpa using hk
    obtain ⟨eT⟩ := nonempty_titsQuot_equiv hk2
    haveI : IsSimpleGroup ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) := gff_isSimpleGroup_tits hk2
    haveI : Group.IsPerfect ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) :=
      (CFSG.LieType.Simplicity.titsData k hk2).isPerfect hk2
    obtain ⟨x, y, hxy⟩ := exists_mul_ne_of_isPerfect ↥(commutator ↥(reeFixed ReeTag.F4 k 0))
    refine ⟨LargeEvenCenterQuot (LargeEvenTwF4H 0 k), inferInstance, ⟨.twF4der, 0, 1⟩,
      eT.isSimpleGroup, ⟨eT.symm x, eT.symm y, fun h => hxy (by simpa using congrArg eT h)⟩,
      ⟨le_rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
    · rw [hdiv]
      rfl
    · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
      exact ⟨k, inferInstance, inferInstance, hk, ⟨MulEquiv.refl _⟩⟩
    · unfold ggFixDer
      rw [ggFixSub_eq_fixSub]
      exact ⟨(((CFSG.LieType.BorelTits.commutatorSubgroupEquiv (FP.fixSub f)).trans
        (CFSG.LieType.BorelTits.commutatorEquiv φ)).trans
        (CFSG.LieType.BorelTits.commutatorEquiv (ReeTag.reeFixedEquivReeGamma k 0).symm)).trans
        eT.symm⟩
  ·
    obtain ⟨eR⟩ := gff_nonempty_centerQuot_equiv_reeGamma hb1 hk
    obtain ⟨hs₀, hna₀⟩ := twF4Quot_simple hb1 hk
    have hb' : ((2 * a + 1) / p - 1) / 2 = b := by rw [hdiv]; omega
    refine ⟨LargeEvenCenterQuot (LargeEvenTwF4H b k), inferInstance, ⟨.twF4, 0, (2 * a + 1) / p⟩,
      hs₀, hna₀, ?_, rfl, ?_, nonempty_ggFixDer_equiv hD hna₀ (φ.trans eR.symm)⟩
    · show 1 ≤ (2 * a + 1) / p ∧ ((0 : ℕ) = 0 ∧ Odd ((2 * a + 1) / p) ∧ 3 ≤ (2 * a + 1) / p)
      rw [hdiv]
      exact ⟨by omega, rfl, ⟨b, rfl⟩, by omega⟩
    · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
      show LargeEvenRecipeTwF4 (((2 * a + 1) / p - 1) / 2) _
      rw [hb']
      exact ⟨k, inferInstance, inferInstance, hk, ⟨MulEquiv.refl _⟩⟩

end Y10GField

end CFSG.LocalAnalysis.GLTheoremA

end
