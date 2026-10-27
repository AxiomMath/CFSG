module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTGeneric
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.ReeTransport
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Sporadic.Schreier.Tits
open CFSG.HardMathSupport.Dickson.SuzukiReeB (exists_eq_conj_of_mem_range fixSubgroup_conj)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

theorem reeF4_valid {b : ℕ} (hb : 1 ≤ b) : (TauCeti.LieTypeIndex.reeF4 b).Valid := by
  refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
  · simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using hb
  · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]

theorem tits_valid : TauCeti.LieTypeIndex.tits.Valid := by
  refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
  · simp [TauCeti.LieTypeIndex.inStandardRange_iff]
  · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]

private noncomputable def commutatorEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    ↥(commutator A) ≃* ↥(commutator B) :=
  ((commutator A).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]))

section F4

set_option linter.unusedSectionVars false


theorem commutator_reeGamma_F4_zero_data {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2) :
    IsSimpleGroup ↥(commutator (ReeTag.F4.reeGamma k 0)) ∧
      (∃ x y : ↥(commutator (ReeTag.F4.reeGamma k 0)), x * y ≠ y * x) ∧
      Nonempty (↥(commutator (ReeTag.F4.reeGamma k 0)) ≃*
        (TauCeti.CFSGIndex.lie ⟨.tits, tits_valid⟩).Group) := by
  haveI : Fact (Nat.card k = 2) := ⟨hk⟩
  let e₁ : ↥(commutator (reeFixed ReeTag.F4 k 0)) ≃* ↥(commutator (ReeTag.F4.reeGamma k 0)) :=
    commutatorEquiv' (ReeTag.reeFixedEquivReeGamma k 0)
  let e₂ : ↥(commutator (reeFixed ReeTag.F4 k 0)) ≃* titsD := titsDerivedIso (K := k)
  obtain ⟨e₃⟩ := titsModelEquiv (TauCeti.CFSGIndex.lie ⟨.tits, tits_valid⟩).Group 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨tits_valid, ⟨MulEquiv.refl _⟩⟩)
  let e : ↥(commutator (ReeTag.F4.reeGamma k 0)) ≃* titsD := e₁.symm.trans e₂
  haveI : IsSimpleGroup titsD := titsD_simple
  haveI hs : IsSimpleGroup ↥(commutator (ReeTag.F4.reeGamma k 0)) := e.isSimpleGroup
  refine ⟨hs, ?_, ⟨e.trans e₃.symm⟩⟩
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ x y : titsD, x * y = y * x := fun x y => by
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact hcon _ _
  have hcen : Subgroup.center titsD = ⊤ :=
    eq_top_iff.2 fun x _ => Subgroup.mem_center_iff.2 fun y => hcomm y x
  rw [titsD_center] at hcen
  haveI := titsD_nontrivial
  exact bot_ne_top hcen

theorem exists_fixSubgroup_fieldAut_equiv' {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    ∃ (b : ℕ) (_ : Nat.card (fixSubfield σ) = 2 ^ (2 * b + 1))
      (_ : CharP (fixSubfield σ) ReeTag.F4.prime),
      Nonempty (↥(fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) ≃*
        ↥(ReeTag.F4.reeGamma (fixSubfield σ) b)) := by
  classical
  obtain ⟨b, -, hkcard, hfixed⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK hp hp2 σ hσ
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP (fixSubfield σ) ReeTag.F4.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  haveI := hchar
  have hFix : fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) =
      (ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
  refine ⟨b, hkcard, hchar, ⟨?_⟩⟩
  exact (((fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)).equivMapOfInjective
      (ReeTag.F4.reeGamma K a).subtype (ReeTag.F4.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hfixed))).trans
    ((ReeTag.F4.reeGamma (fixSubfield σ) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype)).symm

theorem srtOut_fieldAut_F4 {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (σ : K ≃+* K)
    (hσ : orderOf σ = p) : SRTOut 2 (ReeTag.F4.reeGammaFieldAut K a σ) := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨b, hkcard, hchar, ⟨eC⟩⟩ := exists_fixSubgroup_fieldAut_equiv' hK hp hp2 σ hσ
  haveI := hchar
  haveI : Finite (fixSubfield σ) := Subtype.finite
  haveI : Finite (ModGL ReeTag.F4.tag (fixSubfield σ)) := finite_modGL
  haveI : Finite ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) := Subtype.finite
  rcases Nat.eq_zero_or_pos b with rfl | hb
  ·
    have hk2 : Nat.card (fixSubfield σ) = 2 := by simpa using hkcard
    obtain ⟨hs, hnc, ⟨hcat⟩⟩ := commutator_reeGamma_F4_zero_data hk2
    haveI := hs
    refine srtOut_of_fixed_equiv_derived _ eC hs hnc ?_ fun hb => ?_
    · exact Or.inl ⟨.lie ⟨.tits, tits_valid⟩, TauCeti.LieTypeIndex.characteristic_tits,
        ⟨hcat⟩⟩
    · exact isEmpty_quot_alternating_six_of_equiv_cat hb hnc ⟨.tits, tits_valid⟩ ⟨hcat⟩
  ·
    have hv := reeF4_valid hb
    obtain ⟨eCat⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeGamma_equiv_cat_of_card hb
        hv hkcard
    have hs : IsSimpleGroup ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hkcard
    have hperf : commutator (ReeTag.F4.reeGamma (fixSubfield σ) b) = ⊤ :=
      ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hkcard
    have hnc : ∃ x y : ↥(ReeTag.F4.reeGamma (fixSubfield σ) b), x * y ≠ y * x := by
      by_contra hab
      push Not at hab
      have hc : commutator ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hab y x
      rw [hperf] at hc
      exact top_ne_bot hc
    refine srtOut_of_fixed_equiv_simple _ hnc ?_ (fun hb' => ?_) eC
    · exact Or.inl ⟨.lie ⟨.reeF4 b, hv⟩, TauCeti.LieTypeIndex.characteristic_reeF4 b,
        ⟨eCat.symm⟩⟩
    · exact isEmpty_quot_alternating_six_of_equiv_cat hb' hnc ⟨.reeF4 b, hv⟩ ⟨eCat.symm⟩

theorem srtOut_reeGamma_F4_inner_three {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) (y : ReeTag.F4.reeGamma K a)
    (hy : orderOf y = 3) : SRTOut 2 (MulAut.conj y) := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨e⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK y hy
  have hF'card : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  haveI : Fintype (GaloisField 2 (2 * (2 * a + 1))) := Fintype.ofFinite _
  have hF'fcard : Fintype.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF'card
  have hq := (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
    (F := GaloisField 2 (2 * (2 * a + 1))) (f := 2 * a + 1) hF'card (by omega)).1
  let E : ↥(fixSubgroup (MulAut.conj y)) ≃*
      ↥(StatedSU 3 (2 ^ (2 * a + 1)) (GaloisField 2 (2 * (2 * a + 1)))) :=
    (MulEquiv.subgroupCongr (fixSubgroup_conj y)).trans e
  have hmq : ((3 : ℕ), 2 ^ (2 * a + 1)) ≠ ((3 : ℕ), 2) := by
    intro h
    have h2 : 2 ^ (2 * a + 1) = 2 := (Prod.mk.inj h).2
    have : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hch : ringChar (GaloisField 2 (2 * (2 * a + 1))) = 2 :=
    ringChar.eq (GaloisField 2 (2 * (2 * a + 1))) 2
  have hFD : LieFactorData 2
      ↥(StatedSU 3 (2 ^ (2 * a + 1)) (GaloisField 2 (2 * (2 * a + 1)))) := by
    have h := suFactorFacts_holds (GaloisField 2 (2 * (2 * a + 1))) 3 (2 ^ (2 * a + 1))
      hF'fcard (by norm_num) hmq
    rw [hch] at h
    exact h
  have hg : (↥(fixSubgroup (MulAut.conj y)) ⧸ Subgroup.center ↥(fixSubgroup (MulAut.conj y))) ≃*
      (↥(StatedSU 3 (2 ^ (2 * a + 1)) (GaloisField 2 (2 * (2 * a + 1)))) ⧸
        Subgroup.center ↥(StatedSU 3 (2 ^ (2 * a + 1)) (GaloisField 2 (2 * (2 * a + 1))))) :=
    QuotientGroup.congr _ _ E (Subgroup.map_center_eq E)
  refine srtOut_of_derived (MulAut.conj y) (N := fixSubgroup (MulAut.conj y)) le_rfl
    (by rw [Subgroup.subgroupOf_self]; exact le_top)
    (CFSG.Open.IsQuasisimple.of_mulEquiv E (LieSemisimple.open_isQuasisimple hq))
    (LieFactorData.of_mulEquiv E.symm hFD) fun _ => ?_
  exact ⟨fun f => (suAltSixFacts_holds (GaloisField 2 (2 * (2 * a + 1))) 3 (2 ^ (2 * a + 1))
    hF'fcard (by norm_num)).false (hg.symm.trans f)⟩

theorem reeF4_inner_or_field {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    {β : MulAut (ReeTag.F4.reeGamma K a)} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    (∃ y : ReeTag.F4.reeGamma K a, β = MulAut.conj y ∧ y ^ p = 1 ∧ y ≠ 1) ∨
      ∃ (σ : K ≃+* K) (g : ReeTag.F4.reeGamma K a), orderOf σ = p ∧
        β = MulAut.conj g * ReeTag.F4.reeGammaFieldAut K a σ * (MulAut.conj g)⁻¹ := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF β
  have hΨα : Ψ ⟨x, σ⟩ = β := by rw [hΨ x σ]; exact hxσ.symm
  let Θ : MulAut (ReeTag.F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘ : Θ β = σ := by
    show SemidirectProduct.rightHom (Ψ.symm β) = σ
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hσp : σ ^ p = 1 := by rw [← hΘ, ← map_pow, hβ, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut K a 1 = 1 :=
    map_one (ReeTag.F4.reeGammaFieldAutHom K a)
  by_cases hσ1 : σ = 1
  · left
    have hβx : β = MulAut.conj x := by
      rw [hxσ]
      change MulAut.conj x * ReeTag.F4.reeGammaFieldAut K a σ = _
      rw [hσ1, hone, mul_one]
    have hZ : Subgroup.center (ReeTag.F4.reeGamma K a) = ⊥ :=
      ReeTag.large_Ree_fixed_group_center_trivial a K hK
    obtain ⟨y, hy, hyp, hy1⟩ := exists_eq_conj_of_mem_range hZ ⟨x, hβx.symm⟩ hβ hβ1
    exact ⟨y, hy, hyp, hy1⟩
  · right
    have hσo : orderOf σ = p := orderOf_eq_prime hσp hσ1
    obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hp σ hσo β hβ
      ⟨x, hxσ⟩
    exact ⟨σ, g, hσo, hg⟩

theorem srtOut_reeGamma_F4_three {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {β : MulAut (ReeTag.F4.reeGamma K a)} (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) : SRTOut 2 β := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases reeF4_inner_or_field ha hK Nat.prime_three hβ hβ1 with ⟨y, rfl, hy3, hy1⟩ |
    ⟨σ, g, hσ, rfl⟩
  · exact srtOut_reeGamma_F4_inner_three ha hK y (orderOf_eq_prime hy3 hy1)
  · exact (srtOut_fieldAut_F4 hK Nat.prime_three (by norm_num) σ hσ).conj (MulAut.conj g)

theorem srtOut_reeF4_three (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) {S : Type}
    [Group S] [Finite S]
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group)) {β : MulAut S}
    (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) : SRTOut 2 β := by
  obtain ⟨e0⟩ := he
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hv e0
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  refine SRTOut.of_congr e ?_
  refine srtOut_reeGamma_F4_three ha hK (by rw [← map_pow, hβ, map_one]) ?_
  exact fun h => hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))

end F4

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
