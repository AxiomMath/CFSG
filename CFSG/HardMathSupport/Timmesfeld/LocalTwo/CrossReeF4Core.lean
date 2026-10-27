module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeNF
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.ReeStabilizer
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
public import CFSG.RankThree.PartTwo.KFacts.KS14SzRee
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofLinkFacts
public import CFSG.RankThree.Chevalley.SteinbergCFPrimeFieldG2LocalCores
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.AlgebraicGroups
open CFSG.LieType.Simplicity (titsData isSimpleGroup_quotient_center_reeFixed_F4)
open CFSG.RankThree.PartTwo.KFacts.KS14 (center_commutator_reeFixed_tits_eq_bot)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form ringAut_commute)

section ReeF4


theorem reeF4_inner_field_trivial {b : ℕ} {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hkcard : Nat.card k = 2 ^ (2 * b + 1)) :
    ∀ ρ : k ≃+* k, ReeTag.F4.reeGammaFieldAut k b ρ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (ReeTag.F4.reeGamma k b) → ρ = 1 := by
  intro ρ hρ
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  · subst hb0
    exact CFSG.RankThree.Chevalley.ringEquiv_eq_one_of_card_eq_prime Nat.prime_two
      (by simpa using hkcard) ρ
  · obtain ⟨-, hNFk', -⟩ :=
      large_Ree_full_inner_field_automorphism_normal_form b hb1 k hkcard
    obtain ⟨y, hy⟩ := hρ
    obtain ⟨q, -, huniq⟩ := hNFk' (ReeTag.F4.reeGammaFieldAut k b ρ)
    have hone' : ReeTag.F4.reeGammaFieldAut k b 1 = 1 :=
      map_one (ReeTag.F4.reeGammaFieldAutHom k b)
    have h1 := huniq (1, ρ) (by simp)
    have h2 := huniq (y, 1) (by
      change ReeTag.F4.reeGammaFieldAut k b ρ =
        MulAut.conj y * ReeTag.F4.reeGammaFieldAut k b 1
      rw [hone', mul_one]
      exact hy.symm)
    exact congrArg Prod.snd (h1.trans h2.symm)

theorem fieldCoreAt_reeGamma_F4 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {σ : K ≃+* K} (hδp : orderOf (ReeTag.F4.reeGammaFieldAut K a σ) = p) {b : ℕ}
    (hkcard : Nat.card (fixSubfield σ) = 2 ^ (2 * b + 1))
    (hfixed : ((ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (ReeTag.F4.reeGamma K a).subtype =
      (ReeTag.F4.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype))
    (hdvd : p ∣ Nat.card ((ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus
      (MonoidHom.id _))) :
    FieldCoreAt p (ReeTag.F4.reeGammaFieldAut K a σ) := by
  classical
  set Γ := ReeTag.F4.reeGamma K a with hΓ
  set δ := ReeTag.F4.reeGammaFieldAut K a σ with hδ
  set J := δ.toMonoidHom.eqLocus (MonoidHom.id _) with hJ
  set k := fixSubfield σ with hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hkcard]; exact (pow_pos (by norm_num) _).ne')
  have : CharP k ReeTag.F4.prime := by
    have : Fintype k := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hinj : Function.Injective (MulAut.conj : Γ →* MulAut Γ) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  let eC : J ≃* ReeTag.F4.reeGamma k b :=
    (((J).equivMapOfInjective Γ.subtype Γ.subtype_injective).trans
      (MulEquiv.subgroupCongr hfixed)).trans
    ((ReeTag.F4.reeGamma k b).equivMapOfInjective _
      (baseChangeGL_injective (τ := ReeTag.F4.tag) k.subtype)).symm
  set R := reeFixed ReeTag.F4 k b with hR
  let e : R ≃* ReeTag.F4.reeGamma k b := ReeTag.reeFixedEquivReeGamma k b
  let eJR : J ≃* R := eC.trans e.symm
  have hZk : Subgroup.center (ReeTag.F4.reeGamma k b) = ⊥ :=
    ReeTag.large_Ree_fixed_group_center_trivial b k hkcard
  have hZR : Subgroup.center R = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center (ReeTag.F4.reeGamma k b) :=
      (MulEquivClass.apply_mem_center_iff e).2 hz
    rw [hZk, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e.injective (hz'.trans (map_one e).symm))
  have hZJ : Subgroup.center J = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have : eJR z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      obtain ⟨y', rfl⟩ := eJR.surjective y
      rw [← map_mul, ← map_mul, hz y']
    rw [hZR, Subgroup.mem_bot] at this
    exact eJR.injective (this.trans (map_one eJR).symm)
  have hRcard : Nat.card J = Nat.card R := Nat.card_congr eJR.toEquiv
  obtain ⟨hSD, hNAD, hpD⟩ : IsSimpleGroup (commutator R) ∧
      (∃ x y : commutator R, x * y ≠ y * x) ∧ p ∣ Nat.card (commutator R) := by
    rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · subst hb0
      have hk2 : Nat.card k = 2 := by simpa using hkcard
      set D := commutator R with hDdef
      have : IsSimpleGroup (D ⧸ Subgroup.center D) := ((titsData k hk2).isQuasisimple hk2).2.1
      have hZD : Subgroup.center D = ⊥ := center_commutator_reeFixed_tits_eq_bot hk2
      have hs : IsSimpleGroup D :=
        ((QuotientGroup.quotientMulEquivOfEq hZD).trans
          QuotientGroup.quotientBot).symm.isSimpleGroup
      obtain ⟨x, hx, y, hy, hxy⟩ := (titsData k hk2).nonabelian
      refine ⟨hs, ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩, ?_⟩
      have hidx : D.index ≤ 2 :=
        CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.index_commutator_tits_le (K := k) hk2
      have hidx0 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hcard := Subgroup.card_mul_index D
      rw [hRcard, ← hcard] at hdvd
      rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · have : IsSimpleGroup (reeFixed ReeTag.F4 k b ⧸ Subgroup.center (reeFixed ReeTag.F4 k b)) :=
        isSimpleGroup_quotient_center_reeFixed_F4 b hb1 hkcard
      have hs : IsSimpleGroup R :=
        ((QuotientGroup.quotientMulEquivOfEq hZR).trans
          QuotientGroup.quotientBot).symm.isSimpleGroup
      have hRna : ∃ x y : R, x * y ≠ y * x := by
        by_contra hc
        push Not at hc
        obtain ⟨x, hx⟩ := exists_ne (1 : R)
        refine hx ?_
        have hxZ : x ∈ Subgroup.center R :=
          Subgroup.mem_center_iff.2 fun z => hc z x
        rwa [hZR, Subgroup.mem_bot] at hxZ
      have hDtop : commutator R = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator R) with h | h
        · exfalso
          obtain ⟨x, y, hxy⟩ := hRna
          have h1 : x * y * x⁻¹ * y⁻¹ ∈ commutator R := by
            rw [commutator_def]
            exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
          rw [h, Subgroup.mem_bot] at h1
          exact hxy (commutatorElement_eq_one_iff_mul_comm.1 h1)
        · exact h
      let eD : commutator R ≃* R := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
      refine ⟨eD.isSimpleGroup, ?_, ?_⟩
      · exact exists_noncomm_of_mulEquiv eD.symm hRna
      · rw [Nat.card_congr eD.toEquiv, ← hRcard]
        exact hdvd
  let eT : commutator J ≃* commutator R :=
    ((commutator J).equivMapOfInjective eJR.toMonoidHom eJR.injective).trans
      (MulEquiv.subgroupCongr
        (CFSG.ComponentClassification.CatalogueBSmallRee.map_commutator_mulEquiv eJR))
  have hSJ : IsSimpleGroup (commutator J) := eT.isSimpleGroup
  have hNAJ : ∃ x y : commutator J, x * y ≠ y * x := by
    exact exists_noncomm_of_mulEquiv eT.symm hNAD
  have hpJ : ¬ Nat.Coprime p (Nat.card (commutator J)) := by
    refine fun hc => (Nat.Prime.coprime_iff_not_dvd hp).1 hc ?_
    rw [Nat.card_congr eT.toEquiv]
    exact hpD
  obtain ⟨-, hNFk, -⟩ := large_Ree_full_inner_field_automorphism_normal_form (a := a) ha K hK
  have hinner := reeF4_inner_field_trivial hkcard
  have hres : ∀ (x : Γ) (τ : K ≃+* K), δ x = x →
      (∀ j : Γ, δ j = j → x * ReeTag.F4.reeGammaFieldAutHom K a τ j * x⁻¹ = j) →
      τ ∈ Subgroup.zpowers σ := fun x τ hx hfix =>
    CFSG.SignalizerFunctorTheorem.CatalogBridge.ree_zpowers_of_inner_on_subfield σ hfixed hinner x
      τ hx hfix
  have hNF : ∀ α : MulAut Γ, ∃ (x : Γ) (τ : K ≃+* K),
      α = MulAut.conj x * (ReeTag.F4.reeGammaFieldAutHom K a) τ := fun α => by
    obtain ⟨⟨x, τ⟩, h, -⟩ := hNFk α
    exact ⟨x, τ, h⟩
  exact fieldCoreAt_of_normalForm_derived hinj
    (fun u v => ringAut_commute u v) (ReeTag.F4.reeGammaFieldAutHom K a) hNF (σ := σ) hδp
    (J := J) (fun z => Iff.rfl) hZJ hSJ hNAJ hpJ hres

end ReeF4

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
