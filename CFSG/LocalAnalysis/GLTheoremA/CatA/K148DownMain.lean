module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148DownCoset
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148DownFacts
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs104
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I148XMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor)

variable {G : Type} [Group G] [Finite G]

theorem k148_phi_ker_le {J I : Subgroup G} (hIJ : I ≤ J) {d : G}
    (hdN : d ∈ Subgroup.normalizer (J : Set G)) (hdI : ∀ i ∈ I, d * i = i * d) :
    (k148Phi hIJ hdN hdI).ker ≤ GLAPPrimeCore 3 ↥I := by
  intro x hx
  apply k148_ker_le hIJ
  rw [MonoidHom.mem_ker] at hx ⊢
  have h := congrArg Subtype.val hx
  rw [k148Phi_val, Subgroup.coe_one] at h
  exact h

theorem k148_outer (hG2 : K148G2SimpleFact) (hTwo : K148TwoG2Fact) {X J I : Subgroup G} {d : G}
    (hJ : GLAPComponent 3 X J) (hchev : IsChevSimple 2 (PSimple 3 J)) (hTD4 : IsTD4 3 J)
    (hdN : d ∈ Subgroup.normalizer (J : Set G)) (hd3 : d ^ 3 = 1) (hNI : NonInner 3 d J)
    (hI : GLAPComponent 3 (J ⊓ cx d) I)
    (hfix : Nat.sqrt (card2 3 J) ≤ 2 * twoPart (Nat.card ↥(lemma102_fixSub 3 hdN))) :
    (∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 ∧
      2 < q.card ∧ Nonempty (PQuot 3 I ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group)) ∨
    catalogIs (PQuot 3 I) (onLie fun | .twistedA 2 q => q.card = 3 | _ => False) := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨q, hv, ⟨eS⟩⟩ := td4_index hTD4
  have hq2 : q.p = 2 := td4g2_p_two hv eS hchev
  have hQJ : CFSG.Open.IsQuasisimple (PQuot 3 J) := isQuasisimple_pQuot_of_glaPComponent hp3 hJ
  have hm : CFSG.Models.LieModel (PQuot 3 J ⧸ Subgroup.center (PQuot 3 J)) .trialityD4
      0 q.p q.exponent :=
    CFSG.Models.lieModel_of_namesTag ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ eS
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hdvd := card_center_dvd_of_table hGA hQJ hm (a := 1) (b := 1) (c := 1) (d := 1) rfl rfl
    (by norm_num)
  have hc1 : Nat.card (Subgroup.center (PQuot 3 J)) = 1 := Nat.dvd_one.1 (by simpa using hdvd)
  have hcenter : Subgroup.center (PQuot 3 J) = ⊥ := Subgroup.eq_bot_of_card_eq _ hc1
  have eQS : PQuot 3 J ≃* PSimple 3 J :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
  obtain ⟨K, hKf, hKfin, σ, hK, hσ, -, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  obtain ⟨-, hfac⟩ := td4_order hv eS
  rw [hq2] at hfac
  have hcard2 : card2 3 J = 2 ^ (12 * q.exponent) := by
    unfold card2 twoPart
    rw [Nat.card_congr eQS.toEquiv, hfac]
  let eQC : PQuot 3 J ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := eQS.trans (eS.trans eC)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hK' : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [hK, hq2]
  have hσ' : ∀ c, σ c = c ^ 2 ^ q.exponent := fun c => by rw [hσ c, hq2]
  set α : MulAut (PQuot 3 J) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 J ⟨d, hdN⟩ with hαdef
  have hα3 : α ^ 3 = 1 := by
    rw [hαdef, ← map_pow]
    have h3 : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (J : Set G))) ^ 3 = 1 := Subtype.ext hd3
    rw [h3, map_one]
  have hαout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (PQuot 3 J) := fun hin =>
    hNI.2 ((inducesInnerMod_iff_barAut_mem_inner hdN).2 hin)
  have hIX : I ≤ J ⊓ Subgroup.centralizer ({d} : Set G) := hI.1
  have hIJ : I ≤ J := hIX.trans inf_le_left
  have hdI : ∀ i ∈ I, d * i = i * d := fun i hi =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hIX hi).2).symm
  have hsubI : CFSG.Open.IsSubnormal I (J ⊓ Subgroup.centralizer ({d} : Set G)) := hI.2.1
  have hQI : CFSG.Open.IsQuasisimple (PQuot 3 I) := isQuasisimple_pQuot_of_glaPComponent hp3 hI
  have hnontrivI : Nontrivial (PQuot 3 I) := by
    haveI : IsSimpleGroup (PQuot 3 I ⧸ Subgroup.center (PQuot 3 I)) := hQI.2
    exact (QuotientGroup.mk_surjective (s := Subgroup.center (PQuot 3 I))).nontrivial
  let Φ := k148Phi hIJ hdN hdI
  obtain ⟨φ, hφ⟩ := k148_quot_hom Φ (k148_phi_ker_le hIJ hdN hdI)
  have hsqrt : Nat.sqrt (card2 3 J) = 2 ^ (6 * q.exponent) := by
    rw [hcard2, show 2 ^ (12 * q.exponent) = (2 ^ (6 * q.exponent)) ^ 2 by rw [← pow_mul]; ring_nf]
    exact Nat.sqrt_eq' _
  set α' : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := MulAut.congr eQC α with hα'def
  have hα'eq : ∀ y, α' (eQC y) = eQC (α y) := fun y => by
    rw [hα'def]
    show eQC (α (eQC.symm (eQC y))) = eQC (α y)
    rw [MulEquiv.symm_apply_apply]
  have hα'3 : α' ^ 3 = 1 := by
    rw [hα'def, ← map_pow, hα3, map_one]
  have hα'out : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut α' := by
    rintro ⟨g, hg⟩
    apply hαout
    refine ⟨eQC.symm g, ?_⟩
    refine MulEquiv.ext (fun y => ?_)
    apply eQC.injective
    rw [← hα'eq, ← hg, MulAut.conj_apply, MulAut.conj_apply]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hFixα : ∀ y : PQuot 3 J, y ∈ lemma102_fixSub 3 hdN ↔ α y = y := by
    intro y
    show lemma102_conjQ 3 hdN y = y ↔ α y = y
    constructor
    · intro h
      calc α y = α (lemma102_conjQ 3 hdN y) := by rw [h]
        _ = y := barAut_comp_conjQ hdN y
    · intro h
      apply α.injective
      rw [barAut_comp_conjQ hdN y, h]
  have hFixMap : (lemma102_fixSub 3 hdN).map eQC.toMonoidHom =
      CFSG.RankThree.PartTwo.Sec4.autFix α' := by
    ext c
    constructor
    · rintro ⟨y, hy, rfl⟩
      show α' (eQC y) = eQC y
      rw [hα'eq, (hFixα y).1 hy]
    · intro hc
      refine ⟨eQC.symm c, (hFixα _).2 ?_, eQC.apply_symm_apply c⟩
      apply eQC.injective
      rw [← hα'eq, MulEquiv.apply_symm_apply]
      exact hc
  have hFixIso : ↥(lemma102_fixSub 3 hdN) ≃* ↥(CFSG.RankThree.PartTwo.Sec4.autFix α') :=
    (MulEquiv.subgroupMap eQC (lemma102_fixSub 3 hdN)).trans (MulEquiv.subgroupCongr hFixMap)
  have hcardFix : Nat.card ↥(lemma102_fixSub 3 hdN) =
      Nat.card ↥(CFSG.RankThree.PartTwo.Sec4.autFix α') := Nat.card_congr hFixIso.toEquiv
  have h3f : (2 ^ q.exponent) ^ 3 = 2 ^ (3 * q.exponent) := by rw [← pow_mul, mul_comm]
  rcases CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv
      hf hK' hσ' hα'3 hα'out with hstd | ⟨e2⟩
  ·
    obtain ⟨β, hβ⟩ := hstd
    have eA : Nonempty (↥(CFSG.RankThree.PartTwo.Sec4.autFix α') ≃*
        ↥(CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ))) := by
      rcases hβ with h | h
      · rw [h]
        exact td4g2_autFix_conj β (fieldActor (t := TwistTag.D4) σ σ)
      · rw [h]
        have h' := td4g2_autFix_conj β (fieldActor (t := TwistTag.D4) σ σ)⁻¹
        rw [td4g2_autFix_inv] at h'
        exact h'
    obtain ⟨eA⟩ := eA
    let eFix : ↥(lemma102_fixSub 3 hdN) ≃*
        ↥(CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) :=
      hFixIso.trans eA
    have hR := k148_sub_fix hIJ hdN hd3 hdI hIX hsubI
    rcases Nat.lt_or_ge q.exponent 2 with hlt | hge
    ·
      have hf1 : q.exponent = 1 := by omega
      have hK1 : Nat.card K = (2 ^ 1) ^ 3 := by rw [hK', hf1]
      have hσ1 : ∀ c, σ c = c ^ 2 ^ 1 := fun c => by rw [hσ' c, hf1]
      exact Or.inr (hTwo K σ hK1 hσ1 (lemma102_fixSub 3 hdN) eFix _ hR
        (PQuot 3 I) φ hφ hQI)
    ·
      have hsimp :
          IsSimpleGroup ↥(CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) :=
        hG2 K σ q.exponent hge hK' hσ'
      have hsimpFix : IsSimpleGroup ↥(lemma102_fixSub 3 hdN) := MulEquiv.isSimpleGroup eFix
      rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimpFix hR with hbot | htop
      ·
        exfalso
        obtain ⟨z, hz⟩ := exists_ne (1 : PQuot 3 I)
        obtain ⟨r, rfl⟩ := hφ z
        have hr : (r : ↥(lemma102_fixSub 3 hdN)) = 1 := by
          have hr' : (r : ↥(lemma102_fixSub 3 hdN)) ∈ (⊥ : Subgroup ↥(lemma102_fixSub 3 hdN)) :=
            (le_of_eq hbot) r.2
          exact Subgroup.mem_bot.1 hr'
        have hr1 : r = 1 := Subtype.ext hr
        exact hz (by rw [hr1, map_one])
      · have eRF : ↥(k148Phi hIJ hdN hdI).range ≃* ↥(lemma102_fixSub 3 hdN) :=
          (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
        haveI : IsSimpleGroup ↥(k148Phi hIJ hdN hdI).range := MulEquiv.isSimpleGroup eRF
        obtain ⟨eQ⟩ := k148_iso_of_simple φ hφ hnontrivI
        have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
        have hqc : 2 < q.card := by
          rw [hcard]
          calc 2 < 2 ^ 2 := by norm_num
            _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hge
        have h3c : 3 ≤ q.card := by omega
        have hvG2 : (TauCeti.LieTypeIndex.G2 q).Valid :=
          (TauCeti.LieTypeIndex.valid_iff _).2
            ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 h3c,
              by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
        have hKq : Nat.card K = (q.p ^ q.exponent) ^ 3 := by rw [hq2]; exact hK'
        have hσq : ∀ c, σ c = c ^ (q.p ^ q.exponent) := fun c => by rw [hq2]; exact hσ' c
        obtain ⟨eG2⟩ := td4g2_fixSub_G2 hvG2 hKq hσq
        exact Or.inl ⟨q, hvG2, hq2, hqc,
          ⟨eQ.symm.trans (eRF.trans (eFix.trans eG2))⟩⟩
  ·
    exfalso
    obtain ⟨e2'⟩ := e2
    have h2 := td4g2_pgl_case_twoPart hf hK' hσ' e2'
    rw [← hcardFix] at h2
    rw [h2, h3f, hsqrt] at hfix
    have h1 : 2 ^ (6 * q.exponent) ≤ 2 ^ (3 * q.exponent + 1) := by
      calc 2 ^ (6 * q.exponent) ≤ 2 * 2 ^ (3 * q.exponent) := hfix
        _ = 2 ^ (3 * q.exponent) * 2 := by ring
        _ = 2 ^ (3 * q.exponent + 1) := by rw [pow_succ]
    have h2' : 6 * q.exponent ≤ 3 * q.exponent + 1 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
    omega

theorem i148d_of_facts (G : Type) [Group G] [Finite G] (hInn : K148InnerCentFact) (hG2 : K148G2SimpleFact)
    (hTwo : K148TwoG2Fact) : I148DownAt G := by
  intro X J I d hJ hchev hTD4 hdN hd3 hnc hI hsq
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨q, hv, ⟨eS⟩⟩ := td4_index hTD4
  have hq2 : q.p = 2 := td4g2_p_two hv eS hchev
  have hQJ : CFSG.Open.IsQuasisimple (PQuot 3 J) := isQuasisimple_pQuot_of_glaPComponent hp3 hJ
  have hm : CFSG.Models.LieModel (PQuot 3 J ⧸ Subgroup.center (PQuot 3 J)) .trialityD4
      0 q.p q.exponent :=
    CFSG.Models.lieModel_of_namesTag ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ eS
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hdvd := card_center_dvd_of_table hGA hQJ hm (a := 1) (b := 1) (c := 1) (d := 1) rfl rfl
    (by norm_num)
  have hc1 : Nat.card (Subgroup.center (PQuot 3 J)) = 1 := Nat.dvd_one.1 (by simpa using hdvd)
  have hcenter : Subgroup.center (PQuot 3 J) = ⊥ := Subgroup.eq_bot_of_card_eq _ hc1
  have eQS : PQuot 3 J ≃* PSimple 3 J :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
  obtain ⟨K, hKf, hKfin, σ, hK, hσ, -, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  obtain ⟨-, hfac⟩ := td4_order hv eS
  rw [hq2] at hfac
  have hcard2 : card2 3 J = 2 ^ (12 * q.exponent) := by
    unfold card2 twoPart
    rw [Nat.card_congr eQS.toEquiv, hfac]
  let eQC : PQuot 3 J ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := eQS.trans (eS.trans eC)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hK' : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [hK, hq2]
  have hσ' : ∀ c, σ c = c ^ 2 ^ q.exponent := fun c => by rw [hσ c, hq2]
  set α : MulAut (PQuot 3 J) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 J ⟨d, hdN⟩ with hαdef
  have hα3 : α ^ 3 = 1 := by
    rw [hαdef, ← map_pow]
    have h3 : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (J : Set G))) ^ 3 = 1 := Subtype.ext hd3
    rw [h3, map_one]
  have hα1 : α ≠ 1 := fun h =>
    hnc ((chev_barAut_eq_one_iff_centMod (p := 3) hdN).1 (hαdef.symm.trans h))
  have hIJ : I ≤ J := hI.1.trans inf_le_left
  have hdI : ∀ i ∈ I, d * i = i * d := fun i hi =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hI.1 hi).2).symm
  let Φ := k148Phi hIJ hdN hdI
  obtain ⟨φ, hφ⟩ := k148_quot_hom Φ (k148_phi_ker_le hIJ hdN hdI)
  have hcardI : Nat.card (PQuot 3 I) ∣ Nat.card ↥(lemma102_fixSub 3 hdN) :=
    (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_subgroup_dvd_card _)
  have hbound : card2 3 I ≤ twoPart (Nat.card ↥(lemma102_fixSub 3 hdN)) :=
    lemma102_twoPart_le_of_dvd (Nat.card_pos).ne' hcardI
  have hsqrt : Nat.sqrt (card2 3 J) = 2 ^ (6 * q.exponent) := by
    rw [hcard2, show 2 ^ (12 * q.exponent) = (2 ^ (6 * q.exponent)) ^ 2 by rw [← pow_mul]; ring_nf]
    exact Nat.sqrt_eq' _
  have key : card2 3 I ≤ 2 ^ (3 * q.exponent) → False := by
    intro hm
    rw [hsqrt] at hsq
    have h1 : 2 ^ (6 * q.exponent) ≤ 2 ^ (3 * q.exponent + 1) := by
      rw [pow_succ]
      calc 2 ^ (6 * q.exponent) ≤ 2 * card2 3 I := hsq
        _ ≤ 2 * 2 ^ (3 * q.exponent) := Nat.mul_le_mul_left 2 hm
        _ = 2 ^ (3 * q.exponent) * 2 := by ring
    have h2 : 6 * q.exponent ≤ 3 * q.exponent + 1 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
    omega
  by_cases hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PQuot 3 J)
  ·
    exfalso
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hin
    have hc3 : c ^ 3 = 1 := by
      have h3 : MulAut.conj (c ^ 3) = 1 := by rw [map_pow, hc, hα3]
      have hmem : c ^ 3 ∈ Subgroup.center (PQuot 3 J) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg := congrArg (fun φ : MulAut (PQuot 3 J) => φ g) h3
        simp only [MulAut.conj_apply, MulAut.one_apply] at hg
        exact (mul_inv_eq_iff_eq_mul.1 hg).symm
      rw [hcenter] at hmem
      exact Subgroup.mem_bot.1 hmem
    have hc1 : c ≠ 1 := by
      intro h
      apply hα1
      rw [← hc, h, map_one]
    have hfix := lemma102_fixSub_eq_centralizer hdN hc
    have hcentC : Nat.card (Subgroup.centralizer ({c} : Set (PQuot 3 J))) =
        Nat.card (Subgroup.centralizer ({eQC c} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
      apply Nat.card_congr
      refine Equiv.subtypeEquiv eQC.toEquiv (fun g => ?_)
      show g ∈ Subgroup.centralizer ({c} : Set (PQuot 3 J)) ↔
        eQC g ∈ Subgroup.centralizer ({eQC c} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← map_mul,
        ← map_mul, eQC.injective.eq_iff]
    have hz3 : eQC c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
    have hz1 : eQC c ≠ 1 := fun h => hc1 (eQC.injective (by rw [h, map_one]))
    have hres := hInn q.exponent hf K σ hK' hσ' (eQC c) hz3 hz1
    have hb2 : card2 3 I ≤ twoPart (Nat.card (Subgroup.centralizer ({c} : Set (PQuot 3 J)))) := by
      rw [← hfix]
      exact hbound
    rw [hcentC, hres] at hb2
    have h3f : (2 ^ q.exponent) ^ 3 = 2 ^ (3 * q.exponent) := by rw [← pow_mul, mul_comm]
    exact key (h3f ▸ hb2)
  ·
    have hNI : NonInner 3 d J := ⟨hdN, fun h => hin ((inducesInnerMod_iff_barAut_mem_inner hdN).1 h)⟩
    rcases k148_outer hG2 hTwo hJ hchev hTD4 hdN hd3 hNI hI
        (hsq.trans (Nat.mul_le_mul_left 2 hbound)) with ⟨q, hv, -, -, ⟨e⟩⟩ | hcat
    · exact ⟨hNI, ⟨TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩, Or.inl trivial, ⟨e⟩⟩⟩
    · exact ⟨hNI, catalogIs_imp (fun i hi => Or.inr hi) hcat⟩

end CFSG.LocalAnalysis.GLTheoremA

end
