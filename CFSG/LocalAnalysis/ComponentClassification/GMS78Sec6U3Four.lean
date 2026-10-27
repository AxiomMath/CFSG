module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6U3FourCases
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveReduce
import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6QuasiC
import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6NotNormalC

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

section Reduce

variable {X : Type} [Group X] [Finite X]

theorem exists_setting310_sup
    (h32 : AS76b.Lemma32) (h332 : AS76b.Lemma33Two) (hcfg : AS76b.Section3Config)
    {A R : Subgroup X} (hH : RankTwoHyp X A) (hO : standardComponentOddCore X = ⊥)
    (hA5 : Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin 5)))
    (hodd : Odd (Nat.card (center ↥A))) (hR : IsSylowOf 2 R (centralizer (A : Set X)))
    (hno : ∀ x : X, ¬ rightConjugate R x ≤ A) :
    ∃ (g : ↥(rankTwoX A ⊔ R)) (T V₀ : Subgroup ↥(rankTwoX A ⊔ R)),
      RankTwoAltFive.Setting310 (A.subgroupOf (rankTwoX A ⊔ R)) (R.subgroupOf (rankTwoX A ⊔ R))
        g T V₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hA5
  have hAperf : commutator ↥A = ⊤ := hH.standard.1.1
  have hZ : center ↥A = ⊥ := RankTwoAlt.center_eq_bot_of_odd_five hAperf e hodd
  let eA : ↥A ≃* RankTwoAltFive.A5 :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  have hA31 : AS76b.Hyp31 A :=
    ⟨hH.standard, RankTwoClassical.hypIIAlt5 ↥A hAperf ⟨e⟩, hO, by have := hH.rank; omega,
      hH.not_normal⟩
  have hstd := hH.standard
  obtain ⟨hXF, hXs⟩ := AS76b.asc08Lemma34 X A hA31
  have hXsimple : IsSimpleGroup ↥(rankTwoX A) := by
    rw [show rankTwoX A = CFSG.generalizedFitting X from hXF]
    exact hXs
  set H := rankTwoX A ⊔ R with hHdef
  have hAX : A ≤ rankTwoX A := le_normalClosure
  have hAG₁ : A ≤ H := hAX.trans le_sup_left
  have hRG₁ : R ≤ H := le_sup_right
  have hAc : Nat.card A = 60 := by rw [Nat.card_congr eA.toEquiv, RankTwoAltFive.card_A5]
  have hA1 : ∀ {B : Subgroup X}, A ≤ B → B = ⊥ → False := by
    intro B hAB hB1
    rw [hB1, le_bot_iff] at hAB
    apply hH.not_normal
    rw [hAB]
    infer_instance
  have heven : Even (Nat.card (centralizer (A : Set X) ⊓ H : Subgroup X)) := by
    have hR1 : R ≠ ⊥ :=
      AS76b.isSylowOf_ne_bot_of_even hR (AS76b.tightlyEmbedded_centralizer hstd).1
    have h2R : 2 ∣ Nat.card R := by
      rcases hR.isPGroup.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hR1
      · exact h
    exact even_iff_two_dvd.mpr (h2R.trans (Subgroup.card_dvd_of_le (le_inf hR.le hRG₁)))
  have hstd₁ := standard_subgroupOf hstd hAG₁ heven
  have hnn : ¬ (A.subgroupOf H).Normal := by
    intro hn
    have hnX : (A.subgroupOf (rankTwoX A)).Normal := by
      constructor
      intro a ha x
      have h1 := hn.conj_mem ⟨(a : X), hAG₁ ha⟩ ha ⟨(x : X), le_sup_left (b := R) x.2⟩
      rw [mem_subgroupOf] at h1 ⊢
      simpa using h1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf (rankTwoX A)) with h | h
    · rw [subgroupOf_eq_bot] at h
      exact hA1 le_rfl (le_bot_iff.mp fun a ha => h.le_bot ⟨ha, hAX ha⟩)
    · apply hH.not_normal
      rw [le_antisymm hAX (subgroupOf_eq_top.mp h)]
      infer_instance
  have hrank₁ : 2 ≤ Open.pRank 2 (centralizer ((A.subgroupOf H : Subgroup ↥H) : Set ↥H)) := by
    obtain ⟨U, hUK, hU, hU4⟩ := RankTwoSporadic.exists_four_le_of_two_le_pRank hH.rank
    obtain ⟨c, -, hcU⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hR
      (fun v => ⟨1, Subtype.ext (by simpa using hU.2 v v.2)⟩) hUK
    have hEG₁ : rightConjugate U c ≤ H := hcU.trans hRG₁
    have hUc := AS76b.isElemAbelian_rightConjugate hU c
    refine CFSG.SectionRank.le_pRank one_lt_two
      (E := (rightConjugate U c).subgroupOf H) ?_ ?_ ?_
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (mem_centralizer_iff.mp (hR.le (hcU (mem_subgroupOf.mp hx))) y
        (mem_subgroupOf.mp hy))
    · refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
      · apply Subtype.ext
        apply Subtype.ext
        simpa using
          congrArg Subtype.val (hUc.1.is_comm.comm ⟨((x : ↥H) : X), x.2⟩ ⟨((y : ↥H) : X), y.2⟩)
      · rw [mem_subgroupOf] at hx
        exact Subtype.ext (by simpa using hUc.2 _ hx)
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hU4, ← rightConjugate_card U c]
      exact Nat.card_congr (subgroupOfEquivOfLe hEG₁).toEquiv
  have hH₁ : RankTwoHyp ↥H (A.subgroupOf H) :=
    ⟨LocalAnalysis.ComponentInitial.kProper_subgroup
      (fun e h => SectionRank.catalog_of_mulEquiv e h) hH.kProper _, hstd₁, hnn, hrank₁⟩
  let eA₁ : ↥(A.subgroupOf H) ≃* ↥A := subgroupOfEquivOfLe hAG₁
  have hO₁ : standardComponentOddCore ↥H = ⊥ :=
    RankTwoAltFive.oddCore_sup_eq_bot hXF hXsimple (by rw [hAc]; decide)
  let e₁ : rankTwoQuot (A.subgroupOf H) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr (center _) (center _) eA₁ (Subgroup.map_center_eq eA₁)).trans e
  have hodd₁ : Odd (Nat.card (center ↥(A.subgroupOf H))) := by
    rwa [Nat.card_congr (Subgroup.centerCongr eA₁).toEquiv]
  have hR₁ : IsSylowOf 2 (R.subgroupOf H) (centralizer ((A.subgroupOf H : Subgroup ↥H) :
      Set ↥H)) := by
    rw [GMS78.centralizer_subgroupOf_eq hAG₁, ← isSylowOf_map_subtype_iff H,
      subgroupOf_map_subtype, subgroupOf_map_subtype, inf_eq_left.mpr hRG₁,
      inf_eq_left.mpr inf_le_right]
    exact hR.of_le (le_inf hR.le hRG₁) inf_le_left
  have hno₁ : ∀ x : ↥H, ¬ rightConjugate (R.subgroupOf H) x ≤ A.subgroupOf H := by
    intro x hx
    apply hno x
    intro r hr
    have hrH : r ∈ H := by
      have h1 : (x : X) * r * (x : X)⁻¹ ∈ H := hRG₁ ((mem_rightConjugate_iff _ _ _).mp hr)
      have h2 := H.mul_mem (H.mul_mem (H.inv_mem x.2) h1) x.2
      simpa [mul_assoc] using h2
    have h := hx ((RankTwoAltFive.mem_rightConjugate_subgroupOf x ⟨r, hrH⟩).mpr hr)
    exact mem_subgroupOf.mp h
  have hle : (rankTwoX (A.subgroupOf H)).map H.subtype ≤ rankTwoX A := by
    rw [map_le_iff_le_comap]
    have : ((rankTwoX A).comap H.subtype).Normal :=
      (normalClosure_normal (s := (A : Set X))).comap _
    exact normalClosure_le_normal fun a ha => hAX (mem_subgroupOf.mp ha)
  have hX₁ : (rankTwoX (A.subgroupOf H)).map H.subtype = rankTwoX A := by
    refine le_antisymm hle ?_
    have hnN : (((rankTwoX (A.subgroupOf H)).map H.subtype).subgroupOf (rankTwoX A)).Normal := by
      constructor
      intro n hn x
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨m, hm, hmn⟩ := hn
      have hx₁ : (x : X) ∈ H := le_sup_left (b := R) x.2
      refine ⟨⟨x, hx₁⟩ * m * ⟨x, hx₁⟩⁻¹, (normalClosure_normal).conj_mem m hm _, ?_⟩
      simp [← hmn]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (((rankTwoX (A.subgroupOf H)).map H.subtype).subgroupOf (rankTwoX A)) with h | h
    · exfalso
      rw [subgroupOf_eq_bot] at h
      refine hA1 (B := ⊥) (fun a ha => h.le_bot ⟨?_, hAX ha⟩) rfl
      exact ⟨⟨a, hAG₁ ha⟩, le_normalClosure ha, rfl⟩
    · exact subgroupOf_eq_top.mp h
  have hXR₁ : rankTwoX (A.subgroupOf H) ⊔ R.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, hX₁, subgroupOf_map_subtype, inf_eq_left.mpr hRG₁,
      ← MonoidHom.range_eq_map, range_subtype]
  have hA31₁ : AS76b.Hyp31 (A.subgroupOf H) :=
    ⟨hstd₁, RankTwoClassical.hypIIAlt5 _ hstd₁.1.1 ⟨e₁⟩, hO₁, by omega, hnn⟩
  obtain ⟨g, hg, T, hT, hTN, hTR⟩ := RankTwoAltFive.exists_sec3 hcfg hA31₁ hR₁
  have hloc :=
    RankTwoAltFive.case310Local_of h32 h332 hA31₁ (eA₁.trans eA) hR₁ hno₁ hg hT hTN hTR
  exact ⟨g, T, _, RankTwoAltFive.setting310_of hH₁ hO₁ ⟨e₁⟩ hodd₁ hR₁ hno₁ hXR₁ hloc⟩

end Reduce

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T : Subgroup G}

theorem false_of_four_of_standard
    (h3 : Sec3 G L T) (hF : Foundation)
    (hcfg : AS76b.Section3Config) (hGold : Asc76X.GoldschmidtTheoremA)
    (hIIb : RankTwoAltFive.Asc310IIb) (hKP : Assembly.KProper Blueprint.Catalog G)
    (e : rankTwoQuot L ≃* PSU3 2 2) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    (hstd : standardComponentIsStandard (oddQuotImageC K (u3X₀ L K)))
    (hnn : ¬ (oddQuotImageC K (u3X₀ L K)).Normal) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Xb := oddQuotImageC K (u3X₀ L K) with hXb
  have hKP₁ : Assembly.KProper Blueprint.Catalog (u3G₁Bar K) :=
    CatalogueKProperOver.kProper_quotient (fun e h => SectionRank.catalog_of_mulEquiv e h)
      (LocalAnalysis.ComponentInitial.kProper_subgroup
        (fun e h => SectionRank.catalog_of_mulEquiv e h) hKP (centralizer (K : Set G))) _
  obtain ⟨Ē, hĒC, hĒel, hĒ4⟩ := h3.exists_four_le_centralizer_oddQuotImageC hKL
  have hH : RankTwoHyp (u3G₁Bar K) Xb := ⟨hKP₁, hstd, hnn, two_le_pRank_of_le hĒC hĒel hĒ4⟩
  have hO : standardComponentOddCore (u3G₁Bar K) = ⊥ := standardComponentOddCore_quot_eq_bot
  obtain ⟨hA5, hodd⟩ := oddQuotImageC_facts_four h3 e hKL hKo hKH
  have hT₀2 : IsPGroup 2 ((T ⊓ centralizer (L : Set G)).subgroupOf (centralizer (K : Set G))) :=
    (h3.sylow.isPGroup.to_le inf_le_left).comap_subtype
  obtain ⟨Rb, hR, hTR⟩ :=
    AS76b.exists_isSylowOf_le oddQuotImageC_T₀_le_centralizer (hT₀2.map (QuotientGroup.mk' _))
  have hno : ∀ x : u3G₁Bar K, ¬ rightConjugate Rb x ≤ Xb := by
    intro x hx
    obtain ⟨E, hET, -, hE4⟩ := h3.exists_four_le
    have hE1 : E ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hE4
      exact absurd hE4 (by norm_num)
    obtain ⟨⟨t, htE⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hE1
    have ht := hET htE
    have hmem : QuotientGroup.mk' _ (⟨t, T₀_le_centralizer_K hKL ht⟩ : centralizer (K : Set G))
        ∈ Rb := hTR ⟨⟨t, T₀_le_centralizer_K hKL ht⟩, ht, rfl⟩
    refine not_conj_mem_oddQuotImageC_four h3 hF e hKL hKo hKH ht
      (fun h => ht1 (Subtype.ext h)) x⁻¹ (hx ?_)
    have e1 : ∀ y : u3G₁Bar K, x * (x⁻¹ * y * x⁻¹⁻¹) * x⁻¹ = y := fun y => by group
    rw [mem_rightConjugate_iff, e1]
    exact hmem
  obtain ⟨g, T', V₀, hset⟩ :=
    exists_setting310_sup hF.lemma32 hF.lemma33Two hcfg hH hO hA5 hodd hR hno
  have hR4 : Nat.card Rb = 4 := by
    rw [← hset.cardR]
    exact (Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : Rb ≤ rankTwoX Xb ⊔ Rb)).toEquiv).symm
  have hT4 : 4 ≤ Nat.card (oddQuotImageC K (T ⊓ centralizer (L : Set G))) := by
    obtain ⟨E, hET, -, hE4⟩ := h3.exists_four_le
    rw [card_map_mk_of_isPGroup hT₀2, ← hE4,
      Nat.card_congr (subgroupOfEquivOfLe (T₀_le_centralizer_K hKL)).toEquiv]
    exact Subgroup.card_le_of_le hET
  have hRT := eq_of_le_of_card_ge hTR (by rw [hR4]; exact hT4)
  subst hRT
  have hXH : Xb ≤ rankTwoX Xb ⊔ oddQuotImageC K (T ⊓ centralizer (L : Set G)) :=
    (le_normalClosure : Xb ≤ rankTwoX Xb).trans le_sup_left
  have hTH : oddQuotImageC K (T ⊓ centralizer (L : Set G)) ≤
      rankTwoX Xb ⊔ oddQuotImageC K (T ⊓ centralizer (L : Set G)) := le_sup_right
  exact (em _).elim (false_of_setting310_IIb_four h3 hF e hKL hKo hKH hIIb hXH hTH hset)
    (false_of_setting310_IIa_four h3 hF e hKL hKo hKH hGold hXH hTH hset)

end Sec3

theorem gms6U3Four_of
    (hF : Foundation) (hcfg : AS76b.Section3Config)
    (hGold : Asc76X.GoldschmidtTheoremA) (hT : GMS61TightC) (hC : GMS61CaseOneC)
    (hIIb : RankTwoAltFive.Asc310IIb) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
      standardComponentOddCore G = ⊥ →
        Assembly.LowTwoRank.StatedClassicalModel (rankTwoQuot A) .PSU 3 2 2 → False := by
  intro G _ _ L hA hO hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : BenderHyp G L :=
    ⟨hA.standard, hO, hA.not_normal, hA.rank, Or.inr (Or.inl ⟨2, le_rfl, hs⟩)⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_psu3_of_stated le_rfl hs
  obtain ⟨T, hTs⟩ := exists_isSylowOf 2 (normalizer (L : Set G))
  have h3 : Sec3 G L T := ⟨hB, hTs⟩
  have hZ : Odd (Nat.card (center L)) := odd_card_center_of_psu3 hB.standard.1.1 le_rfl e
  obtain ⟨K, hKL, hKo, hKH, -⟩ := exists_u3TorusK hZ le_rfl e h3.isSylowOf_T₁
  obtain ⟨hstd, hnn⟩ := gms61InductionC_of gms61QuasisimpleC hT (gms61NotNormalC hF) hC
    G L T K 2 le_rfl ⟨e⟩ h3 hKL hKo hKH
  exact h3.false_of_four_of_standard hF hcfg hGold hIIb hA.kProper e hKL hKo hKH hstd hnn

end CFSG.ComponentClassification.GMS78
