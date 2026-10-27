module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveLocal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Setup

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoClassical CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem oddCore_eq_bot_of {H : Subgroup G}
    (hO : ∀ N : Subgroup G, N ≤ H → H ≤ normalizer (N : Set G) → Odd (Nat.card N) → N = ⊥) :
    standardComponentOddCore H = ⊥ := by
  rw [standardComponentOddCore, sSup_eq_bot]
  rintro M ⟨hM, hodd⟩
  have hNH : H ≤ normalizer ((M.map H.subtype : Subgroup G) : Set G) := by
    intro h hh
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨⟨h, hh⟩ * m * (⟨h, hh⟩ : H)⁻¹, hM.conj_mem m hm _, ?_⟩
    simp [MulAut.conj_apply]
  have h := hO (M.map H.subtype) (map_subtype_le M) hNH
    (by rwa [card_map_of_injective H.subtype_injective])
  exact (map_eq_bot_iff_of_injective _ H.subtype_injective).mp h

theorem oddCore_sup_eq_bot {A R : Subgroup G}
    (hXF : rankTwoX A = CFSG.generalizedFitting G) (hXs : IsSimpleGroup ↥(rankTwoX A))
    (heven : Even (Nat.card A)) :
    standardComponentOddCore ↥(rankTwoX A ⊔ R) = ⊥ := by
  refine oddCore_eq_bot_of fun N hNH hHN hodd => ?_
  set X := rankTwoX A with hXdef
  have hXn : X.Normal := normalClosure_normal
  have hNX : N ⊓ X = ⊥ := by
    have hn : ((N ⊓ X).subgroupOf X).Normal := by
      constructor
      intro n hn x
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨hnN, hnX⟩ := mem_inf.mp hn
      refine mem_inf.mpr ⟨?_, ?_⟩
      · exact (mem_normalizer_iff.mp (hHN (le_sup_left (b := R) x.2)) _).mp hnN
      · simpa using X.mul_mem (X.mul_mem x.2 hnX) (X.inv_mem x.2)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ X).subgroupOf X) with h | h
    · rw [subgroupOf_eq_bot] at h
      exact le_bot_iff.mp fun n hn => h.le_bot ⟨hn, (mem_inf.mp hn).2⟩
    · exfalso
      have hXN : X ≤ N := fun x hx => (mem_inf.mp (subgroupOf_eq_top.mp h hx)).1
      have hAN : A ≤ N := (le_normalClosure).trans hXN
      exact Nat.not_even_iff_odd.mpr hodd
        (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp heven).trans (Subgroup.card_dvd_of_le hAN)))
  have hNC : N ≤ centralizer (X : Set G) := by
    intro n hn
    rw [mem_centralizer_iff]
    intro x hx
    have hc : n * x * n⁻¹ * x⁻¹ ∈ N ⊓ X := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : x * n⁻¹ * x⁻¹ ∈ N :=
          (mem_normalizer_iff.mp (hHN (le_sup_left (b := R) hx)) _).mp (inv_mem hn)
        simpa [mul_assoc] using mul_mem hn h1
      · exact mul_mem (hXn.conj_mem x hx n) (inv_mem hx)
    rw [hNX, mem_bot] at hc
    have h2 : n * x * n⁻¹ = x := by
      calc n * x * n⁻¹ = n * x * n⁻¹ * x⁻¹ * x := by group
        _ = x := by rw [hc, one_mul]
    calc x * n = n * x * n⁻¹ * n := by rw [h2]
      _ = n * x := by group
  have hNX' : N ≤ X := by
    rw [hXF] at hNC ⊢
    exact hNC.trans (CFSG.centralizer_generalizedFitting_le G)
  rw [eq_bot_iff, ← hNX]
  exact le_inf le_rfl hNX'

omit [Finite G] in
theorem mem_rightConjugate_subgroupOf {H R : Subgroup G} (x : ↥H) (r : ↥H) :
    r ∈ rightConjugate (R.subgroupOf H) x ↔ (r : G) ∈ rightConjugate R (x : G) := by
  rw [mem_rightConjugate_iff, mem_rightConjugate_iff, mem_subgroupOf]
  simp

theorem asc08Lemma310_of_local
    (hL : Asc08Lemma310Local) (h32 : Lemma32) (h332 : Lemma33Two) (hcfg : Section3Config) :
    Asc08Lemma310 := by
  intro G _ _ A hH hO hA5 hodd R hR hno
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hA5
  have hAperf : commutator ↥A = ⊤ := hH.standard.1.1
  have hZ : center ↥A = ⊥ := RankTwoAlt.center_eq_bot_of_odd_five hAperf e hodd
  let eA : ↥A ≃* A5 :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  have hA31 : Hyp31 A :=
    ⟨hH.standard, hypIIAlt5 ↥A hAperf ⟨e⟩, hO, by have := hH.rank; omega, hH.not_normal⟩
  have hstd := hH.standard
  obtain ⟨hXF, hXs⟩ := AS76b.asc08Lemma34 G A hA31
  have hXsimple : IsSimpleGroup ↥(rankTwoX A) := by
    rw [show rankTwoX A = CFSG.generalizedFitting G from hXF]
    exact hXs
  set H := rankTwoX A ⊔ R with hHdef
  have hAX : A ≤ rankTwoX A := le_normalClosure
  have hAG₁ : A ≤ H := hAX.trans le_sup_left
  have hRG₁ : R ≤ H := le_sup_right
  have hAc : Nat.card A = 60 := by rw [Nat.card_congr eA.toEquiv, card_A5]
  have hA1 : ∀ {B : Subgroup G}, A ≤ B → B = ⊥ → False := by
    intro B hAB hB1
    rw [hB1, le_bot_iff] at hAB
    apply hH.not_normal
    rw [hAB]
    infer_instance
  have heven : Even (Nat.card (centralizer (A : Set G) ⊓ H : Subgroup G)) := by
    have hR1 : R ≠ ⊥ :=
      AS76b.isSylowOf_ne_bot_of_even hR (AS76b.tightlyEmbedded_centralizer hstd).1
    have h2R : 2 ∣ Nat.card R := by
      rcases hR.isPGroup.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hR1
      · exact h
    exact even_iff_two_dvd.mpr (h2R.trans (Subgroup.card_dvd_of_le (le_inf hR.le hRG₁)))
  have hstd₁ := GMS78.standard_subgroupOf hstd hAG₁ heven
  have hnn : ¬ (A.subgroupOf H).Normal := by
    intro hn
    have hnX : (A.subgroupOf (rankTwoX A)).Normal := by
      constructor
      intro a ha x
      have h1 := hn.conj_mem ⟨(a : G), hAG₁ ha⟩ ha ⟨(x : G), le_sup_left (b := R) x.2⟩
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
          congrArg Subtype.val (hUc.1.is_comm.comm ⟨((x : ↥H) : G), x.2⟩ ⟨((y : ↥H) : G), y.2⟩)
      · rw [mem_subgroupOf] at hx
        exact Subtype.ext (by simpa using hUc.2 _ hx)
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hU4, ← rightConjugate_card U c]
      exact Nat.card_congr (subgroupOfEquivOfLe hEG₁).toEquiv
  have hH₁ : RankTwoHyp ↥H (A.subgroupOf H) :=
    ⟨LocalAnalysis.ComponentInitial.kProper_subgroup
      (fun e h => SectionRank.catalog_of_mulEquiv e h) hH.kProper _, hstd₁, hnn, hrank₁⟩
  let eA₁ : ↥(A.subgroupOf H) ≃* ↥A := subgroupOfEquivOfLe hAG₁
  have hO₁ : standardComponentOddCore ↥H = ⊥ :=
    oddCore_sup_eq_bot hXF hXsimple (by rw [hAc]; decide)
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
      have h1 : (x : G) * r * (x : G)⁻¹ ∈ H := hRG₁ ((mem_rightConjugate_iff _ _ _).mp hr)
      have h2 := H.mul_mem (H.mul_mem (H.inv_mem x.2) h1) x.2
      simpa [mul_assoc] using h2
    have h := hx ((mem_rightConjugate_subgroupOf x ⟨r, hrH⟩).mpr hr)
    exact mem_subgroupOf.mp h
  have hle : (rankTwoX (A.subgroupOf H)).map H.subtype ≤ rankTwoX A := by
    rw [map_le_iff_le_comap]
    have : ((rankTwoX A).comap H.subtype).Normal :=
      (normalClosure_normal (s := (A : Set G))).comap _
    exact normalClosure_le_normal fun a ha => hAX (mem_subgroupOf.mp ha)
  have hX₁ : (rankTwoX (A.subgroupOf H)).map H.subtype = rankTwoX A := by
    refine le_antisymm hle ?_
    have hnN : (((rankTwoX (A.subgroupOf H)).map H.subtype).subgroupOf (rankTwoX A)).Normal := by
      constructor
      intro n hn x
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨m, hm, hmn⟩ := hn
      have hx₁ : (x : G) ∈ H := le_sup_left (b := R) x.2
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
  let eX : ↥(rankTwoX (A.subgroupOf H)) ≃* ↥(rankTwoX A) :=
    ((rankTwoX (A.subgroupOf H)).equivMapOfInjective _ H.subtype_injective).trans
      (MulEquiv.subgroupCongr hX₁)
  have hA31₁ : Hyp31 (A.subgroupOf H) :=
    ⟨hstd₁, hypIIAlt5 _ hstd₁.1.1 ⟨e₁⟩, hO₁, by omega, hnn⟩
  obtain ⟨g, hg, T, hT, hTN, hTR⟩ := exists_sec3 hcfg hA31₁ hR₁
  have hloc := case310Local_of h32 h332 hA31₁ (eA₁.trans eA) hR₁ hno₁ hg hT hTN hTR
  have h1 := hL ↥H (A.subgroupOf H) hH₁ hO₁ ⟨e₁⟩ hodd₁ (R.subgroupOf H) hR₁ hno₁ hXR₁ g T _ hloc
  rcases h1 with ⟨⟨eJ⟩⟩ | ⟨⟨eM⟩, t, ht2, htA, htR, htout⟩
  · exact Or.inl ⟨eX.symm.trans eJ⟩
  refine Or.inr ⟨⟨eX.symm.trans eM⟩, t, by simpa using congrArg Subtype.val ht2, ?_, ?_, ?_⟩
  · rw [← subgroupOf_normalizer_eq hAG₁] at htA
    exact mem_subgroupOf.mp htA
  · rw [← subgroupOf_normalizer_eq hRG₁] at htR
    exact mem_subgroupOf.mp htR
  · rintro ⟨a, ha, hta⟩
    apply htout
    refine ⟨⟨a, hAG₁ ha⟩, ha, fun y hy => Subtype.ext ?_⟩
    simpa using hta y hy

end CFSG.ComponentClassification.RankTwoAltFive
