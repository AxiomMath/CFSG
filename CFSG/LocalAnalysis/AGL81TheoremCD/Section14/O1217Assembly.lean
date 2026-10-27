module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Quasi
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Lift
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217SigmaDefs

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76Basic
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.AGL81C
  CFSG.LocalAnalysis.RankThreeUC.S15

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {q p : ℕ} {E : Subgroup G}

private theorem le_relPPrimeCore_of_inf_sylow_eq_bot {H K Q : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal)
    (hQ : CFSG.ABGLocalTools.IsSylowOf q Q H) (hbot : Q ⊓ K = ⊥) :
    K ≤ CFSG.Open.relPPrimeCore q H := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hQK : CFSG.ABGLocalTools.IsSylowOf q (Q ⊓ K) K :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hQ hKH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn)
  have hnotdvdRel : ¬ q ∣ (Q ⊓ K).relIndex K :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hQK).2.2
  have hnotdvd : ¬ q ∣ Nat.card K := by
    intro hdvd
    apply hnotdvdRel
    have hmul := Subgroup.relIndex_mul_card (H := Q ⊓ K) (K := K)
    rw [inf_eq_left.mpr hQK.le, hbot, Subgroup.card_bot, mul_one] at hmul
    rw [hbot, hmul]
    exact hdvd
  exact le_sSup ⟨hKH, hKn, hq.coprime_iff_not_dvd.mpr hnotdvd⟩

private theorem Hyp1417.exists_normalizing_not_centralizing (h : Hyp1417 G M q p E)
    (h1 : NineFourTwoSigmaGen)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo)
    {A : Subgroup G} (hAE : A ≤ E) (hA : Nat.card A = p)
    (hH : ¬ Subgroup.normalizer (A : Set G) ≤ M) :
    ∃ b : G, b ∈ E ∧ b ∉ A ∧ orderOf b = p ∧
      b ∈ Subgroup.normalizer
        (AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) : Set G) ∧
      b ∉ Subgroup.centralizer
        (AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) : Set G) := by
  classical
  obtain ⟨_, _, s⟩ := h.exists_setting hAE hA hH
  haveI : Fact p.Prime := ⟨h.hp⟩
  haveI : IsMulCommutative ↥E := h.elem.1
  let HA : Subgroup G := Subgroup.normalizer (A : Set G)
  let K : Subgroup G := AGL81C.kSub q M HA
  have hKnorm : (K.subgroupOf HA).Normal := (s.kStructure h1).1
  have hKleN : HA ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (AGL81C.kSub_le q M HA)).mp hKnorm
  have hEHA : E ≤ HA := by
    have hEcentA : E ≤ Subgroup.centralizer (A : Set G) := by
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      simpa using mul_comm' (⟨a, hAE ha⟩ : E) ⟨e, he⟩
    exact hEcentA.trans (Subgroup.centralizer_le_normalizer (A : Set G))
  have hAne : A ≠ E := by
    intro hEq
    have hlt : Nat.card A < Nat.card E := by
      rw [hA, h.card, pow_two]
      calc p = p * 1 := (mul_one p).symm
        _ < p * p := Nat.mul_lt_mul_of_pos_left h.hp.one_lt (Nat.Prime.pos h.hp)
    rw [hEq] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨b, hbE, hbA⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hAE hAne)
  have hbo : orderOf b = p :=
    orderOf_eq_prime (by simpa using h.elem.2 b hbE) (by
      intro hb1
      exact hbA (hb1 ▸ A.one_mem))
  have hKinf : E ⊓ Subgroup.centralizer (K : Set G) = A :=
    h.inf_centralizer_kSub_eq h1 hNT hL34 hAE hA hH
  have hbC : b ∉ Subgroup.centralizer (K : Set G) := by
    intro hb
    have hmem : b ∈ E ⊓ Subgroup.centralizer (K : Set G) := Subgroup.mem_inf.mpr ⟨hbE, hb⟩
    rw [hKinf] at hmem
    exact hbA hmem
  exact ⟨b, hbE, hbA, hbo, hKleN (hEHA hbE), hbC⟩

theorem Hyp1417.false_of_dvd (h : Hyp1417 G M q p E)
    (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong) (h3 : NineTwelveOneSigmaThree)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo) (hK2 : KFactCentralLift)
    (hA6 : KFactAltSixCoreCentral)
    {A : Subgroup G} (hAE : A ≤ E) (hA : Nat.card A = p)
    (hH : ¬ Subgroup.normalizer (A : Set G) ≤ M)
    (hdvd : p ∣ Nat.card ↥(AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) ⊓
      CFSG.Open.relPPrimeCore q (Subgroup.normalizer (A : Set G)))) : False := by
  classical
  obtain ⟨Q, F, s⟩ := h.exists_setting hAE hA hH
  haveI : Fact p.Prime := ⟨h.hp⟩
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let HA : Subgroup G := Subgroup.normalizer (A : Set G)
  let K : Subgroup G := AGL81C.kSub q M HA
  let O : Subgroup G := CFSG.Open.relPPrimeCore q HA
  change p ∣ Nat.card ↥(K ⊓ O) at hdvd
  have hKq : CFSG.IsQuasisimple ↥K := s.isQuasisimple_kSub h1 h2 h3 hA6
  have hcenter : (Subgroup.center ↥K).map K.subtype = K ⊓ O := s.map_center_kSub h1 h2 h3 hA6
  have hlist : CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q
      (↥K ⧸ Subgroup.center ↥K) := s.nineFourListGroup_quot_center h1 h2 h3 hA6
  have hodd : Odd (Nat.card (Subgroup.center ↥K)) := s.odd_card_center_kSub h1 h2 h3 hA6
  have hnotdvd : ¬ q ∣ Nat.card (Subgroup.center ↥K) :=
    s.not_dvd_card_center_kSub h1 h2 h3 hA6
  have hcardZ : Nat.card (Subgroup.center ↥K) = Nat.card ↥(K ⊓ O) := by
    rw [← hcenter, Subgroup.card_map_of_injective K.subtype_injective]
  have hdvdZ : p ∣ Nat.card (Subgroup.center ↥K) := by
    rw [hcardZ]
    exact hdvd
  have hZle : (Subgroup.center ↥K).map K.subtype ≤ K ⊓ M := by
    rw [hcenter]
    exact inf_le_inf le_rfl s.nine.relPPrimeCore_le
  have hKnorm : (K.subgroupOf HA).Normal := (s.kStructure h1).1
  have hKleN : HA ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (AGL81C.kSub_le q M HA)).mp hKnorm
  have hKnotle : ¬ K ≤ M := s.kSub_not_le h1
  have hKlt : K ⊓ M < K := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    exact hKnotle (hEq ▸ inf_le_right)
  obtain ⟨b, hbE, hbA, hbo, hbN, hbC⟩ :=
    h.exists_normalizing_not_centralizing h1 hNT hL34 hAE hA hH
  have hSylowK : CFSG.ABGLocalTools.IsSylowOf q (Q ⊓ K) K :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer s.sylowH
      (AGL81C.kSub_le q M HA) hKleN
  have hSne : Q ⊓ K ≠ ⊥ := by
    intro hbot
    have hKleO : K ≤ O := le_relPPrimeCore_of_inf_sylow_eq_bot s.qPrime
      (AGL81C.kSub_le q M HA) hKnorm s.sylowH hbot
    exact hKnotle (hKleO.trans s.nine.relPPrimeCore_le)
  have hNle : Subgroup.normalizer (Q ⊓ K : Set G) ≤ M :=
    s.normalizer_le_of_isPGroup hSne hSylowK.isPGroup
      (inf_le_left.trans s.nine.Q_le_M)
  have hKNle : K ⊓ Subgroup.normalizer (Q ⊓ K : Set G) ≤ K ⊓ M :=
    le_inf inf_le_left (inf_le_right.trans hNle)
  have hcontra := hK2 q p s.qPrime s.q_ne_two h.hp h.hp2 h.hpq G K hKq hlist hodd
    hnotdvd hdvdZ b hbN hbo hbC (K ⊓ M) hKlt hZle ⟨Q ⊓ K, hSylowK, hKNle⟩
  have hKM : K ⊓ Subgroup.centralizer ({b} : Set G) ≤ M :=
    h.kSub_inf_centralizer_le h1 hNT hL34 hAE hA hH hbE hbA
  exact hcontra (le_inf inf_le_left hKM)

theorem Hyp1417.normalizer_le (h : Hyp1417 G M q p E)
    (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong) (h3 : NineTwelveOneSigmaThree)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo) (hK1 : KFactThreeEightFive) (hK2 : KFactCentralLift)
    (hA6 : KFactAltSixCoreCentral)
    {A : Subgroup G} (hAE : A ≤ E) (hA : Nat.card A = p) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  by_contra hH
  by_cases hdvd : p ∣ Nat.card ↥(AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) ⊓
      CFSG.Open.relPPrimeCore q (Subgroup.normalizer (A : Set G)))
  · exact h.false_of_dvd h1 h2 h3 hNT hL34 hK2 hA6 hAE hA hH hdvd
  · exact h.false_of_coprime h1 hNT hL34 hK1 hAE hA hH hdvd

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217

theorem O1217SigmaAt.of_inputs (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong)
    (h3 : NineTwelveOneSigmaThree)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo) (hK1 : KFactThreeEightFive) (hK2 : KFactCentralLift)
    (hA6 : KFactAltSixCoreCentral)
    {G : Type} [Group G] [Finite G] (hC : CStarGen G) {M : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (hne : (sigmaSet G M).Nonempty)
    (hst : ∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) :
    O1217SigmaAt G M := by
  intro q p hq hp hp2 E hEM hE hEcard hvdvd hrk
  have hqSet : q ∈ sigmaSet G M := by
    simpa only [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hq
  have hqPrime : q.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime q hq.1
  by_cases hpq : p = q
  · subst p
    haveI : Fact q.Prime := ⟨hqPrime⟩
    exact rankThreeGamma_self_le (hst q hqSet) hEM hE.isPGroup
  · haveI : Fact q.Prime := ⟨hqPrime⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have h : Hyp1417 G M q p E :=
      { cstar := hC, maxLocal := hM, sigma_ne := hne, strong := hst, hq := hq,
        hp := hp, hp2 := hp2, hpq := hpq, le := hEM, elem := hE, card := hEcard,
        dvd := hvdvd, rank := hrk }
    have hX : ∀ X : Subgroup G, X ≤ E → Nat.card X = p →
        1 < CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (X : Set G)) := by
      intro X hXE hXcard
      have := hrk X hXE hXcard
      omega
    have hN : ∀ X : Subgroup G, X ≤ E → Nat.card X = p →
        Subgroup.normalizer (X : Set G) ≤ M := fun X hXE hXcard =>
      h.normalizer_le h1 h2 h3 hNT hL34 hK1 hK2 hA6 hXE hXcard
    exact rankThreeGamma_le_of_forall_normalizer_le (p := q) (r := p)
      (hst q hqSet) hE hX hN

theorem o1217SigmaGen_of_inputs (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong)
    (h3 : NineTwelveOneSigmaThree)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo) (hK1 : KFactThreeEightFive) (hK2 : KFactCentralLift)
    (hA6 : KFactAltSixCoreCentral) : O1217SigmaGen :=
  fun G _ _ hC M hM hne hst =>
    O1217SigmaAt.of_inputs h1 h2 h3 hNT hL34 hK1 hK2 hA6 hC hM hne hst

theorem o1217Gen_of_inputs (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong)
    (h3 : NineTwelveOneSigmaThree)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo) (hK1 : KFactThreeEightFive) (hK2 : KFactCentralLift)
    (hA6 : KFactAltSixCoreCentral) : Section15.O1217Gen :=
  o1217Gen_of_o1217SigmaGen (o1217SigmaGen_of_inputs h1 h2 h3 hNT hL34 hK1 hK2 hA6)

theorem o1219SigmaGen_of_inputs (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong)
    (h3 : NineTwelveOneSigmaThree)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo) (hK1 : KFactThreeEightFive) (hK2 : KFactCentralLift)
    (hA6 : KFactAltSixCoreCentral) : Section15.O1219SigmaGen :=
  o1219SigmaGen_of_o1217SigmaGen (o1217SigmaGen_of_inputs h1 h2 h3 hNT hL34 hK1 hK2 hA6)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
