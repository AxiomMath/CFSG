module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFive
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.JSubNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.RankTools
import CFSG.GroupTheory.PRankCommutingSup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFBar
import CFSG.RankThree.PartTwo.Sec19.Item194Proof
public import CFSG.GroupTheory.SylowNormalIndex
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagGroup
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFour
import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
import CFSG.Quasithin.SteinbergBKHigherElementaryThompson

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

private theorem barM_isL3TwoPow {M L : Subgroup G} {n : ℕ}
    (hL : IsTwoPrimeComponent M L)
    (hL3 : IsL3TwoPow n (↥L ⧸ CFSG.pCore 2 ↥L)) :
    IsL3TwoPow n (barM M L) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec19.Item194Proof.nonempty_barM_mulEquiv
    hL.le hL.inf_twoCore
  obtain ⟨e3⟩ := hL3
  exact ⟨e.symm.trans e3⟩

private theorem center_barM_eq_bot {M L : Subgroup G} {n : ℕ}
    (hL : IsTwoPrimeComponent M L)
    (hL3 : IsL3TwoPow n (↥L ⧸ CFSG.pCore 2 ↥L)) :
    Subgroup.center ↥(barM M L) = ⊥ := by
  haveI : IsSimpleGroup (barM M L) := (barM_isL3TwoPow hL hL3).isSimpleGroup
  haveI : Group.IsPerfect (barM M L) := ⟨hL.component.2.2.1⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (barM M L)) with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.mp h)
      (Group.IsPerfect.not_isMulCommutative (G := barM M L))

private theorem barM_sSup_finset {M : Subgroup G} (S : Finset (Subgroup G))
    (hS : ∀ L ∈ S, L ≤ M) :
    barM M (sSup (S : Set (Subgroup G))) = ⨆ L ∈ S, barM M L := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [barM]
  | insert L S hLS ih =>
      rw [Finset.coe_insert, sSup_insert, Finset.iSup_insert]
      rw [barM_sup (hS L (Finset.mem_insert_self L S))
        (sSup_le fun K hK => hS K (Finset.mem_insert_of_mem hK))]
      rw [ih fun K hK => hS K (Finset.mem_insert_of_mem hK)]

theorem pRank_sSup_le_sum_of_center {M H : Subgroup G} {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (S : Finset (Subgroup G)) (hS : ∀ L ∈ S, L ∈ weakBlockSet M H)
    (hZ : ∀ L ∈ S, ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L))) :
    CFSG.Open.pRank d (sSup (S : Set (Subgroup G))) ≤ ∑ L ∈ S, CFSG.Open.pRank d L := by
  classical
  have hSM : ∀ L ∈ S, L ≤ M := fun L hL => (hS L hL).le
  have hZ' : ∀ L ∈ S, ¬ d ∣ Nat.card ↥(barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := by
    intro L hL
    rw [← CFSG.center_map_subtype_eq_inf_centralizer,
      Subgroup.card_map_of_injective (barM M L).subtype_injective]
    exact hZ L hL
  have hcomm : ∀ L ∈ S, ∀ K ∈ S, L ≠ K →
      barM M L ≤ Subgroup.centralizer (barM M K : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro L hL K hK hLK
    have hL2 : IsTwoPrimeComponent M L := (hS L hL).toIsTwoPrimeComponent
    have hK2 : IsTwoPrimeComponent M K := (hS K hK).toIsTwoPrimeComponent
    have hne : barM M L ≠ barM M K := fun he => hLK (hL2.eq_of_barM_eq hK2 he)
    have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
      hL2.component hK2.component hne
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc
  have hrank : CFSG.Open.pRank d (⨆ L ∈ S, barM M L) =
      ∑ L ∈ S, CFSG.Open.pRank d (barM M L) :=
    CFSG.GroupTheory.pRank_iSup_eq_sum_of_commute_of_not_dvd
      (p := d) (s := S) (J := fun L => barM M L) hd hcomm hZ'
  have h1 : CFSG.Open.pRank d (sSup (S : Set (Subgroup G))) =
      CFSG.Open.pRank d (barM M (sSup (S : Set (Subgroup G)))) :=
    (pRank_barM_eq hd hd2 M (sSup (S : Set (Subgroup G))) (sSup_le hSM)).symm
  have h2 : CFSG.Open.pRank d (barM M (sSup (S : Set (Subgroup G)))) =
      CFSG.Open.pRank d (⨆ L ∈ S, barM M L) := by
    rw [barM_sSup_finset S hSM]
  refine ((h1.trans h2).trans ?_).le
  rw [hrank]
  exact Finset.sum_congr rfl fun L hL => pRank_barM_eq hd hd2 M L (hSM L hL)

theorem pRank_sSup_le_sum {M H : Subgroup G} {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L))
    (S : Finset (Subgroup G)) (hS : ∀ L ∈ S, L ∈ weakBlockSet M H) :
    CFSG.Open.pRank d (sSup (S : Set (Subgroup G))) ≤ ∑ L ∈ S, CFSG.Open.pRank d L := by
  refine pRank_sSup_le_sum_of_center hd hd2 S hS ?_
  intro L hL
  obtain ⟨n, -, hL3n⟩ := hL3 L (hS L hL)
  rw [center_barM_eq_bot (hS L hL).toIsTwoPrimeComponent hL3n, Subgroup.card_bot]
  exact hd.not_dvd_one

theorem hdr_of_blocks {M H : Subgroup G}
    (hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L))
    (hmdL : ∀ d : ℕ, d ∈ sigmaSet G M → ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      CFSG.Open.pRank d L ≤ 1) :
    ∀ d : ℕ, d ∈ sigmaSet G M → CFSG.Open.pRank d (jSub M H) ≤ (weakBlockSet M H).ncard := by
  intro d hd
  classical
  letI : Fintype (Subgroup G) := Fintype.ofFinite _
  let T : Finset (Subgroup G) := (weakBlockSet M H).toFinset
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hd2 : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
  have hT : ∀ L ∈ T, L ∈ weakBlockSet M H := fun L hL => Set.mem_toFinset.mp hL
  have hJ : jSub M H = sSup (T : Set (Subgroup G)) := by
    rw [jSub, show (T : Set (Subgroup G)) = weakBlockSet M H from Set.coe_toFinset _]
  have hle := pRank_sSup_le_sum hdp hd2 hL3 T hT
  have hsum_le : ∑ L ∈ T, CFSG.Open.pRank d L ≤ T.card := by
    calc ∑ L ∈ T, CFSG.Open.pRank d L ≤ ∑ L ∈ T, 1 :=
          Finset.sum_le_sum fun L hL => hmdL d hd L (hT L hL)
      _ = T.card := by simp
  have hcard : T.card = (weakBlockSet M H).ncard := by
    rw [← Set.ncard_coe_finset T,
      show (T : Set (Subgroup G)) = weakBlockSet M H from Set.coe_toFinset _]
  rw [hJ]
  exact hle.trans (hsum_le.trans (le_of_eq hcard))

private theorem pRank_eq_one_of_mem_weakBlockSet {M H : Subgroup G} {d : ℕ}
    (hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L))
    (hmdL : ∀ d : ℕ, d ∈ sigmaSet G M → ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      CFSG.Open.pRank d L ≤ 1)
    (hm3 : CFSG.Open.pRank 3 M ≤ 3)
    (hr3 : (weakBlockSet M H).ncard ≤ CFSG.Open.pRank 3 (jSub M H))
    (hd3 : ∀ d : ℕ, d ∈ sigmaSet G M → 3 ≤ CFSG.Open.pRank d (jSub M H))
    (hd : d ∈ sigmaSet G M) {L : Subgroup G} (hL : L ∈ weakBlockSet M H) :
    CFSG.Open.pRank d L = 1 := by
  classical
  letI : Fintype (Subgroup G) := Fintype.ofFinite _
  let T : Finset (Subgroup G) := (weakBlockSet M H).toFinset
  have hT : ∀ K ∈ T, K ∈ weakBlockSet M H := fun K hK => Set.mem_toFinset.mp hK
  have hJ : jSub M H = sSup (T : Set (Subgroup G)) := by
    rw [jSub, show (T : Set (Subgroup G)) = weakBlockSet M H from Set.coe_toFinset _]
  have hle := pRank_sSup_le_sum
    (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1)
    (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1) hL3 T hT
  have hle1 : ∀ K ∈ T, CFSG.Open.pRank d K ≤ 1 := fun K hK => hmdL d hd K (hT K hK)
  have hcard3 : T.card ≤ 3 := by
    calc T.card = (weakBlockSet M H).ncard := by
          rw [← Set.ncard_coe_finset T,
            show (T : Set (Subgroup G)) = weakBlockSet M H from Set.coe_toFinset _]
      _ ≤ CFSG.Open.pRank 3 (jSub M H) := hr3
      _ ≤ CFSG.Open.pRank 3 M :=
          CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) (jSub_le M H)
      _ ≤ 3 := hm3
  have hsum_le_card : ∑ K ∈ T, CFSG.Open.pRank d K ≤ T.card := by
    calc ∑ K ∈ T, CFSG.Open.pRank d K ≤ ∑ K ∈ T, 1 := Finset.sum_le_sum hle1
      _ = T.card := by simp
  have hsum3 : ∑ K ∈ T, CFSG.Open.pRank d K = 3 := by
    have h1 : 3 ≤ CFSG.Open.pRank d (jSub M H) := hd3 d hd
    have h2 : CFSG.Open.pRank d (jSub M H) ≤ ∑ K ∈ T, CFSG.Open.pRank d K := by
      rw [hJ]
      exact hle
    omega
  have hterm : ∀ K ∈ T, CFSG.Open.pRank d K = 1 := by
    refine (Finset.sum_eq_sum_iff_of_le hle1).mp ?_
    rw [hsum3]
    have hcard_eq : T.card = 3 := by omega
    simp [hcard_eq]
  exact hterm L (Set.mem_toFinset.mpr hL)

theorem hdvdL_of_blocks {M H : Subgroup G}
    (hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L))
    (hmdL : ∀ d : ℕ, d ∈ sigmaSet G M → ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      CFSG.Open.pRank d L ≤ 1)
    (hm3 : CFSG.Open.pRank 3 M ≤ 3)
    (hr3 : (weakBlockSet M H).ncard ≤ CFSG.Open.pRank 3 (jSub M H))
    (hd3 : ∀ d : ℕ, d ∈ sigmaSet G M → 3 ≤ CFSG.Open.pRank d (jSub M H)) :
    ∀ d : ℕ, d ∈ sigmaSet G M → ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      d ∣ Nat.card L := by
  intro d hd L hL
  have hterm := pRank_eq_one_of_mem_weakBlockSet hL3 hmdL hm3 hr3 hd3 hd hL
  have hpos : 0 < CFSG.Open.pRank d L := by
    rw [hterm]
    norm_num
  have hpos' : 0 < CFSG.Open.pRank d (⊤ : Subgroup ↥L) := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := d) L]
  have hdvd : d ∣ Nat.card ↥L :=
    CFSG.RankThreeCoreUniqueness.Helpers.prime_dvd_card_of_pRank_pos d (⊤ : Subgroup ↥L) hpos'
  simpa using hdvd

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
