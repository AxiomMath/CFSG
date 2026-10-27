module

public import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteen
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenBridge
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankThree
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankTable
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankUpper

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

private theorem card_eq_three_of_ranks {ι : Type*} (T : Finset ι) (k m : ι → ℕ)
    (hk1 : ∀ i ∈ T, 1 ≤ k i) (hkr : ∀ i ∈ T, k i + T.card ≤ 4)
    (hm : ∀ i ∈ T, m i + 1 ≤ max 2 (k i)) (h3 : 3 ≤ ∑ i ∈ T, m i) :
    T.card = 3 ∧ ∀ i ∈ T, k i ≤ 1 := by
  have hne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hT
    rw [hT] at h3
    simp at h3
  have hle3 : T.card ≤ 3 := by
    obtain ⟨i, hi⟩ := hne
    have h1 := hk1 i hi
    have h2 := hkr i hi
    omega
  have hcard : T.card = 3 := by
    by_contra hne3
    have hlt : T.card < 3 := lt_of_le_of_ne hle3 hne3
    have hge1 : 1 ≤ T.card := Finset.card_pos.mpr hne
    have hcases : T.card = 1 ∨ T.card = 2 := by omega
    rcases hcases with h1c | h2c
    · have hm2 : ∀ i ∈ T, m i ≤ 2 := by
        intro i hi
        have h1 := hkr i hi
        have h2 := hm i hi
        have hk : k i ≤ 3 := by omega
        have hmax : max 2 (k i) ≤ 3 := max_le (by norm_num) hk
        omega
      have hsum : ∑ i ∈ T, m i ≤ 2 := by
        calc ∑ i ∈ T, m i ≤ ∑ i ∈ T, 2 := Finset.sum_le_sum hm2
          _ = T.card * 2 := by simp
          _ = 2 := by rw [h1c]
      omega
    · have hm1 : ∀ i ∈ T, m i ≤ 1 := by
        intro i hi
        have h1 := hkr i hi
        have h2 := hm i hi
        have hk : k i ≤ 2 := by omega
        have hmax : max 2 (k i) ≤ 2 := max_le (by norm_num) hk
        omega
      have hsum : ∑ i ∈ T, m i ≤ 2 := by
        calc ∑ i ∈ T, m i ≤ ∑ i ∈ T, 1 := Finset.sum_le_sum hm1
          _ = T.card := by simp
          _ = 2 := by rw [h2c]
      omega
  exact ⟨hcard, fun i hi => by
    have h := hkr i hi
    omega⟩

private theorem sigmaSet_prime_odd_five {M H : Subgroup G} (h124 : TwelveFour M H) {d : ℕ}
    (hd : d ∈ sigmaSet G M) : d.Prime ∧ d ≠ 2 ∧ 5 ≤ d := by
  have hp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hodd : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
  have h3 : 3 < d := (h124 d hd).2.1
  exact ⟨hp, hodd, hp.five_le_of_ne_two_of_ne_three hodd (by omega)⟩

private theorem not_dvd_card_inf_of_mem_weakBlockSet {M H L : Subgroup G} {d : ℕ}
    (h41 : ∀ q : ℕ, q ∈ sigmaSet G M → ¬ q ∣ Nat.card (H ⊓ M : Subgroup G))
    (hd : d ∈ sigmaSet G M) (hL : L ∈ weakBlockSet M H) :
    ¬ d ∣ Nat.card (L ⊓ H : Subgroup G) := by
  intro hdiv
  refine h41 d hd (hdiv.trans (Subgroup.card_dvd_of_le ?_))
  exact le_inf inf_le_right (inf_le_left.trans hL.le)


private theorem pRank_le_one_of_mem_sigmaSet
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (hN1 : CFSG.LocalAnalysis.AGL81I.Section4.AGL81FourNineteen)
    (h : TwelveCtx G M p Q H) (h124 : TwelveFour M H)
    (h41 : ∀ q : ℕ, q ∈ sigmaSet G M → ¬ q ∣ Nat.card (H ⊓ M : Subgroup G))
    (hk : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      CFSG.Open.pRank 3 (barM M L) ≤ 1)
    {d : ℕ} (hd : d ∈ sigmaSet G M) {L : Subgroup G} (hL : L ∈ weakBlockSet M H) :
    CFSG.Open.pRank d L ≤ 1 := by
  obtain ⟨hdp, hd2, hd5⟩ := sigmaSet_prime_odd_five h124 hd
  have hkL : CFSG.Open.pRank 3 (barM M L) ≤ 1 := hk L hL
  have h3L : CFSG.Open.pRank 3 (barM M L) ≤ 3 := hkL.trans (by norm_num)
  have hb := (pRank_barM_add_one_le_of_mem_weakBlockSet h1 h2 h25 hN1 h hL h3L hdp hd5
    (not_dvd_card_inf_of_mem_weakBlockSet h41 hd hL)).1
  have hmax : max 2 (CFSG.Open.pRank 3 (barM M L)) ≤ 2 :=
    max_le (by norm_num) (by omega)
  have hbar : CFSG.Open.pRank d (barM M L) = CFSG.Open.pRank d L :=
    pRank_barM_eq hdp hd2 M L hL.le
  have hle : CFSG.Open.pRank d (barM M L) ≤ 1 := by omega
  simpa [hbar] using hle

private theorem card_three_and_three_rank
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h84 : CFSG.AGLEmbedding.Asc81bEightFour)
    (hN1 : CFSG.LocalAnalysis.AGL81I.Section4.AGL81FourNineteen)
    (h : TwelveCtx G M p Q H) (h124 : TwelveFour M H)
    (h41 : ∀ q : ℕ, q ∈ sigmaSet G M → ¬ q ∣ Nat.card (H ⊓ M : Subgroup G))
    (h1015 : TenFifteenSigma M H) {d₀ : ℕ} (hd₀ : d₀ ∈ sigmaSet G M) :
    (weakBlockSet M H).ncard = 3 ∧
      ∀ L : Subgroup G, L ∈ weakBlockSet M H → CFSG.Open.pRank 3 (barM M L) ≤ 1 := by
  classical
  have hm3 : CFSG.Open.pRank 3 M ≤ 3 := pRank_three_le_three_of_twelveCtx h h124
  have hd3 : ∀ d ∈ sigmaSet G M, 3 ≤ CFSG.Open.pRank d (jSub M H) :=
    hd3_of_tenFifteenSigma h h124 h1015
  obtain ⟨hdp, hd2, hd5⟩ := sigmaSet_prime_odd_five h124 hd₀
  let : Fintype (Subgroup G) := Fintype.ofFinite _
  let T : Finset (Subgroup G) := (weakBlockSet M H).toFinset
  have hT : ∀ L ∈ T, L ∈ weakBlockSet M H := fun L hL => Set.mem_toFinset.mp hL
  have hJ : jSub M H = sSup (T : Set (Subgroup G)) := by
    rw [jSub, show (T : Set (Subgroup G)) = weakBlockSet M H from Set.coe_toFinset _]
  have hcard : T.card = (weakBlockSet M H).ncard := by
    rw [← Set.ncard_coe_finset T,
      show (T : Set (Subgroup G)) = weakBlockSet M H from Set.coe_toFinset _]
  have hnpos : 1 ≤ (weakBlockSet M H).ncard := by
    obtain ⟨L₀, hL₀, -⟩ := exists_mem_weakBlockSet_three_dvd h1 h2 h25 h84 h
    have hpos := (Set.ncard_pos (Set.toFinite (weakBlockSet M H))).2 ⟨L₀, hL₀⟩
    omega
  have h3L : ∀ L ∈ T, CFSG.Open.pRank 3 (barM M L) ≤ 3 := by
    intro L hL
    have h := pRank_three_barM_add_ncard_le h1 h2 h25 h (hT L hL)
    omega
  have hZ : ∀ L ∈ T, ¬ d₀ ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
    intro L hL
    exact (pRank_barM_add_one_le_of_mem_weakBlockSet h1 h2 h25 hN1 h (hT L hL)
      (h3L L hL) hdp hd5 (not_dvd_card_inf_of_mem_weakBlockSet h41 hd₀ (hT L hL))).2
  have hle : CFSG.Open.pRank d₀ (jSub M H) ≤ ∑ L ∈ T, CFSG.Open.pRank d₀ L := by
    rw [hJ]
    exact pRank_sSup_le_sum_of_center hdp hd2 T hT hZ
  have hsum : 3 ≤ ∑ L ∈ T, CFSG.Open.pRank d₀ L := (hd3 d₀ hd₀).trans hle
  have key := card_eq_three_of_ranks T (fun L => CFSG.Open.pRank 3 (barM M L))
    (fun L => CFSG.Open.pRank d₀ L)
    (fun L hL => one_le_pRank_three_barM h1 h2 h25 h (hT L hL))
    (fun L hL => by
      have h := pRank_three_barM_add_ncard_le h1 h2 h25 h (hT L hL)
      omega)
    (fun L hL => by
      have hb := (pRank_barM_add_one_le_of_mem_weakBlockSet h1 h2 h25 hN1 h (hT L hL)
        (h3L L hL) hdp hd5 (not_dvd_card_inf_of_mem_weakBlockSet h41 hd₀ (hT L hL))).1
      rwa [pRank_barM_eq hdp hd2 M L (hT L hL).le] at hb)
    hsum
  refine ⟨?_, ?_⟩
  · rw [← hcard]
    exact key.1
  · intro L hL
    exact key.2 L (Set.mem_toFinset.mpr hL)

theorem blockRank_count
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h84 : CFSG.AGLEmbedding.Asc81bEightFour)
    (hN1 : CFSG.LocalAnalysis.AGL81I.Section4.AGL81FourNineteen)
    (h : TwelveCtx G M p Q H)
    (h41 : ∀ d : ℕ, d ∈ sigmaSet G M → ¬ d ∣ Nat.card (H ⊓ M : Subgroup G))
    (h1015 : TenFifteenSigma M H) :
    (weakBlockSet M H).ncard = 3 ∧
      (∀ L : Subgroup G, L ∈ weakBlockSet M H → CFSG.Open.pRank 3 (barM M L) ≤ 1) ∧
      ∀ d : ℕ, d ∈ sigmaSet G M → ∀ L : Subgroup G, L ∈ weakBlockSet M H →
        CFSG.Open.pRank d L ≤ 1 := by
  have h124 : TwelveFour M H :=
    twelveFour_of_weakBlock h41 (exists_mem_weakBlockSet_three_dvd h1 h2 h25 h84 h)
  obtain ⟨d₀, hd₀⟩ := h.sigma_nonempty
  obtain ⟨hcard3, hk⟩ :=
    card_three_and_three_rank h1 h2 h25 h84 hN1 h h124 h41 h1015 hd₀
  exact ⟨hcard3, hk, fun d hd L hL =>
    pRank_le_one_of_mem_sigmaSet h1 h2 h25 hN1 h h124 h41 hk hd hL⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
