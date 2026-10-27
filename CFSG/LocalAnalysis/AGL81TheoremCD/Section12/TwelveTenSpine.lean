module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenBridge
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankLower
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankUpper
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixReduced
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenFinalFromSeven
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.StrongEmbedInput

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

structure TwelveTenSpine (M : Subgroup G) (p : ℕ) (Q H : Subgroup G) : Prop where
  h41 : ∀ d : ℕ, d ∈ sigmaSet G M → ¬ d ∣ Nat.card (H ⊓ M : Subgroup G)
  h1015 : TenFifteenSigma M H
  hmdL : ∀ d : ℕ, d ∈ sigmaSet G M → ∀ L : Subgroup G, L ∈ weakBlockSet M H →
    CFSG.Open.pRank d L ≤ 1
  hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
    ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L)
  hn1 : ∀ (d : ℕ) (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ),
    TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃ → n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1
  hSevenA : TwelveSevenA M H Q
  hNineW : ∀ D : Subgroup G, IsThreeOnePlusTwo ↥D → D ≤ Q →
    ¬ kSub p M H ⊓ normalizer (D : Set G) ≤ M
  hfinalB : TwelveTenFinalB' M H Q p


theorem twelveFour_twelveFive_of_blocks {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H)
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h84 : CFSG.AGLEmbedding.Asc81bEightFour)
    (h41 : ∀ d : ℕ, d ∈ sigmaSet G M → ¬ d ∣ Nat.card (H ⊓ M : Subgroup G))
    (h1015 : TenFifteenSigma M H)
    (hmdL : ∀ d : ℕ, d ∈ sigmaSet G M → ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      CFSG.Open.pRank d L ≤ 1)
    (hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L)) :
    TwelveFour M H ∧ (∀ d : ℕ, d ∈ sigmaSet G M → TwelveFive M H d) ∧
      (weakBlockSet M H).ncard = 3 := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have h124 : TwelveFour M H :=
    twelveFour_of_weakBlock h41 (exists_mem_weakBlockSet_three_dvd h1 h2 h25 h84 h)
  have hr3 := hr3_of_hL3 hL3
  have hd3 := hd3_of_tenFifteenSigma h h124 h1015
  have hdvdL := hdvdL_of_blocks hL3 hmdL (pRank_three_le_three_of_twelveCtx h h124) hr3 hd3
  refine ⟨h124, fun d hd => twelveFive_of_twelveCtx_of_tenFifteen h
    (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1) hd h124 h1015 (hdvdL d hd) hr3
    (hdr_of_blocks hL3 hmdL d hd) hL3, ?_⟩
  obtain ⟨d, hdσ⟩ := h.sigma_nonempty
  exact ncard_weakBlockSet_eq_three_of_rank_count (pRank_three_le_three_of_twelveCtx h h124) hr3
    (hdr_of_blocks hL3 hmdL d hdσ) (hd3 d hdσ)

theorem h4StarFam_contra_spine {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H)
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h84 : CFSG.AGLEmbedding.Asc81bEightFour)
    (hs : TwelveTenSpine M p Q H) : False := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨L, hL⟩ := weakBlockSet_nonempty h1 h2 h25 h84 h
  have hns : ¬ Group.IsSolvable M := not_isSolvable_of_mem_weakBlockSet hL
  obtain ⟨h124, h125, -⟩ :=
    twelveFour_twelveFive_of_blocks h h1 h2 h25 h84 hs.h41 hs.h1015 hs.hmdL hs.hL3
  obtain ⟨d, hdσ⟩ := h.sigma_nonempty
  obtain ⟨hJ, L₁, L₂, L₃, hL₁, hL₂, hL₃, hjoin, ⟨n₁, hodd₁, htype₁⟩,
    ⟨n₂, hodd₂, htype₂⟩, ⟨n₃, hodd₃, htype₃⟩⟩ := h125 d hdσ
  have hdata : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃ :=
    ⟨hdσ, hJ, hL₁, hL₂, hL₃, hjoin, htype₁, htype₂, htype₃, hodd₁, hodd₂, hodd₃⟩
  obtain ⟨e₁, e₂, e₃⟩ := hs.hn1 d L₁ L₂ L₃ n₁ n₂ n₃ hdata
  have hσ7 : sigmaSet G M = {7} :=
    twelveSix_part_three_of_odd_prime_divisors h124 h.sigma_nonempty
      (fun q hq => (h125 q hq).1) (odd_prime_divisors_of_n_eq_one hdata e₁ e₂ e₃)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hstr7 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 M :=
    isStronglyPEmbedded_of_twelveCtx' h hns 7 (by rw [hσ7]; exact Set.mem_singleton 7)
  obtain ⟨D, hD, hDQ, h7⟩ := twelveTenFinalStep_of_twelveSevenA h hs.hSevenA hs.hfinalB
  obtain ⟨x, hxK, hxM⟩ := SetLike.not_le_iff_exists.mp (hs.hNineW D hD hDQ)
  exact hstr7.2.2 x hxM (h7 x hxK hxM)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
