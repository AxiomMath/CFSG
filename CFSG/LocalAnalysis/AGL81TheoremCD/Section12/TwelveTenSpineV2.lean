module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenSpine
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveNineW
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenFinalBProof

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

structure TwelveTenSpineV2 (M : Subgroup G) (p : ℕ) (Q H : Subgroup G) : Prop where
  h41 : ∀ d : ℕ, d ∈ sigmaSet G M → ¬ d ∣ Nat.card (H ⊓ M : Subgroup G)
  h1015 : TenFifteenSigma M H
  hmdL : ∀ d : ℕ, d ∈ sigmaSet G M → ∀ L : Subgroup G, L ∈ weakBlockSet M H →
    CFSG.Open.pRank d L ≤ 1
  hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
    ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L)
  h126 : ∀ (d : ℕ) (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ),
    TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃ → TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃

theorem exists_twelveFiveData {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (h125 : ∀ d : ℕ, d ∈ sigmaSet G M → TwelveFive M H d) :
    ∃ (d : ℕ) (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ),
      TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃ := by
  obtain ⟨d, hdσ⟩ := h.sigma_nonempty
  obtain ⟨hJ, L₁, L₂, L₃, hL₁, hL₂, hL₃, hjoin, ⟨n₁, hodd₁, htype₁⟩,
    ⟨n₂, hodd₂, htype₂⟩, ⟨n₃, hodd₃, htype₃⟩⟩ := h125 d hdσ
  exact ⟨d, L₁, L₂, L₃, n₁, n₂, n₃,
    ⟨hdσ, hJ, hL₁, hL₂, hL₃, hjoin, htype₁, htype₂, htype₃, hodd₁, hodd₂, hodd₃⟩⟩

theorem twelveTenSpine_of_v2_core {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (h3 : CFSG.Open.pRank 3 M ≤ 3)
    (hcard : (weakBlockSet M H).ncard = 3)
    (h125 : ∀ d : ℕ, d ∈ sigmaSet G M → TwelveFive M H d)
    (hv : TwelveTenSpineV2 M p Q H) : TwelveTenSpine M p Q H := by
  obtain ⟨d, L₁, L₂, L₃, n₁, n₂, n₃, hd⟩ := exists_twelveFiveData h h125
  have h6 := hv.h126 d L₁ L₂ L₃ n₁ n₂ n₃ hd
  exact
    { h41 := hv.h41
      h1015 := hv.h1015
      hmdL := hv.hmdL
      hL3 := hv.hL3
      hn1 := fun d' L₁' L₂' L₃' n₁' n₂' n₃' hd' =>
        ⟨TwelveSix.n₁_eq_one hd' (hv.h126 d' L₁' L₂' L₃' n₁' n₂' n₃' hd'),
          TwelveSix.n₂_eq_one hd' (hv.h126 d' L₁' L₂' L₃' n₁' n₂' n₃' hd'),
          TwelveSix.n₃_eq_one hd' (hv.h126 d' L₁' L₂' L₃' n₁' n₂' n₃' hd')⟩
      hSevenA := (twelveSevenData h hd h6 h3 hcard).2.2.2.2
      hNineW := hNineW_of_twelveSix h hd h6 h3 hcard
      hfinalB := twelveTenFinalB'_of_twelveSix h hd h6 h3 hcard }

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
