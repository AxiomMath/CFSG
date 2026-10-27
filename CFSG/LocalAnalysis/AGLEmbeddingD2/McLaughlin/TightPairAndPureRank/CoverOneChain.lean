module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneParab

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding.BlockCyc CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.Open CFSG.HallHigman
open scoped commutatorElement

section Chain

variable {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y}
  {F : Type} [Field F] [Finite F] [CharP F 2]

theorem iSup_torus_le_rankOne {M : ℕ} (h : BorelQuotient D n H π M) {s : Fin D.rank}
    (hall : ∀ k, k ≠ s → Nat.card (rankOne D.rootGroup k) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup k, ∃ b ∈ rankOne D.rootGroup k, a * b ≠ b * a) :
    (⨆ k, H k : Subgroup K) ≤ rankOne D.rootGroup s := by
  refine iSup_le fun k => ?_
  by_cases hk : k = s
  · subst hk
    exact h.ct.H_le k
  · have : H k = ⊥ := by
      refine eq_bot_iff.2 fun t ht => Subgroup.mem_bot.2 ?_
      exact Lie.eq_one_of_central_of_card_six (hall k hk).1 (hall k hk).2 (h.ct.H_le k ht)
        fun g hg => torus_centralizes_rankOne_of_card_six h (hall k hk).1 ht g hg
    rw [this]
    exact bot_le

theorem false_short_chain (h : BorelQuotient D n H π 3) (h4 : 4 ≤ Nat.card F) {s j₀ j₁ j₂ : Fin D.rank}
    (hs : HasTorusSL2 D H s F)
    (hall : ∀ k, k ≠ s → Nat.card (rankOne D.rootGroup k) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup k, ∃ b ∈ rankOne D.rootGroup k, a * b ≠ b * a)
    (h3₀ : HasOrderThree D j₀) (h3₁ : HasOrderThree D j₁) (h3₂ : HasOrderThree D j₂)
    (h3nc₂ : HasOrderThreeNC D j₂)
    (h0s : j₀ ≠ s) (h1s : j₁ ≠ s) (h2s : j₂ ≠ s) (h01 : j₀ ≠ j₁) (h02 : j₀ ≠ j₂)
    (hA01 : D.cartan j₀ j₁ = -1) (hA10 : D.cartan j₁ j₀ = -1) (hc02 : D.cartan j₀ j₂ = 0)
    (hc0s : D.cartan j₀ s = 0) (hc1s : D.cartan j₁ s = 0)
    (hperf : ⁅rankOne D.rootGroup j₀ ⊔ rankOne D.rootGroup j₁,
      rankOne D.rootGroup j₀ ⊔ rankOne D.rootGroup j₁⁆ =
        rankOne D.rootGroup j₀ ⊔ rankOne D.rootGroup j₁)
    {C₁ C₂ : Subgroup Y} (hC₁ : SolvFree C₁) (hC₂ : SolvFree C₂)
    (hcov : ∀ i, (rankOne D.rootGroup i).map π ≤ C₁ ∨ (rankOne D.rootGroup i).map π ≤ C₂) :
    False := by
  have hTL : (⨆ k, H k : Subgroup K) ≤ rankOne D.rootGroup s := iSup_torus_le_rankOne h hall
  have hVT : (rankOne D.rootGroup j₀ ⊔ rankOne D.rootGroup j₁) ⊓ (⨆ k, H k) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 ?_
    obtain ⟨hxV, hxT⟩ := hx
    have hcomm : ∀ x ∈ rankOne D.rootGroup j₀ ⊔ rankOne D.rootGroup j₁,
        ∀ c ∈ rankOne D.rootGroup s, x * c = c * x :=
      Lie.commute_sup_of (commutes_rankOne_of_cartan_eq_zero h.extras h0s hc0s)
        (commutes_rankOne_of_cartan_eq_zero h.extras h1s hc1s)
    exact hs.eq_one_of_central h4 (hTL hxT) fun g hg => hcomm x hxV g hg
  have key : ∀ (C C' : Subgroup Y), SolvFree C → SolvFree C' →
      (rankOne D.rootGroup s).map π ≤ C →
      (∀ i, (rankOne D.rootGroup i).map π ≤ C ∨ (rankOne D.rootGroup i).map π ≤ C') → False := by
    intro C C' hC hC' hsC hcov'
    have hother : ∀ j, j ≠ s → HasOrderThree D j →
        (rankOne D.rootGroup j).map π ≤ C' := by
      intro j hj hj3
      rcases hcov' j with hh | hh
      · exact (false_short_long h h4 hs hj3 (hall j hj) hC hsC hh).elim
      · exact hh
    have h0 := hother j₀ h0s h3₀
    have h1 := hother j₁ h1s h3₁
    have h2 := hother j₂ h2s h3₂
    obtain ⟨E, hE, hel, hcard⟩ := exists_E9_of_nodes h hc02 h02 h3₀ h3nc₂
    have hEC : E ≤ C' := hE.trans (sup_le h0 h2)
    have hVC : (rankOne D.rootGroup j₀ ⊔ rankOne D.rootGroup j₁).map π ≤ C' := by
      rw [Subgroup.map_sup]
      exact sup_le h0 h1
    exact not_isPSolvable_map_A2_torus h (hall j₀ h0s) (hall j₁ h1s) h3₀ h01 hA01 hA10 hVT
      hperf (hC' E _ hEC hVC hel hcard)
  rcases hcov s with hsC | hsC
  · exact key C₁ C₂ hC₁ hC₂ hsC hcov
  · exact key C₂ C₁ hC₂ hC₁ hsC fun i => (hcov i).symm

end Chain

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
