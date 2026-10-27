module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup
public import CFSG.GroupTheory.SylowIntersectionControl.PairSelection
public import CFSG.GroupTheory.SylowIntersectionControl.GomiHyp43
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Ω : Type} [Group Ω] [Finite Ω]

@[expose] def GomiThm45At (c : GNPairChoice Ω) (G : Subgroup Ω) : Prop :=
  GomiHyp43 G → ¬ c.selection.IsRegular G → ∀ S : Subgroup Ω, IsSylowTwoOf S G →
    ∃ X : Subgroup Ω, IsGomiSingularSubgroup G S X

structure GomiThm45Counterexample (c : GNPairChoice Ω) (G S : Subgroup Ω) : Prop where
  hyp43 : GomiHyp43 G
  not_isRegular : ¬ c.selection.IsRegular G
  isSylowTwoOf : IsSylowTwoOf S G
  not_isGomiSingularSubgroup : ∀ X : Subgroup Ω, ¬ IsGomiSingularSubgroup G S X
  minimal : ∀ H : Subgroup Ω, H < G → GomiThm45At c H

theorem exists_gomiThm45Counterexample (c : GNPairChoice Ω) {G : Subgroup Ω}
    (h : ¬ GomiThm45At c G) : ∃ G' S : Subgroup Ω, GomiThm45Counterexample c G' S := by
  obtain ⟨G', hG', hmin⟩ := wellFounded_lt.has_min {H | ¬ GomiThm45At c H} ⟨G, h⟩
  simp only [Set.mem_setOf_eq, GomiThm45At] at hG'
  push Not at hG'
  obtain ⟨hyp, hreg, S, hS, hX⟩ := hG'
  refine ⟨G', S, hyp, hreg, hS, hX, fun H hH => ?_⟩
  by_contra hH'
  exact hmin H hH' hH

omit [Finite Ω] in
theorem GomiHyp43.of_pCoreOf_le {G H : Subgroup Ω} (hG : GomiHyp43 G) (hHG : H ≤ G)
    (hQH : pCoreOf 2 G ≤ H) : GomiHyp43 H := by
  refine hG.mono hHG ?_ (CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hG.charTwo hHG hQH)
  have hQne : pCoreOf 2 G ≠ ⊥ := by
    intro hbot
    have hcent : Subgroup.centralizer ((⊥ : Subgroup Ω) : Set Ω) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.mpr (SetLike.coe_subset_coe.mpr bot_le)
    have hle : G ≤ ⊥ := by
      have hc : G ⊓ Subgroup.centralizer (pCoreOf 2 G : Set Ω) ≤ pCoreOf 2 G := hG.charTwo
      rw [hbot, hcent, inf_top_eq] at hc
      exact hc
    have hGbot : G = ⊥ := le_bot_iff.mp hle
    have hcard : Nat.card G = 1 := by rw [hGbot, Subgroup.card_bot]
    have heven : Even (Nat.card G) := hG.even
    rw [hcard] at heven
    exact Nat.not_even_one heven
  have htwo : 2 ∣ Nat.card (pCoreOf 2 G) := by
    rcases (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 G).card_eq_or_dvd with
      h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hQne
    · exact h
  exact even_iff_two_dvd.mpr (htwo.trans (Subgroup.card_dvd_of_le hQH))

end CFSG.GroupTheory
