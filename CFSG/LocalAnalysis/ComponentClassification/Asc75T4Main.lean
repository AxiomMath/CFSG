module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Top
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Centralizer
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Thm5

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding

structure MainCounterexample (G : Type) [Group G] [Finite G] (Q : Subgroup G) : Prop where
  ih : Thm4BelowWeak (Nat.card G)
  tight : TightlyEmbedded Q
  four : HasFourGroup (twoPrimeLayerIn Q)
  not_case1 : ¬ Thm4Case1 Q
  not_case3 : ¬ Thm4Case3 Q

@[expose] def StepConjNormalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Q : Subgroup G), MainCounterexample G Q →
    MainSetting Q → NormalInConjNormalizer Q

@[expose] def StepEndgame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Q : Subgroup G), MainCounterexample G Q →
    MainSetting Q → linkedClass Q = {Q} → ¬ OddNormalizerOverlaps Q → False

@[expose] def StepRankOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Q : Subgroup G), Thm4Below (Nat.card G) →
    TightlyEmbedded Q → twoPrimeLayerIn Q ≠ oddCoreIn Q → ¬ HasFourGroup (twoPrimeLayerIn Q) →
    ¬ Thm4Case1 Q → ¬ Thm4Case3 Q → ¬ OddNormalizerOverlaps Q →
    (1 < CFSG.Open.pRank 2 Q → ∀ g : G, g ∉ normalizer (Q : Set G) →
      Even (Nat.card (rightConjugate Q g ⊓ normalizer (Q : Set G) : Subgroup G)) →
      ∃ S : Subgroup G, IsSylowOf 2 S (rightConjugate Q g) ∧ S ≤ normalizer (Q : Set G))

theorem false_of_mainCounterexample (h3 : AschbacherTheorem3.Theorem3Statement)
    (h5 : Theorem5Statement) (hN : StepConjNormalizer) (hE : StepEndgame) {G : Type} [Group G]
    [Finite G] {Q : Subgroup G} (hM : MainCounterexample G Q) (hodd : ¬ OddNormalizerOverlaps Q) :
    False := by
  have hNQ : normalizer (Q : Set G) ≠ ⊤ := fun h =>
    hM.not_case1 (normalIn_twoPrimeLayerIn_top_of_normal (normalizer_eq_top_iff.mp h))
  have hS := mainSetting_of_normalInCentralizers h3 hM.tight hNQ hM.four
    (noThm3Alt3_of_not_thm4Case3 hM.tight hM.not_case3)
    (normalInCentralizers_of_thm4BelowWeak h3 hM.ih hM.tight hM.four hM.not_case3)
  by_cases hND : normalizer (linkedLayer Q : Set G) = ⊤
  · exact hM.not_case1 (hS.thm4Case1_of_normalizer_eq_top hND)
  · exact hE G Q hM hS (hS.linkedClass_eq_singleton h5 (hN G Q hM hS) hND) hodd

theorem pRank_eq_one_of_not_hasFourGroup {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hK : twoPrimeLayerIn Q ≠ oddCoreIn Q) (h4 : ¬ HasFourGroup (twoPrimeLayerIn Q)) :
    CFSG.Open.pRank 2 (twoPrimeLayerIn Q) = 1 := by
  refine le_antisymm ?_ (one_le_pRank_of_even (even_card_twoPrimeLayerIn hK))
  by_contra hlt
  exact h4 (hasFourGroup_of_one_lt_pRank (by omega))

theorem asc75Theorem4_of_steps (h3 : AschbacherTheorem3.Theorem3Statement)
    (h5 : Theorem5Statement) (hN : StepConjNormalizer) (hE : StepEndgame) (hD : StepRankOne) :
    Asc75Theorem4 := by
  rw [asc75Theorem4_iff]
  suffices h : ∀ (n : ℕ) (G : Type) [Group G] [Finite G], Nat.card G = n →
      ∀ Q : Subgroup G, TightlyEmbedded Q → twoPrimeLayerIn Q ≠ oddCoreIn Q →
        Thm4Conclusion Q from
    fun G _ _ Q => h _ G rfl Q
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro G _ _ hn Q htight hK
  have ih : Thm4Below (Nat.card G) := fun H _ _ hH Q' h1 h2 =>
    ihn _ (hn ▸ hH) H rfl Q' h1 h2
  by_contra hcon
  have h1 : ¬ Thm4Case1 Q := fun h => hcon (Or.inl h)
  have h2 : ¬ Thm4Case2 Q := fun h => hcon (Or.inr (Or.inl h))
  have h3' : ¬ Thm4Case3 Q := fun h => hcon (Or.inr (Or.inr h))
  by_cases hodd : OddNormalizerOverlaps Q
  · rcases thm4Case1_or_thm4Case2_of_oddNormalizerOverlaps htight hK hodd with h | h
    · exact h1 h
    · exact h2 h
  by_cases h4 : HasFourGroup (twoPrimeLayerIn Q)
  · exact false_of_mainCounterexample h3 h5 hN hE ⟨ih.weak, htight, h4, h1, h3'⟩ hodd
  · exact h2 ⟨pRank_eq_one_of_not_hasFourGroup hK h4,
      hD G Q ih htight hK h4 h1 h3' hodd⟩

end CFSG.ComponentClassification.Asc75T4
