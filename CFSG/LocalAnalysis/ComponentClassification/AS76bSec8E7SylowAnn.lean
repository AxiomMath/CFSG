module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneAnnihilator
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivation
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowCertDefs

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open CFSG.Blueprint.Chevalley CFSG.SeitzReduction

theorem e7_oddDerivHeight_decodeVec_le :
    (Tag.E7.rootCertificate.roots.all fun c =>
      decide (oddDerivHeight (decodeVec c : Fin Tag.E7.rank → ℤ) ≤ 17)) = true := by
  decide +kernel


theorem e7AnnWalkB_sound {S L : List (Fin Tag.E7.rank → ℤ)} (cs : List ℕ) :
    ∀ W : List (Fin Tag.E7.rank → ℤ), e7AnnWalkB S L cs W = true → ∀ c ∈ cs,
      height (decodeVec c : Fin Tag.E7.rank → ℤ) ≤ 0 ∨
        (∃ γ ∈ L, CFSG.LieType.Ree.vecBEq γ (decodeVec c) = true) ∨
          ∃ δ ∈ S, annihIsRootB .E7 (decodeVec c + δ) = true := by
  have hpass : ∀ c : ℕ, (decide (oddDerivHeight (decodeVec c : Fin Tag.E7.rank → ℤ) ≤ 0) ||
      L.any fun γ => CFSG.LieType.Ree.vecBEq γ (decodeVec c)) = true →
      height (decodeVec c : Fin Tag.E7.rank → ℤ) ≤ 0 ∨
        (∃ γ ∈ L, CFSG.LieType.Ree.vecBEq γ (decodeVec c) = true) ∨
          ∃ δ ∈ S, annihIsRootB .E7 (decodeVec c + δ) = true := by
    intro c hcond
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hcond
    rcases hcond with hcond | hcond
    · exact Or.inl (by rwa [← oddDerivHeight_eq])
    · exact Or.inr (Or.inl hcond)
  induction cs with
  | nil => intro W _ c hc; exact absurd hc List.not_mem_nil
  | cons a cs ih =>
    intro W h c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · cases W with
      | nil =>
        rw [e7AnnWalkB] at h
        split at h
        · exact hpass c (by assumption)
        · exact absurd h Bool.false_ne_true
      | cons δ W' =>
        rw [e7AnnWalkB] at h
        split at h
        · exact hpass c (by assumption)
        · simp only [Bool.and_eq_true] at h
          exact Or.inr (Or.inr ⟨δ, mem_of_oddDerivMemB h.1.1,
            annihIsRootB_iff.2 (isRoot_of_oddDerivIsRootB h.1.2)⟩)
    · cases W with
      | nil =>
        rw [e7AnnWalkB] at h
        split at h
        · exact ih [] h c hc
        · exact absurd h Bool.false_ne_true
      | cons δ W' =>
        rw [e7AnnWalkB] at h
        split at h
        · exact ih _ h c hc
        · simp only [Bool.and_eq_true] at h
          exact ih W' h.2 c hc

theorem annListCheck_of_e7AnnB {S L W : List (Fin Tag.E7.rank → ℤ)} (h : e7AnnB S L W = true) :
    annListCheck .E7 17 S L = true := by
  simp only [e7AnnB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨hS, hL⟩, hW⟩, hLL⟩ := h
  have hwalk := e7AnnWalkB_sound _ W hW
  have hM := e7_oddDerivHeight_decodeVec_le
  simp only [List.all_eq_true, decide_eq_true_eq] at hM
  simp only [annListCheck, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.any_eq_true]
  refine ⟨⟨⟨⟨fun c hc => ?_, fun δ hδ => ?_⟩, fun γ hγ => ?_⟩, fun c hc => ?_⟩,
    fun γ hγ γ' hγ' => ?_⟩
  · rw [← oddDerivHeight_eq]
    exact hM c hc
  · exact ⟨annihIsRootB_iff.2 (isRoot_of_oddDerivIsRootB (hS δ hδ).1),
      by rw [← oddDerivHeight_eq]; exact (hS δ hδ).2⟩
  · exact ⟨annihIsRootB_iff.2 (isRoot_of_oddDerivIsRootB (hL γ hγ).1),
      by rw [← oddDerivHeight_eq]; exact (hL γ hγ).2⟩
  · rcases hwalk c hc with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · rcases hLL γ hγ γ' hγ' with h | h
    · exact Or.inl (by rw [← oddDerivHeight_eq]; exact h)
    · refine Or.inr ?_
      rw [Bool.not_eq_true']
      exact Bool.eq_false_iff.2 fun h' =>
        not_isRoot_of_oddDerivNotRootB h (annihIsRootB_iff.1 h')

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
