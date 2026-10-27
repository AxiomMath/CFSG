module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherAssembly
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairStatements
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

universe u

variable {G : Type u} [Group G]

@[expose] def PairStabilizerRankOneTheorem (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      twoRank (pairPointStabilizer H beta) = 1 ∧
        ∀ t ∈ rightPairFlipFiber H z beta, ∃ z₀ ∈ conjugacyWithin H z,
          ∃ w ∈ pairPointStabilizer H beta, orderOf w = 2 ∧ Commute w t ∧ Commute w z₀ ∧
            ¬ Subgroup.centralizer ({w} : Set G) ≤ H ∧
            MinimalInvolutionPointLocalFailure H z₀ ∧
            involutionPointClass z₀ = involutionPointClass z

@[expose] def RankOnePairFixedDegreeTheorem (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      twoRank (pairPointStabilizer H beta) = 1 →
        ∀ w ∈ pairPointStabilizer H beta, orderOf w = 2 → Commute w z →
          ¬ Subgroup.centralizer ({w} : Set G) ≤ H →
            ∃ i : ℕ, (i = 1 ∨ i = 2 ∨ i = 3) ∧
              Nat.card (elementFixedSet H w) =
                Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ i + 1

@[expose] def NonunitaryContradictionTheorem (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta,
        ∀ w ∈ pairPointStabilizer H beta, orderOf w = 2 → Commute w t → Commute w z →
          ∀ i : ℕ, (i = 1 ∨ i = 2) →
            Nat.card (elementFixedSet H w) ≠
              Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ i + 1

@[expose] def UnitaryContradictionTheorem (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta, twoRank (pairPointStabilizer H beta) = 1 →
        ∀ w ∈ pairPointStabilizer H beta, orderOf w = 2 → Commute w z → Commute w t →
          Nat.card (elementFixedSet H w) ≠
            Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 3 + 1

theorem rightPairFlipFiber_congr {H : Subgroup G} {z z₀ : G}
    (hclass : involutionPointClass z₀ = involutionPointClass z) (beta : rightCosetSpace H) :
    rightPairFlipFiber H z₀ beta = rightPairFlipFiber H z beta := by
  ext t
  simp only [rightPairFlipFiber, Set.mem_ofPred_eq, hclass]

theorem distinguishedRoots_congr {H : Subgroup G} {z z₀ : G}
    (hclass : involutionPointClass z₀ = involutionPointClass z) (w : G) :
    distinguishedRoots H z₀ w = distinguishedRoots H z w := by
  simp only [distinguishedRoots, hclass]

theorem exists_rightCoset_ne {H : Subgroup G} (hH : H ≠ ⊤) :
    ∃ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
    by_contra h
    push Not at h
    exact hH (eq_top_iff.mpr fun g _ => h g)
  refine ⟨rightCosetMk H g, fun heq => hg ?_⟩
  have := Quotient.exact heq
  change (QuotientGroup.rightRel H) g 1 at this
  rw [QuotientGroup.rightRel_apply] at this
  simpa using this

theorem not_minimalLocalFailure_of_parts [Finite G]
    (hP : PairStabilizerRankOneTheorem G) (hD : RankOnePairFixedDegreeTheorem G)
    (hN : NonunitaryContradictionTheorem G) (hU : UnitaryContradictionTheorem G)
    (H : Subgroup G) (z : G) : ¬ MinimalInvolutionPointLocalFailure H z := by
  intro h
  obtain ⟨beta, hbeta⟩ := exists_rightCoset_ne h.local_datum.proper
  obtain ⟨hcard, -, -⟩ := involution_point_uniform_pair_flips h.local_datum beta hbeta
  obtain ⟨t, ht⟩ : ∃ t, t ∈ rightPairFlipFiber H z beta := by
    have hz : z ∈ conjugacyWithin H z := ⟨1, by simp⟩
    have : Nonempty (conjugacyWithin H z) := ⟨⟨z, hz⟩⟩
    have hpos : 0 < Nat.card (rightPairFlipFiber H z beta) := hcard ▸ Nat.card_pos
    obtain ⟨⟨t, ht⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨t, ht⟩
  obtain ⟨hrank, hpair⟩ := hP H z h beta hbeta
  obtain ⟨z₀, -, w, hwB, hw, hwt, hwz₀, hesc, h₀, hclass⟩ := hpair t ht
  have ht₀ : t ∈ rightPairFlipFiber H z₀ beta := by rwa [rightPairFlipFiber_congr hclass]
  obtain ⟨i, hi, hdeg⟩ := hD H z₀ h₀ beta hbeta hrank w hwB hw hwz₀ hesc
  rcases hi with rfl | rfl | rfl
  · exact hN H z₀ h₀ beta hbeta t ht₀ w hwB hw hwt hwz₀ 1 (Or.inl rfl) hdeg
  · exact hN H z₀ h₀ beta hbeta t ht₀ w hwB hw hwt hwz₀ 2 (Or.inr rfl) hdeg
  · exact hU H z₀ h₀ beta hbeta t ht₀ hrank w hwB hw hwz₀ hwt hdeg

theorem theoremTwo_of_parts
    (h : ∀ (G : Type) [Group G] [Finite G], PairStabilizerRankOneTheorem G ∧
      RankOnePairFixedDegreeTheorem G ∧ NonunitaryContradictionTheorem G ∧
        UnitaryContradictionTheorem G) :
    CFSG.ProperTwoGeneratedCore.Assembly.TheoremTwo :=
  CFSG.ProperTwoGeneratedCore.Assembly.theoremTwo_of_no_minimal_failure fun G _ _ H z =>
    let ⟨hP, hD, hN, hU⟩ := h G
    not_minimalLocalFailure_of_parts hP hD hN hU H z

end CFSG.ProperTwoGeneratedCore.HighRankPair
