module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517_4bOfRankTwo
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUHolds

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open KFactsPair

theorem exists_split_of_isRankTwoType_of_not_unitary {d : TauCeti.LieTypeIndex}
    (h : IsRankTwoType d)
    (hUn : ¬ ∃ Q : TauCeti.PrimePower, d = .twistedA 3 Q ∨ d = .twistedA 4 Q) :
    ∃ Q : TauCeti.PrimePower, d = .A 2 Q ∨ d = .B 2 Q ∨ d = .G2 Q := by
  cases d with
  | A l Q =>
      rcases l with _ | _ | _ | _ | _ | l
      · simp [IsRankTwoType] at h
      · simp [IsRankTwoType] at h
      · exact ⟨Q, Or.inl rfl⟩
      · simp [IsRankTwoType] at h
      · simp [IsRankTwoType] at h
      · simp [IsRankTwoType] at h
  | B l Q =>
      rcases l with _ | _ | _ | _ | _ | l
      · simp [IsRankTwoType] at h
      · simp [IsRankTwoType] at h
      · exact ⟨Q, Or.inr (Or.inl rfl)⟩
      · simp [IsRankTwoType] at h
      · simp [IsRankTwoType] at h
      · simp [IsRankTwoType] at h
  | twistedA l Q =>
      rcases l with _ | _ | _ | _ | _ | _ | l
      · simp [IsRankTwoType] at h
      · simp [IsRankTwoType] at h
      · simp [IsRankTwoType] at h
      · exact absurd ⟨Q, Or.inl rfl⟩ hUn
      · exact absurd ⟨Q, Or.inr rfl⟩ hUn
      · simp [IsRankTwoType] at h
      · simp [IsRankTwoType] at h
  | G2 Q => exact ⟨Q, Or.inr (Or.inr rfl)⟩
  | C l Q => simp [IsRankTwoType] at h
  | D l Q => simp [IsRankTwoType] at h
  | twistedD l Q => simp [IsRankTwoType] at h
  | E6 Q => simp [IsRankTwoType] at h
  | E7 Q => simp [IsRankTwoType] at h
  | E8 Q => simp [IsRankTwoType] at h
  | F4 Q => simp [IsRankTwoType] at h
  | twistedE6 Q => simp [IsRankTwoType] at h
  | trialityD4 Q => simp [IsRankTwoType] at h
  | suzuki m => simp [IsRankTwoType] at h
  | reeG2 m => simp [IsRankTwoType] at h
  | reeF4 m => simp [IsRankTwoType] at h
  | tits => simp [IsRankTwoType] at h

theorem K517_4b_of_rank_two_three
    (hRest : ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X),
      GNSetting X T → GNGood T T₁ T₂ →
      ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
      gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        (∃ Q : TauCeti.PrimePower, d.1 = .A 2 Q ∨ d.1 = .B 2 Q ∨ d.1 = .G2 Q) →
        IsRankTwoPlus d.1 → IsRankTwoType d.1 →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ indexQ d.1 - 1 →
          1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls) :
    K517_4b := by
  refine K517_4b_of_rank_two ?_
  intro X _ _ T T₁ T₂ hX hGood Ls hY hinv d hd h2 he q hq hq2 hqQ
  by_cases hUn : ∃ Q : TauCeti.PrimePower, d.1 = .twistedA 3 Q ∨ d.1 = .twistedA 4 Q
  · exact K517_4b_rank_two_unitary X T T₁ T₂ hX hGood Ls hY hinv d hUn hd h2 ⟨he⟩ q hq hqQ
  · exact hRest X T T₁ T₂ hX hGood Ls hY hinv d
      (exists_split_of_isRankTwoType_of_not_unitary h2 hUn) hd h2 ⟨he⟩ q hq hq2 hqQ

@[expose] def K517_4b_rank_two_A2B2G2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X),
    GNSetting X T → GNGood T T₁ T₂ →
    ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
    gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
    ∀ d : TauCeti.ValidLieTypeIndex,
      (∃ Q : TauCeti.PrimePower, d.1 = .A 2 Q ∨ d.1 = .B 2 Q ∨ d.1 = .G2 Q) →
      IsRankTwoPlus d.1 → IsRankTwoType d.1 →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ indexQ d.1 - 1 →
        1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls

theorem K517_4b_of_rank_two_A2B2G2
    (h : K517_4b_rank_two_A2B2G2) : K517_4b :=
  K517_4b_of_rank_two_three h

end CFSG.LocalAnalysis.RankThreeUC.S15

end
