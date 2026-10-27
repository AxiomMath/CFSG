module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517_4bNotRankTwo

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open KFactsPair

theorem odd_two_pow_sub_one {e : ℕ} (he : 1 ≤ e) : Odd (2 ^ e - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  refine ⟨2 ^ k - 1, ?_⟩
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [pow_succ]
  omega

theorem odd_indexQ_sub_one_of_isRankTwoPlus {d : TauCeti.LieTypeIndex}
    (hd : IsRankTwoPlus d) : Odd (indexQ d - 1) := by
  cases d with
  | A m Q =>
      simp only [IsRankTwoPlus] at hd
      simp only [indexQ]
      rw [TauCeti.PrimePower.card_def, hd.1]
      exact odd_two_pow_sub_one Q.exponent_pos
  | B m Q =>
      simp only [IsRankTwoPlus] at hd
      simp only [indexQ]
      rw [TauCeti.PrimePower.card_def, hd.1]
      exact odd_two_pow_sub_one Q.exponent_pos
  | D m Q =>
      simp only [IsRankTwoPlus] at hd
      simp only [indexQ]
      rw [TauCeti.PrimePower.card_def, hd.1]
      exact odd_two_pow_sub_one Q.exponent_pos
  | twistedD m Q =>
      simp only [IsRankTwoPlus] at hd
      simp only [indexQ]
      rw [TauCeti.PrimePower.card_def, hd.1]
      exact odd_two_pow_sub_one Q.exponent_pos
  | twistedA m Q =>
      simp only [IsRankTwoPlus] at hd
      simp only [indexQ]
      rw [TauCeti.PrimePower.card_def, hd.1]
      exact odd_two_pow_sub_one Q.exponent_pos
  | G2 Q =>
      simp only [IsRankTwoPlus] at hd
      simp only [indexQ]
      rw [TauCeti.PrimePower.card_def, hd]
      exact odd_two_pow_sub_one Q.exponent_pos
  | C l Q => simp only [IsRankTwoPlus] at hd
  | E6 Q => simp only [IsRankTwoPlus] at hd
  | E7 Q => simp only [IsRankTwoPlus] at hd
  | E8 Q => simp only [IsRankTwoPlus] at hd
  | F4 Q => simp only [IsRankTwoPlus] at hd
  | twistedE6 Q => simp only [IsRankTwoPlus] at hd
  | trialityD4 Q => simp only [IsRankTwoPlus] at hd
  | suzuki n => simp only [IsRankTwoPlus] at hd
  | reeG2 n => simp only [IsRankTwoPlus] at hd
  | reeF4 n => simp only [IsRankTwoPlus] at hd
  | tits => simp only [IsRankTwoPlus] at hd

theorem K517_4b_of_rank_two
    (hRT : ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X),
      GNSetting X T → GNGood T T₁ T₂ →
      ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
      gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
      ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 → IsRankTwoType d.1 →
      (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ indexQ d.1 - 1 →
        1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls) :
    K517_4b := by
  intro X _ _ T T₁ T₂ hX hGood Ls hY hinv d hd he q hq hqQ
  obtain ⟨e⟩ := he
  let U : Subgroup ↥Ls := (gnImg T T ⊓ Ls).subgroupOf Ls
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (gnImg T T ⊓ Ls) Ls :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow hY.1.2.1
  have hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    · rw [show ((U.subgroupOf (⊤ : Subgroup ↥Ls)).index = U.index) from
        Subgroup.relIndex_top_right _]
      exact hS.2.2
  have hq2 : q ≠ 2 := by
    intro hq2eq
    have h2dvd : 2 ∣ indexQ d.1 - 1 := by
      rw [← hq2eq]
      exact hqQ
    obtain ⟨k, hk⟩ := odd_indexQ_sub_one_of_isRankTwoPlus hd
    obtain ⟨m, hm⟩ := h2dvd
    omega
  by_cases h2 : IsRankTwoType d.1
  · exact hRT X T T₁ T₂ hX hGood Ls hY hinv d hd h2 e q hq hq2 hqQ
  · exact k517_4b_of_not_rank_two hX hGood hY hinv hd h2 e hq hq2 hqQ
      hUmax.2.1 hUmax rfl

end CFSG.LocalAnalysis.RankThreeUC.S15

end
