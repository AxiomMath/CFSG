module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeFactsOrth
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveRanksNotLe
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaPlanes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TwelveRanksLe

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem exists_mulEquiv_of_isLieOver_twistedD {Y : Type} [Group Y] {r : ℕ}
    (h : IsLieOver Y (.twistedD r) 2 1) :
    4 ≤ r ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K),
      Nonempty (Y ≃* StatedProj (StatedOmega (StatedQuadMinus r K b c))) := by
  obtain ⟨⟨d, hv⟩, ⟨q, hqp, hqe, hd⟩, ⟨e⟩⟩ := h
  simp only at hd
  subst hd
  obtain ⟨⟨-, hf, hr⟩, K, hKf, hKfin, hK, b, c, -, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hqp e
  rw [hqp] at hK
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact ⟨hr, K, hKf, hKfin, hchar, b, c, ⟨e'⟩⟩

theorem three_le_pRank_of_isLieOver_twistedD {Y : Type} [Group Y] [Finite Y] {r : ℕ}
    (h : IsLieOver Y (.twistedD r) 2 1) : 3 ≤ Open.pRank 3 (⊤ : Subgroup Y) := by
  obtain ⟨hr, K, _, _, _, b, c, ⟨e⟩⟩ := exists_mulEquiv_of_isLieOver_twistedD h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three hr b c

theorem four_le_pRank_of_isLieOver_twistedD {Y : Type} [Group Y] [Finite Y] {r : ℕ}
    (h : IsLieOver Y (.twistedD r) 2 1) (hr5 : 5 ≤ r) : 4 ≤ Open.pRank 3 (⊤ : Subgroup Y) := by
  obtain ⟨-, K, _, _, _, b, c, ⟨e⟩⟩ := exists_mulEquiv_of_isLieOver_twistedD h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.four_le_pRank_three_omegaMinus
    hr5 b c

theorem center_eq_bot_of_mulEquiv {Y G : Type} [Group Y] [Group G] (e : Y ≃* G)
    (h : Subgroup.center G = ⊥) : Subgroup.center Y = ⊥ := by
  have h1 := Subgroup.map_center_eq e
  rw [h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1

theorem center_eq_bot_of_isLieOver_D {Y : Type} [Group Y] {r : ℕ} (h : IsLieOver Y (.D r) 2 1) :
    Subgroup.center Y = ⊥ := by
  obtain ⟨d, ⟨q, hqp, hqe, hd⟩, ⟨e⟩⟩ := h
  have hq : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hqp, hqe, pow_one]
  exact center_eq_bot_of_mulEquiv e
    (CFSG.HardMathSupport.Curtis.Coordinator.PLType.tauCetiOrthFacts_holds.1 r d
      ⟨q, hq, Or.inl hd⟩).1

theorem center_eq_bot_of_isLieOver_twistedD {Y : Type} [Group Y] {r : ℕ}
    (h : IsLieOver Y (.twistedD r) 2 1) : Subgroup.center Y = ⊥ := by
  obtain ⟨d, ⟨q, hqp, hqe, hd⟩, ⟨e⟩⟩ := h
  have hq : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hqp, hqe, pow_one]
  exact center_eq_bot_of_mulEquiv e
    (CFSG.HardMathSupport.Curtis.Coordinator.PLType.tauCetiOrthFacts_holds.1 r d
      ⟨q, hq, Or.inr hd⟩).1

theorem exists_isElemAbelian_card_nine_of_two_le_pRank {Y : Type} [Group Y] [Finite Y]
    (hc : Subgroup.center Y = ⊥) (h2 : 2 ≤ Open.pRank 3 (⊤ : Subgroup Y)) :
    ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ E ⊓ Subgroup.center Y = ⊥ := by
  obtain ⟨E, -, hE, hcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank Nat.prime_three
      (H := (⊤ : Subgroup Y)) h2
  exact ⟨E, hE, hcard, by rw [hc, inf_bot_eq]⟩

theorem exists_isElemAbelian_card_nine_of_isLieOver_orth {Y : Type} [Group Y] [Finite Y]
    (h : IsLieOver Y (.D 4) 2 1 ∨ ∃ r, 4 ≤ r ∧ IsLieOver Y (.twistedD r) 2 1) :
    ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ E ⊓ Subgroup.center Y = ⊥ := by
  rcases h with h | ⟨_, -, h⟩
  · exact exists_isElemAbelian_card_nine_of_two_le_pRank (center_eq_bot_of_isLieOver_D h)
      ((by norm_num : 2 ≤ 4).trans (TwelveRanksNotLe.four_le_pRank_three_of_isLieOver_D h))
  · exact exists_isElemAbelian_card_nine_of_two_le_pRank (center_eq_bot_of_isLieOver_twistedD h)
      ((by norm_num : 2 ≤ 3).trans (three_le_pRank_of_isLieOver_twistedD h))

theorem four_le_pRank_of_isLieOver_orth {Y : Type} [Group Y] [Finite Y]
    (h : IsLieOver Y (.D 4) 2 1 ∨ ∃ r, 5 ≤ r ∧ IsLieOver Y (.twistedD r) 2 1) :
    4 ≤ Open.pRank 3 (⊤ : Subgroup Y) := by
  rcases h with h | ⟨_, hr, h⟩
  · exact TwelveRanksNotLe.four_le_pRank_three_of_isLieOver_D h
  · exact four_le_pRank_of_isLieOver_twistedD h hr

end TwelveRanksLe

end CFSG.LocalAnalysis.RankThreeTheoremC
