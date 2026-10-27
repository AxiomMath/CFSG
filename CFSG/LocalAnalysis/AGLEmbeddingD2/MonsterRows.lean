module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MonsterD2PRank
import CFSG.YGroups.Y443.Tri.Finiteness

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint CFSG.Monster.Generated

theorem eq_of_sq_dvd_monsterOrder {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ 2 ∣ CFSG.Open.monsterOrder) : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
  have hN : CFSG.Open.monsterOrder ≠ 0 := by norm_num [CFSG.Open.monsterOrder]
  have hmem : p ∈ CFSG.Open.monsterOrder.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, hN⟩
  clear hN
  norm_num [CFSG.Open.monsterOrder, Nat.primeFactors, Nat.primeFactorsList] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals first
    | exact absurd rfl hp2
    | (exfalso; norm_num [CFSG.Open.monsterOrder] at h; done)
    | simp

section Rest

theorem d2IndexDatum_M_of_ne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5)
    (h7 : p ≠ 7) (h11 : p ≠ 11) (h13 : p ≠ 13) {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (e : L ≃* NativeSporadic.Carrier .M) : D2IndexDatum L p := by
  refine ⟨?_, Or.inl fun hsq => ?_⟩
  · rw [CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple e]
    exact hp.not_dvd_one
  · obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
    rw [Nat.card_congr ε.toEquiv, CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder] at hsq
    rcases eq_of_sq_dvd_monsterOrder hp hp2 hsq with h | h | h | h | h <;> contradiction

theorem d2FreeCaseAt_M_of_ne :
    D2FreeCaseAt (.sporadic .M) fun p => p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7 ∧ p ≠ 11 ∧ p ≠ 13 :=
  d2FreeCaseAt_M_of_datum fun _ _ _ _ ⟨e⟩ _ hp hp2 hne =>
    d2IndexDatum_M_of_ne hp hp2 hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2 e

theorem d2IndexCaseAt_M_of_rows
    (h7 : D2IndexCaseAt (.sporadic .M) fun p => p = 7 ∨ p = 11 ∨ p = 13) :
    D2IndexCaseAt (.sporadic .M) fun _ => True := by
  intro G _ _ hglob hD1 p _ P M A H R hesc hmax hβ Rbar K hRbar hK he
  by_cases h35 : p = 3 ∨ p = 5
  · exact d2IndexCaseAt_M_three_five G hglob hD1 p h35 P M A H R hesc hmax hβ Rbar K hRbar hK he
  by_cases h71 : p = 7 ∨ p = 11 ∨ p = 13
  · exact h7 G hglob hD1 p h71 P M A H R hesc hmax hβ Rbar K hRbar hK he
  rw [not_or] at h35
  rw [not_or, not_or] at h71
  exact d2FreeCaseAt_M_of_ne.indexCaseAt G hglob hD1 p ⟨h35.1, h35.2, h71.1, h71.2.1, h71.2.2⟩
    P M A H R hesc hmax hβ Rbar K hRbar hK he

end Rest

end CFSG.AGLEmbeddingD2
