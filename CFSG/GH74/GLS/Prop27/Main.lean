module

public import CFSG.GH74.GLS.Prop27.Lemma26
public import CFSG.GH74.GLS.Prop27.Elim
public import CFSG.GH74.GLS.Prop27.EndGame
public import CFSG.GH74.GLS.Statements

public section

namespace CFSG.GH74.GLS.Prop27

open Subgroup Blueprint Assembly.LowTwoRank CFSG.Assembly.Dichotomy

theorem s_prop27G_of_leaves
    (L : Prop27Leaves) : S_prop27G := by
  intro G _ _ hG hgen hK hLB hrank hC2
  by_contra hcon
  have hL2 : ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K →
      InC2 ↥K ∧ ¬ HasL2Model ↥K IsFM9 := by
    intro x hx K hK'
    exact ⟨hC2 x hx K hK', fun hm => hcon ⟨x, hx, K, hK', hm⟩⟩
  obtain ⟨t, ht, hne⟩ : ∃ t : G, orderOf t = 2 ∧
      pPrimeCore 2 ↥(centralizer ({t} : Set G)) ≠ ⊥ := by
    rcases lemma26G_of_leaves L G hG hgen hK hrank hL2 with h | h
    · exact absurd h hLB.2.2
    · exact h
  have hne' : involutionOddCore t ≠ ⊥ := fun h => hne ((involutionOddCore_eq_bot_iff' t).mp h)
  have hrank3 : CFSG.Open.twoRank G = 3 := by
    rw [← pRank_two_eq_twoRank]
    exact hrank
  have hs : IsSimpleGroup G := hG.1
  rcases isSporadic_J1_or_isBenderGroup hG.2.1 hK hgen hrank3 L.thm182
      (fun a b ha hb hab => involutionOddCore_inf_le_of_leaves L hgen hL2 ha hb hab) ht hne' with
    hJ | hB
  · exact hne (pPrimeCore_centralizer_eq_bot_of_J1 hJ t ht)
  · exact hne (pPrimeCore_centralizer_eq_bot_of_isBenderGroup hB t ht)

end CFSG.GH74.GLS.Prop27
