module

public import CFSG.LieType.Ree.SmallReeModelSchreier

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.Open
  CFSG.Assembly.LowTwoRank

theorem card_of_reeTitsModel_twistedG2 {G : Type} [Group G] {p f : ℕ}
    (h : ReeTitsModel G .twistedG2 p f) :
    p = 3 ∧ ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ Nat.card G = ordRee (3 ^ f) := by
  obtain ⟨-, -, hp, -, hiso⟩ := small_Ree_model_Schreier G p f h
  refine ⟨hp, ?_⟩
  subst hp
  obtain ⟨hadm, a, hfa, hmodel⟩ := h
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  have ha : 1 ≤ a := by omega
  refine ⟨a, ha, hfa, ?_⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 3 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, -, -, -, -, hcard, -⟩ :=
    small_Ree_Borel_coset_Sylow_action a K hK' w₀ hw₀
  rw [Nat.card_congr E.toEquiv, hcard, ordRee, hfa]
  exact mul_right_comm _ _ _

end CFSG.ClassicalInvolution
