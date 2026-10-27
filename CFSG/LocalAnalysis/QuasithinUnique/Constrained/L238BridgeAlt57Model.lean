module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Big
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Two
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Bridge.Alt57Model

theorem alt57_g2 (K : Type) [Field K] [Finite K] (hK : ∃ n : ℕ, Nat.card K = 2 ^ n) :
    NoAlt57Image ↥(quasithinG2 K) := by
  obtain ⟨n, hn⟩ := hK
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hn]
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hcard
      have := Fintype.one_lt_card (α := K)
      omega
    · exact h0
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) hcard
  refine noAlt57Image_of_mulEquiv (MulEquiv.subgroupCongr quasithinG2_eq_cayleyGroup) ?_
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn' : n = 1 := by omega
    exact noAlt57Image_cayley_two (by rw [hn, hn']; norm_num)
  · exact noAlt57Image_cayley_big hn h2

theorem alt57ModelFacts : Alt57ModelFacts := ⟨fun K _ _ hK => alt57_sp4 K hK, alt57_g2⟩

end CFSG.QuasithinUnique.Bridge
