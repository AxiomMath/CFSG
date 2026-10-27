module

public import CFSG.GH74.Filter.Statements
public import CFSG.GH74.Filter.Witness
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Linear
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Symplectic

public section

namespace CFSG.GH74.Filter

open Blueprint Assembly.LowTwoRank

theorem t_PSL_even_unipotent : S_PSL_even_unipotent := by
  intro G _ _ n f hm h5
  obtain ⟨⟨hp, hf, hn2, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := n) (a := n / 2) (b := (n + 1) / 2)
    (by omega) (by omega) hK
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h
  apply not_gen4_of_twoRank
  change 4 < CFSG.Open.pRank 2 (⊤ : Subgroup G)
  have : f * (n / 2 * ((n + 1) / 2)) = f * (n / 2) * ((n + 1) / 2) := by ring
  omega

theorem t_PSp_even_unipotent : S_PSp_even_unipotent := by
  intro G _ _ n f hm h5
  obtain ⟨⟨hp, hf, hn2, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.SectionRank.ClassicalOdd.le_pRank_Sp (n := n) hn2 hK
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h
  apply not_gen4_of_twoRank
  change 4 < CFSG.Open.pRank 2 (⊤ : Subgroup G)
  omega

end CFSG.GH74.Filter
