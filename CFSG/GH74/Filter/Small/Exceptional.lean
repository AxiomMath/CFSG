module

public import CFSG.GH74.Filter.Statements
public import CFSG.GH74.Filter.Witness
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels

public section

namespace CFSG.GH74.Filter

open Blueprint Assembly.LowTwoRank

theorem t_G2_even
    : S_G2_even := by
  intro G _ _ f hm
  obtain ⟨⟨hp, hf, -, h3⟩, hG⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.SectionRank.three_mul_le_pRank_of_G2Model (S := G) (p := 2) (f := f) hG
  apply not_gen4_of_twoRank
  change 4 < CFSG.Open.pRank 2 (⊤ : Subgroup G)
  have hf2 : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    omega
  omega

end CFSG.GH74.Filter
