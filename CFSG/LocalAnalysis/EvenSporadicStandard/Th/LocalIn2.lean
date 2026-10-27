module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Data

public section

namespace CFSG.EvenSporadicStandard.ThStd

variable {G : Type} [Group G]

structure ThLocalIn2 (B A Aa : Subgroup G) (b : G) : Prop where
  Aa_le : Aa ≤ B
  Aa_comm : ∀ x ∈ Aa, ∀ y ∈ Aa, x * y = y * x
  Aa_card : Nat.card Aa = 2 ^ 8
  Aa_exp : ∀ x ∈ Aa, x ^ 4 = 1
  A_eq_sq : ∀ y, y ∈ A ↔ ∃ x ∈ Aa, x ^ 2 = y
  Aa_unique : ∀ Y : Subgroup G, Y ≤ B → (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y = 2 ^ 8 →
    Y = Aa
  b_mem : b ∈ B
  b_not_mem : b ∉ Aa
  b_sq : b ^ 2 = 1
  b_inv : ∀ x ∈ Aa, b * x * b⁻¹ = x⁻¹

end CFSG.EvenSporadicStandard.ThStd
