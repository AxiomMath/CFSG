module

public import Certificates.Certificate10016
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Multipliers.U62Kernel

public section

namespace CFSG.LieType.Multipliers.U62

open CFSG.CosetTable

theorem cover₁_card_le :
    Finite (PG 4 cover₁) ∧ Nat.card (PG 4 cover₁) ≤ 13685760 :=
  Certificates.certificate10016

theorem cover_card_le :
    Finite (PG 5 coverWs) ∧ Nat.card (PG 5 coverWs) ≤ 12 * 9196830720 := by
  obtain ⟨f₁, c₁⟩ := cover₁_card_le
  have : Finite (PG (subsetOf 5 [0, 1, 2, 3]).length
      (restrictWords (subsetOf 5 [0, 1, 2, 3]) coverWs)) := f₁
  obtain ⟨f₀, c₀⟩ := card_le_of_genSub_index coverWs (subsetOf 5 [0, 1, 2, 3])
    kernel_index.1 kernel_index.2
  exact ⟨f₀, (c₀.trans (Nat.mul_le_mul_left 8064 c₁)).trans (by norm_num)⟩

end CFSG.LieType.Multipliers.U62
