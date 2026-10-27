module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Sporadic.FischerOddCore.Fi24TJComp

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

theorem card_centralizer_tJ :
    Nat.card (Subgroup.centralizer ({CFSG.Sporadic.Fi24.tJ} : Set CFSG.Sporadic.Fi24.J)) =
      258247006617600 := by
  have h1 : Nat.card (Subgroup.centralizer ({CFSG.Sporadic.Fi24.tJ} : Set CFSG.Sporadic.Fi24.J)) =
      Nat.card CFSG.Sporadic.Fi24.CE := by
    rw [← CFSG.Sporadic.Fi24.map_centralizer_tJ,
      Subgroup.card_map_of_injective CFSG.Sporadic.Fi24.jR_injective]
  have h2 : Nat.card CFSG.Sporadic.Fi24.CE = 2 * Nat.card CFSG.Sporadic.Fi24.LE :=
    CFSG.Fischer.card_eq_two_mul_of_index inf_le_left
      CFSG.Sporadic.FischerOddCore.fi24_index_LE
  rw [h1, h2, CFSG.Sporadic.Fi24.card_LE]

end CFSG.EvenSporadicStandard.TwoFi22.DS81
