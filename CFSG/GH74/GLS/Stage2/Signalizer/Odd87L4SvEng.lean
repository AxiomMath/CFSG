module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvArith
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvEngSeven
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Five

public section

open Subgroup CFSG.GH74.GLS.Stage4.Hex
open scoped MatrixGroups

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem l4_sl2_engine {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card F)
    {X₀ : Subgroup SL(4, F)} (hX : IsPGroup p ↥X₀) (ι : SL2 F →* SL(4, F))
    (hnorm : ∀ g, ι g ∈ normalizer (X₀ : Set SL(4, F))) :
    ∀ g, ∀ x ∈ X₀, ι g * x = x * ι g := by
  have hN0 : Nat.card SL(4, F) ≠ 0 := Nat.card_pos.ne'
  have hv : padicValNat p (Nat.card X₀) ≤ padicValNat p (Nat.card SL(4, F)) :=
    (padicValNat_dvd_iff_le hN0).1
      (pow_padicValNat_dvd.trans (Subgroup.card_subgroup_dvd_card X₀))
  by_cases hexc : p = 3 ∧ (Nat.card F = 5 ∨ Nat.card F = 7)
  · obtain ⟨rfl, h57⟩ := hexc
    rcases h57 with h | h
    · exact sl2_centralizes_five_three h ι hX hnorm (hv.trans (padicValNat_three_card_sl4_five h))
    · exact sl2_centralizes_seven_three h ι hX hnorm (hv.trans (padicValNat_three_card_sl4_seven h))
  · rcases sl2_centralizes_or_large hp2 hodd h5 hpq ι hX hnorm with h | h
    · exact h
    · exfalso
      have := padicValNat_card_sl4_lt hodd h5 hp2 hpq hexc
      omega

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
