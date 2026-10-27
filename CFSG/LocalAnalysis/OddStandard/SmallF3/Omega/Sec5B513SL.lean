module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5b513_sl23_conj_of_sq {ζ a b : SL23} (hζ : ζ * ζ = 1) (hζ1 : ζ ≠ 1)
    (ha : a * a = ζ) (hb : b * b = ζ) : ∃ u : SL23, u⁻¹ * a * u = b := by
  obtain rfl : ζ = -1 := (sl23_unique_involution ζ hζ).resolve_left hζ1
  revert a b
  decide +kernel

theorem sec5b513_sl23_comm_or_anti {ζ a u : SL23} (hζ : ζ * ζ = 1) (hζ1 : ζ ≠ 1)
    (ha : a * a = ζ) :
    (u ^ 4 = 1 → a * (u⁻¹ * a * u) = (u⁻¹ * a * u) * a) ∧
      (u ^ 4 ≠ 1 → a * (u⁻¹ * a * u) = ζ * ((u⁻¹ * a * u) * a)) := by
  obtain rfl : ζ = -1 := (sl23_unique_involution ζ hζ).resolve_left hζ1
  revert a u
  decide +kernel

theorem sec5b513_sl23_split (g : SL23) : ∃ u : SL23, u ^ 4 ≠ 1 ∧ (u⁻¹ * g) ^ 4 ≠ 1 := by
  revert g
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
