module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5b_sl23_eq_of_sq_eq_one {a ζ : SL23} (hζ : ζ * ζ = 1) (hζ1 : ζ ≠ 1)
    (ha : a * a = 1) : a = 1 ∨ a = ζ := by
  revert a ζ
  decide +kernel

theorem sec5b_sl23_eq_of_central {ζ c₀ : SL23} (hζ : ζ * ζ = 1) (hζ1 : ζ ≠ 1)
    (h : ∀ c : SL23, c₀ * c = c * c₀) : c₀ = 1 ∨ c₀ = ζ := by
  revert c₀ ζ
  decide +kernel

theorem sec5b_sl23_eq_of_comm_conj {ζ a₀ a : SL23} (hζ : ζ * ζ = 1) (hζ1 : ζ ≠ 1)
    (h0 : a₀ * a₀ = ζ)
    (h : ∀ c : SL23, a * (c⁻¹ * a₀ * c * a₀⁻¹) = (c⁻¹ * a₀ * c * a₀⁻¹) * a) :
    a = 1 ∨ a = ζ := by
  revert a a₀ ζ
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
