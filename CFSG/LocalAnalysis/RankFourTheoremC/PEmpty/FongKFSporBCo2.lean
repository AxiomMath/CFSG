module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSporBWit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFCub2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.Sporadic.Co2
public import Certificates.Certificate40021
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
open scoped commutatorElement

theorem co2Five_witness :
    ∃ x y g₁ g₂ : NativeSporadic.Co2, x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧
      Commute ⁅x, y⁆ y ∧
      g₁ * x * g₁⁻¹ = x ^ 2 * y ^ 1 * ⁅x, y⁆ ^ 0 ∧ g₁ * y * g₁⁻¹ = x ^ 3 * y ^ 2 * ⁅x, y⁆ ^ 2 ∧
      g₂ * x * g₂⁻¹ = x ^ 2 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧ g₂ * y * g₂⁻¹ = x ^ 3 * y ^ 4 * ⁅x, y⁆ ^ 1 :=
  (spec2 22).cub2_of_check co2FiveData Certificates.certificate40021

theorem co2Five_reach : ∀ w : Fin 2 → ZMod 5, w ≠ 0 → ∃ s : ZMod 5, s ≠ 0 ∧
    s • w ∈ Heis.reach [!![((2 : ℕ) : ZMod 5), ((3 : ℕ) : ZMod 5); ((1 : ℕ) : ZMod 5), ((2 : ℕ) : ZMod 5)],
      !![((2 : ℕ) : ZMod 5), ((3 : ℕ) : ZMod 5); ((0 : ℕ) : ZMod 5), ((4 : ℕ) : ZMod 5)]] 5 := by
  decide +kernel

theorem co2Five_oneClassE :
    OneClassE 5 NativeSporadic.Co2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, y, g₁, g₂, hx, hy, hne, hzx, hzy, h₁x, h₁y, h₂x, h₂y⟩ := co2Five_witness
  haveI : Finite NativeSporadic.Co2 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co2.card_Co2]; norm_num)
  have hsyl : ¬ 5 ^ 4 ∣ Nat.card NativeSporadic.Co2 := by
    rw [CFSG.Sporadic.Co2.card_Co2]
    decide
  exact oneClassE_of_witness (by norm_num) hsyl hx hy hne hzx hzy h₁x h₁y h₂x h₂y 5
    co2Five_reach

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF
