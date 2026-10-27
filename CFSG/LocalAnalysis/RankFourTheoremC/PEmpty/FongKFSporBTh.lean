module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSporBWit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFCub2
public import CFSG.RankThree.OddKernel.SporadicKernelTh
public import Certificates.Certificate40020
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
open scoped commutatorElement

theorem thFive_witness :
    ∃ x y g₁ g₂ : NativeSporadic.Th, x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧
      Commute ⁅x, y⁆ y ∧
      g₁ * x * g₁⁻¹ = x ^ 2 * y ^ 4 * ⁅x, y⁆ ^ 2 ∧ g₁ * y * g₁⁻¹ = x ^ 2 * y ^ 2 * ⁅x, y⁆ ^ 0 ∧
      g₂ * x * g₂⁻¹ = x ^ 0 * y ^ 1 * ⁅x, y⁆ ^ 3 ∧ g₂ * y * g₂⁻¹ = x ^ 3 * y ^ 2 * ⁅x, y⁆ ^ 4 :=
  (spec2 248).cub2_of_check thFiveData Certificates.certificate40020

theorem thFive_reach : ∀ w : Fin 2 → ZMod 5, w ≠ 0 → ∃ s : ZMod 5, s ≠ 0 ∧
    s • w ∈ Heis.reach [!![((2 : ℕ) : ZMod 5), ((2 : ℕ) : ZMod 5); ((4 : ℕ) : ZMod 5),
      ((2 : ℕ) : ZMod 5)], !![((0 : ℕ) : ZMod 5), ((3 : ℕ) : ZMod 5); ((1 : ℕ) : ZMod 5),
      ((2 : ℕ) : ZMod 5)]] 5 := by
  decide +kernel

theorem thFive_oneClassE :
    OneClassE 5 NativeSporadic.Th := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, y, g₁, g₂, hx, hy, hne, hzx, hzy, h₁x, h₁y, h₂x, h₂y⟩ := thFive_witness
  haveI : Finite NativeSporadic.Th :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_Th_eq]; norm_num)
  have hsyl : ¬ 5 ^ 4 ∣ Nat.card NativeSporadic.Th := by
    rw [CFSG.RankThree.OddKernel.card_Th_eq]
    decide
  exact oneClassE_of_witness (by norm_num) hsyl hx hy hne hzx hzy h₁x h₁y h₂x h₂y 5
    thFive_reach

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF
