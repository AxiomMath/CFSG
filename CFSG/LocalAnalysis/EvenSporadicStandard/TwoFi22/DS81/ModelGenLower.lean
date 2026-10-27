module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJProj

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen

open Subgroup CFSG.Sporadic.Fi23 FrameJ CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

section

theorem exists_odd_lift (g : CFSG.Sporadic.Fi22.J) (m : ℕ) (hm : Odd m) (hgm : g ^ m = 1) :
    ∃ c : Cd, piC c = g ∧ Odd (orderOf c) := by
  obtain ⟨c0, hc0⟩ := piC_surjective g
  refine ⟨c0 ^ (m + 1), ?_, ?_⟩
  · rw [map_pow, hc0, pow_succ, hgm, one_mul]
  · have hker : c0 ^ m ∈ piC.ker := by
      rw [MonoidHom.mem_ker, map_pow, hc0, hgm]
    have hsq : (c0 ^ m) ^ 2 = 1 := by
      have := pow_card_eq_one' (x := (⟨c0 ^ m, hker⟩ : piC.ker))
      rw [card_ker_piC] at this
      have h2 := congrArg Subtype.val this
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
      exact h2
    obtain ⟨k, hk⟩ := hm
    have hdvd : orderOf (c0 ^ (m + 1)) ∣ m := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← pow_mul, mul_comm, pow_mul]
      have : m + 1 = 2 * (k + 1) := by omega
      rw [this, pow_mul, hsq, one_pow]
    exact Odd.of_dvd_nat ⟨k, hk⟩ hdvd

end

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen
