module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2S6Basic
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Setup

variable {K : Type} [Group K] [Finite K] (S : Subgroup K) [S.Normal]

theorem orderOf_conjNormal_eq_two (hC : centralizer (S : Set K) = ⊥) {z : K}
    (hz : orderOf z = 2) : orderOf (MulAut.conjNormal (H := S) z) = 2 := by
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have h1 : (MulAut.conjNormal (H := S) z) ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  have h2 : MulAut.conjNormal (H := S) z ≠ 1 := by
    intro h
    have hmem : z ∈ centralizer (S : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hx := congrArg (fun f : MulAut ↥S => ((f ⟨s, hs⟩ : ↥S) : K)) h
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at hx
      calc s * z = (z * s * z⁻¹) * z := by rw [hx]
        _ = z * s := by group
    rw [hC, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hz
    exact absurd hz (by norm_num)
  exact orderOf_eq_prime h1 h2

end Setup

end CFSG.EvenSporadicStandard.M24Std.KForm
