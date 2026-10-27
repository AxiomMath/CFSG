module

public import CFSG.Assembly.Defs

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving.OddGen

open Subgroup

variable {G : Type} [Group G]

theorem odd_closure_conj {B : Subgroup G} {x : G} (hx : x ∈ B) {g : G}
    (hg : g ∈ Subgroup.closure {y : G | y ∈ B ∧ Odd (orderOf y)}) :
    x * g * x⁻¹ ∈ Subgroup.closure {y : G | y ∈ B ∧ Odd (orderOf y)} := by
  have hle : Subgroup.closure {y : G | y ∈ B ∧ Odd (orderOf y)} ≤
      (Subgroup.closure {y : G | y ∈ B ∧ Odd (orderOf y)}).comap (MulAut.conj x).toMonoidHom := by
    apply (Subgroup.closure_le _).2
    rintro t ⟨htB, hto⟩
    show x * t * x⁻¹ ∈ Subgroup.closure {y : G | y ∈ B ∧ Odd (orderOf y)}
    apply Subgroup.subset_closure
    refine ⟨B.mul_mem (B.mul_mem hx htB) (B.inv_mem hx), ?_⟩
    have hpow : (x * t * x⁻¹) ^ orderOf t = 1 := by
      rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
    exact Odd.of_dvd_nat hto (orderOf_dvd_of_pow_eq_one hpow)
  exact hle hg

end CFSG.HardMathSupport.Cooperstein.Proving.OddGen

end
