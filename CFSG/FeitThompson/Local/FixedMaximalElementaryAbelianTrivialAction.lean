module

public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
import CFSG.FeitThompson.Local.MaximalPlaneCentralizerPrimeTorsion
import CFSG.FeitThompson.Local.CoprimeOddFixedCentralizerTorsion

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open MulAction Subgroup

variable {p : ℕ} {P : Type*} [Group P]

theorem maximal_isElementaryAbelian_iff {E : Subgroup P} :
    Maximal (IsElementaryAbelian p) E ↔
      Maximal (fun A : Subgroup P => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E := by
  simp only [Maximal, isElementaryAbelian_iff]

theorem mem_fixedPoints_range_of_mem_centralizer_of_pow_eq_one {D : Type*} [Group D]
    (ρ : D →* MulAut P) {E : Subgroup P}
    (hE : Maximal (fun A : Subgroup P => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hEfix : ∀ a : D, ∀ e ∈ E, ρ a e = e) {x : P}
    (hx : x ∈ centralizer (FixedPoints.subgroup ρ.range P : Set P)) (hxp : x ^ p = 1) :
    x ∈ FixedPoints.subgroup ρ.range P := by
  have hEF : E ≤ FixedPoints.subgroup ρ.range P := fun e he =>
    (mem_fixedPoints_range_iff ρ).2 fun a => hEfix a e he
  refine hEF (mem_of_maximal_of_mem_centralizer_of_pow_eq_one hE ?_ hxp)
  exact mem_centralizer_iff.2 fun e he => mem_centralizer_iff.1 hx e (hEF he)

theorem fixedPoints_range_eq_top_of_maximal_isElementaryAbelianSubgroup_fixed [Finite P]
    (hp : p.Prime) (hodd : Odd p) (hP : IsPGroup p P) {D : Type*} [Group D] [Finite D]
    (ρ : D →* MulAut P) (hcop : (Nat.card D).Coprime (Nat.card P)) {E : Subgroup P}
    (hE : Maximal (IsElementaryAbelianSubgroup p) E) (hEfix : ∀ a : D, ∀ e ∈ E, ρ a e = e) :
    FixedPoints.subgroup ρ.range P = ⊤ :=
  fixedPoints_range_eq_top_of_coprime_of_pow_eq_one_mem hp hodd hP ρ hcop fun _ hx hxp =>
    mem_fixedPoints_range_of_mem_centralizer_of_pow_eq_one ρ
      (maximal_isElementaryAbelianSubgroup_iff.1 hE) hEfix hx hxp

theorem apply_eq_self_of_maximal_isElementaryAbelianSubgroup_fixed [Finite P] (hp : p.Prime)
    (hodd : Odd p) (hP : IsPGroup p P) {D : Type*} [Group D] [Finite D] (ρ : D →* MulAut P)
    (hcop : (Nat.card D).Coprime (Nat.card P)) {E : Subgroup P}
    (hE : Maximal (IsElementaryAbelianSubgroup p) E) (hEfix : ∀ a : D, ∀ e ∈ E, ρ a e = e)
    (a : D) (x : P) : ρ a x = x :=
  (mem_fixedPoints_range_iff ρ).1
    (fixedPoints_range_eq_top_of_maximal_isElementaryAbelianSubgroup_fixed hp hodd hP ρ hcop hE
      hEfix ▸ mem_top x) a

theorem apply_eq_self_of_maximal_isElementaryAbelian_fixed [Finite P] (hp : p.Prime) (hodd : Odd p)
    (hP : IsPGroup p P) {D : Type*} [Group D] [Finite D] (ρ : D →* MulAut P)
    (hcop : (Nat.card D).Coprime (Nat.card P)) {E : Subgroup P}
    (hE : Maximal (IsElementaryAbelian p) E) (hEfix : ∀ a : D, ∀ e ∈ E, ρ a e = e)
    (a : D) (x : P) : ρ a x = x :=
  apply_eq_self_of_maximal_isElementaryAbelianSubgroup_fixed hp hodd hP ρ hcop
    (maximal_isElementaryAbelianSubgroup_iff.2 (maximal_isElementaryAbelian_iff.1 hE)) hEfix a x

theorem eq_one_of_maximal_isElementaryAbelianSubgroup_fixed [Finite P] (hp : p.Prime) (hodd : Odd p)
    (hP : IsPGroup p P) {D : Type*} [Group D] [Finite D] (ρ : D →* MulAut P)
    (hcop : (Nat.card D).Coprime (Nat.card P)) {E : Subgroup P}
    (hE : Maximal (IsElementaryAbelianSubgroup p) E) (hEfix : ∀ a : D, ∀ e ∈ E, ρ a e = e)
    (a : D) : ρ a = 1 :=
  MulEquiv.ext fun x =>
    apply_eq_self_of_maximal_isElementaryAbelianSubgroup_fixed hp hodd hP ρ hcop hE hEfix a x

end

end CFSG.FeitThompson
