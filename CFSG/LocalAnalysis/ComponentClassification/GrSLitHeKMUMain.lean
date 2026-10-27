module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSLitReach
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace HeKMU

private theorem mul_pow_eq {X : Type} [Group X] {u w : X} (huu : u * u = 1) (hww : w * w = 1)
    (j : ℕ) : u * (u * w) ^ j = ((u * w) ^ j)⁻¹ * u := by
  have hux : u * (u * w) = (u * w)⁻¹ * u := by
    calc u * (u * w) = w := by rw [← mul_assoc, huu, one_mul]
      _ = (u * w)⁻¹ * u := by rw [mul_inv_rev, inv_mul_cancel_right, inv_eq_of_mul_eq_one_right hww]
  generalize u * w = x at hux ⊢
  induction j with
  | zero => simp
  | succ j ih =>
    calc u * x ^ (j + 1) = (u * x ^ j) * x := by rw [pow_succ, mul_assoc]
      _ = (x ^ j)⁻¹ * (u * x) := by rw [ih, mul_assoc]
      _ = (x ^ j)⁻¹ * (x⁻¹ * u) := by rw [hux]
      _ = (x * x ^ j)⁻¹ * u := by rw [mul_inv_rev, mul_assoc]
      _ = (x ^ (j + 1))⁻¹ * u := by rw [pow_succ']

theorem isPComponent_of_odd {X : Type} [Group X] [Finite X] {u w : X} {M : Subgroup X}
    (hu : orderOf u = 2) (hw : orderOf w = 2) (hodd : Odd (orderOf (u * w)))
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hMw : M ≤ centralizer ({w} : Set X)) :
    IsPComponent 2 (M.subgroupOf (centralizer ({w} : Set X))) := by
  obtain ⟨k, hk⟩ := hodd
  have huu : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hww : w * w = 1 := by rw [← pow_two, ← hw, pow_orderOf_eq_one]
  have hxn : (u * w) ^ (2 * k + 1) = 1 := by rw [← hk, pow_orderOf_eq_one]
  set d := (u * w) ^ (k + 1) with hd
  have hdd : d * d = u * w := by
    rw [hd, ← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hxn, one_mul]
  have hdu : d⁻¹ * u * d = w := by
    have h1 : u * d = d⁻¹ * u := mul_pow_eq huu hww (k + 1)
    calc d⁻¹ * u * d = d⁻¹ * (u * d) := by group
      _ = d⁻¹ * (d⁻¹ * u) := by rw [h1]
      _ = (d * d)⁻¹ * u := by group
      _ = w := by rw [hdd, mul_inv_rev, inv_mul_cancel_right, inv_eq_of_mul_eq_one_right hww]
  have huC : u ∈ centralizer (M : Set X) :=
    mem_centralizer_iff.mpr fun m hm => mem_centralizer_singleton_iff.mp (hMu hm)
  have hwC : w ∈ centralizer (M : Set X) :=
    mem_centralizer_iff.mpr fun m hm => mem_centralizer_singleton_iff.mp (hMw hm)
  have hdM : d ∈ centralizer (M : Set X) := pow_mem (mul_mem huC hwC) _
  have hconj : ∀ y ∈ M, (MulAut.conj d⁻¹) y = y := fun y hy => by
    rw [MulAut.conj_apply, inv_inv, mul_assoc, mem_centralizer_iff.mp hdM y hy,
      inv_mul_cancel_left]
  have hMeq : M.map (MulAut.conj d⁻¹).toMonoidHom = M := by
    ext y
    constructor
    · rintro ⟨m, hm, rfl⟩
      change (MulAut.conj d⁻¹) m ∈ M
      rw [hconj m hm]
      exact hm
    · intro hy
      exact ⟨y, hy, hconj y hy⟩
  have hφu : (MulAut.conj d⁻¹) u = w := by rw [MulAut.conj_apply, inv_inv, hdu]
  obtain ⟨-, hMφp⟩ := GSLit.isPComponent_map_centralizer (MulAut.conj d⁻¹) hMu hMp
  rw [hφu, hMeq] at hMφp
  exact hMφp

end HeKMU

end CFSG.ComponentClassification.GrSLit
