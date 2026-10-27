module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F2b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74QDefs

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

theorem odd_orderOf_qOne (hodd : Odd (Nat.card K)) : Odd (orderOf (qOne K)) := by
  have h : qOne K ^ ringChar K = 1 := by
    rw [qOne, HypFrame.longSL2_upperSL2, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul,
      CharP.cast_eq_zero, zero_mul, ofAdd_zero, map_one]
  exact (odd_ringChar hodd).of_dvd_nat (orderOf_dvd_of_pow_eq_one h)

theorem JThree_mem_centralizer_odd (hodd : Odd (Nat.card K)) (B : SL(2, K)) :
    (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false B ∈
      centralizer ({qOne K} : Set (spinGroup (quadOdd 3 K))) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hswap : (oddFrame 3 K).toHypFrame.toFrame fin3_zero_ne_one true false =
      ((oddFrame 3 K).toHypFrame.toFrame fin3_zero_ne_one true true).swap :=
    toFrame_not _ fin3_zero_ne_one true true
  refine mem_centralizer_singleton_iff.mpr (mul_comm_of_spinAction h2 (odd_orderOf_qOne hodd) ?_)
  rw [qOne, spinAction_longSL2, spinAction_longSL2, hswap]
  exact (Frame.La_comm_La_swap _ _ _).symm

theorem f2bOdd_holds : F2bOdd := by
  intro K _ _ hodd
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have : Finite (spinGroup (quadOdd 3 K)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  choose lift hlift using fun u : radU K => exists_odd_lift hodd u.2
  let Φ : radU K × SL(2, K) × SL(2, K) →
      centralizer ({qOne K} : Set (spinGroup (quadOdd 3 K))) := fun p =>
    ⟨lift p.1 * (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false p.2.1 *
      shortSeven K p.2.2, mul_mem (mul_mem (lift_mem_centralizer h2 (hlift p.1).2
        ((hlift p.1).1 ▸ p.1.2)) (JThree_mem_centralizer_odd hodd _))
          (shortSeven_mem_centralizer _)⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨u, B, A⟩ ⟨u', B', A'⟩ h
    have h' := congrArg Subtype.val h
    simp only [Φ] at h'
    have hπ := congrArg (spinAction (quadOdd 3 K)) h'
    simp only [map_mul, (hlift u).1, (hlift u').1] at hπ
    have hL0 : ∀ (v : radU K) (C D : SL(2, K)),
        ((v : VEnd K) * spinAction (quadOdd 3 K)
          ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false C) *
          spinAction (quadOdd 3 K) (shortSeven K D)) (oddVec 3 K 0 true) =
        spinAction (quadOdd 3 K) ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false C)
          (oddVec 3 K 0 true) := by
      intro v C D
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, shortSeven_mem_fixW D 0 true (by decide),
        (spinAction_JThree_apply C).1, apply_planeL_of_mem_radU v.2]
    have hL1 : ∀ (v : radU K) (C D : SL(2, K)),
        ((v : VEnd K) * spinAction (quadOdd 3 K)
          ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false C) *
          spinAction (quadOdd 3 K) (shortSeven K D)) (oddVec 3 K 1 true) =
        spinAction (quadOdd 3 K) ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false C)
          (oddVec 3 K 1 true) := by
      intro v C D
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, shortSeven_mem_fixW D 1 true (by decide),
        (spinAction_JThree_apply C).2, apply_planeL_of_mem_radU v.2]
    have hB : B = B' := JThree_eq_of_apply_eq
      (by rw [← hL0 u B A, ← hL0 u' B' A', hπ])
      (by rw [← hL1 u B A, ← hL1 u' B' A', hπ])
    subst hB
    have hc : ∀ D : SL(2, K), (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false B *
        shortSeven K D = shortSeven K D *
          (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false B := fun D =>
      (commute_spinJ₁_spinJ₃ ⟨D, rfl⟩ ⟨B, rfl⟩).symm
    rw [mul_assoc, mul_assoc, hc A, hc A', ← mul_assoc, ← mul_assoc] at h'
    have h'' := mul_right_cancel h'
    have hu : u = u' := by
      have hv : (u' : VEnd K)⁻¹ * (u : VEnd K) =
          spinAction (quadOdd 3 K) (shortSeven K A' * (shortSeven K A)⁻¹) := by
        have := congrArg (spinAction (quadOdd 3 K)) h''
        simp only [map_mul, (hlift u).1, (hlift u').1] at this
        rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← this, mul_inv_cancel_right]
      have h1 := eq_one_of_mem_radU_of_mem_fixW (g := shortSeven K A' * (shortSeven K A)⁻¹)
        (mul_mem (shortSeven_mem_fixW _) (inv_mem (shortSeven_mem_fixW _)))
        (hv ▸ mul_mem (inv_mem u'.2) u.2)
      rw [← hv, inv_mul_eq_one] at h1
      exact Subtype.ext h1.symm
    subst hu
    have hA : A = A' := LieType.Steinberg.SpinOdd.shortSL2_injective (oddFrame 3 K) 2 true
      (mul_left_cancel h'')
    subst hA
    rfl
  have hcard : Nat.card (radU K × SL(2, K) × SL(2, K)) =
      Nat.card K ^ 9 * (Nat.card K ^ 2 - 1) ^ 2 := by
    rw [Nat.card_prod, Nat.card_prod, card_radU,
      LieType.Steinberg.card_specialLinearGroup_fin_two]
    ring
  rw [← hcard]
  exact Nat.card_le_card_of_injective Φ hΦ

end CFSG.ComponentClassification.HarrisLit.T1.S74
