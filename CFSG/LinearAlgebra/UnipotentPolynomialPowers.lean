module

public import Mathlib.RingTheory.Binomial
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import Mathlib.Tactic.NoncommRing

public noncomputable section

namespace CFSG.LinearAlgebra

open Matrix Polynomial Finset

universe u v
variable {k : Type u} [Field k] [CharZero k]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {n : ℕ}

local instance : Algebra ℚ k := DivisionRing.toRatAlgebra

def unipotentPolynomialPowers (N : Matrix ι ι k) (d : ℕ) :
    Matrix ι ι (Polynomial k) :=
  ∑ j ∈ range d, (Ring.choose (X : Polynomial k) j) • (N ^ j).map C

theorem unipotentPolynomialPowers_eval (N : Matrix ι ι k) (d : ℕ) (t : k) :
    (unipotentPolynomialPowers N d).map (Polynomial.evalRingHom t) =
      ∑ j ∈ range d, Ring.choose t j • N ^ j := by
  ext a b
  simp only [unipotentPolynomialPowers, Matrix.map_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Polynomial.coe_evalRingHom]
  rw [Polynomial.eval_finset_sum]
  apply sum_congr rfl
  intro j _
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  have h := Ring.map_choose (Polynomial.evalRingHom t) (X : Polynomial k) j
  simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_X] using
    congrArg (· * (N ^ j) a b) h

theorem unipotentPolynomialPowers_eval_natCast
    (N : Matrix ι ι k) {d : ℕ} (hN : N ^ d = 0) (m : ℕ) :
    (unipotentPolynomialPowers N d).map (Polynomial.evalRingHom (m : k)) =
      (1 + N) ^ m := by
  rw [unipotentPolynomialPowers_eval]
  have hsum : (1 + N) ^ m =
      ∑ j ∈ range (m + 1), Ring.choose (m : k) j • N ^ j := by
    rw [add_comm, (Commute.one_right N).add_pow]
    apply sum_congr rfl
    intro j _
    simp only [one_pow, mul_one, Ring.choose_natCast]
    rw [Algebra.smul_def]
    simpa only [map_natCast] using (Nat.cast_commute (m.choose j) (N ^ j)).eq.symm
  rw [hsum]
  by_cases hdm : d ≤ m + 1
  · rw [← sum_range_add_sum_Ico (fun j => Ring.choose (m : k) j • N ^ j) hdm]
    have hz : ∑ j ∈ Ico d (m + 1), Ring.choose (m : k) j • N ^ j = 0 := by
      apply sum_eq_zero
      intro j hj
      rw [pow_eq_zero_of_le (mem_Ico.mp hj).1 hN, smul_zero]
    rw [hz, add_zero]
  · have hmd : m + 1 ≤ d := le_of_lt (lt_of_not_ge hdm)
    rw [← sum_range_add_sum_Ico (fun j => Ring.choose (m : k) j • N ^ j) hmd]
    have hz : ∑ j ∈ Ico (m + 1) d, Ring.choose (m : k) j • N ^ j = 0 := by
      apply sum_eq_zero
      intro j hj
      have hjm : m < j := by have := (mem_Ico.mp hj).1; omega
      rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hjm, Nat.cast_zero, zero_smul]
    rw [hz, add_zero]

theorem polynomial_eq_of_eval_natCast {p q : Polynomial k}
    (h : ∀ m : ℕ, p.eval (m : k) = q.eval (m : k)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  exact (Set.infinite_range_of_injective (Nat.cast_injective (R := k))).mono
    (by rintro _ ⟨m, rfl⟩; exact h m)

theorem unipotentPolynomialPowers_rescale
    (N : Matrix ι ι k) {d : ℕ} (hN : N ^ d = 0) (m : ℕ) :
    (unipotentPolynomialPowers N d).map
        (fun p => p.comp (C (m : k) * X)) =
      unipotentPolynomialPowers N d ^ m := by
  apply Matrix.ext
  intro a b
  apply polynomial_eq_of_eval_natCast
  intro r
  have hleft := unipotentPolynomialPowers_eval_natCast N hN (m * r)
  have hright := unipotentPolynomialPowers_eval_natCast N hN r
  have hpow := congrArg (fun M : Matrix ι ι k => M ^ m) hright
  have hevalpow := Matrix.map_pow (unipotentPolynomialPowers N d) (Polynomial.evalRingHom (r : k)) m
  have hentry := congrFun (congrFun (hevalpow.trans hpow) a) b
  rw [Matrix.map_apply, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  have hcast : (m : k) * (r : k) = ((m * r : ℕ) : k) := (Nat.cast_mul m r).symm
  rw [hcast]
  have hL := congrFun (congrFun hleft a) b
  simp only [Matrix.map_apply, Polynomial.coe_evalRingHom] at hL hentry
  rw [hL]
  simpa only [← pow_mul, Nat.mul_comm r m] using hentry.symm

theorem unipotentPolynomialPowers_sub_one_pow_eq_zero
    (N : Matrix ι ι k) {d : ℕ} (hN : N ^ d = 0) :
    (unipotentPolynomialPowers N d - 1) ^ d = 0 := by
  apply Matrix.ext
  intro a b
  apply polynomial_eq_of_eval_natCast
  intro m
  have hzero : ((1 + N) ^ m - 1) ^ d = 0 := by
    have hfactor : ∃ P : Matrix ι ι k, Commute N P ∧ (1 + N) ^ m - 1 = N * P := by
      induction m with
      | zero => exact ⟨0, Commute.zero_right _, by simp⟩
      | succ m ih =>
        obtain ⟨P, hP, heq⟩ := ih
        refine ⟨P * (1 + N) + 1,
          (hP.mul_right ((Commute.one_right N).add_right (Commute.refl N))).add_right
            (Commute.one_right N), ?_⟩
        rw [pow_succ, ← sub_add_cancel ((1 + N) ^ m) 1, heq]
        noncomm_ring
    obtain ⟨P, hP, heq⟩ := hfactor
    rw [heq, hP.mul_pow, hN, zero_mul]
  have hmap := Matrix.map_pow (unipotentPolynomialPowers N d - 1)
    (Polynomial.evalRingHom (m : k)) d
  have hmapbase : (unipotentPolynomialPowers N d - 1).map (Polynomial.evalRingHom (m : k)) =
      (1 + N) ^ m - 1 := by
    rw [Matrix.map_sub _ (map_sub (Polynomial.evalRingHom (m : k))),
      Matrix.map_one _ (map_zero _) (map_one _),
      unipotentPolynomialPowers_eval_natCast N hN m]
  rw [hmapbase, hzero] at hmap
  have h := congrFun (congrFun hmap a) b
  simpa only [Matrix.map_apply, Matrix.zero_apply, Polynomial.coe_evalRingHom,
    Polynomial.eval_zero] using h

theorem unipotentPolynomialPowers_eval_inv_natCast_pow
    (N : Matrix ι ι k) {d : ℕ} (hN : N ^ d = 0) {m : ℕ} (hm : m ≠ 0) :
    ((unipotentPolynomialPowers N d).map (Polynomial.evalRingHom ((m : k)⁻¹))) ^ m =
      1 + N := by
  have h := congrArg (fun M : Matrix ι ι (Polynomial k) =>
    M.map (Polynomial.evalRingHom ((m : k)⁻¹))) (unipotentPolynomialPowers_rescale N hN m)
  rw [Matrix.map_pow] at h
  have hc : ((unipotentPolynomialPowers N d).map
      (fun p => p.comp (C (m : k) * X))).map (Polynomial.evalRingHom ((m : k)⁻¹)) =
      (unipotentPolynomialPowers N d).map (Polynomial.evalRingHom 1) := by
    apply Matrix.ext
    intro a b
    simp only [Matrix.map_apply, Polynomial.coe_evalRingHom, Polynomial.eval_comp,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hm : (m : k) ≠ 0)]
  rw [hc] at h
  have h1 := unipotentPolynomialPowers_eval_natCast N hN 1
  simp only [Nat.cast_one, pow_one] at h1
  exact h.symm.trans h1

def unipotentPolynomialPowersUnit (N : Matrix ι ι k) {d : ℕ} (hN : N ^ d = 0) :
    Matrix.GeneralLinearGroup ι (Polynomial k) :=
  (show IsUnit (unipotentPolynomialPowers N d) from by
    have hn : IsNilpotent (unipotentPolynomialPowers N d - 1) :=
      ⟨d, unipotentPolynomialPowers_sub_one_pow_eq_zero N hN⟩
    simpa only [add_sub_cancel] using hn.isUnit_one_add).unit

theorem unipotentPolynomialPowersUnit_val (N : Matrix ι ι k) {d : ℕ} (hN : N ^ d = 0) :
    (unipotentPolynomialPowersUnit N hN : Matrix ι ι (Polynomial k)) =
      unipotentPolynomialPowers N d := by
  exact IsUnit.unit_spec _

theorem map_unipotentPolynomialPowersUnit_natCast
    (U : Matrix.GeneralLinearGroup ι k) {d : ℕ}
    (hU : ((U : Matrix ι ι k) - 1) ^ d = 0) (m : ℕ) :
    Matrix.GeneralLinearGroup.map (Polynomial.evalRingHom (m : k))
        (unipotentPolynomialPowersUnit ((U : Matrix ι ι k) - 1) hU) = U ^ m := by
  apply Units.ext
  simpa only [Matrix.GeneralLinearGroup.val_map_apply, unipotentPolynomialPowersUnit_val,
    Units.val_pow_eq_pow_val, add_sub_cancel] using
    unipotentPolynomialPowers_eval_natCast ((U : Matrix ι ι k) - 1) hU m

theorem map_unipotentPolynomialPowersUnit_inv_natCast_pow
    (U : Matrix.GeneralLinearGroup ι k) {d : ℕ}
    (hU : ((U : Matrix ι ι k) - 1) ^ d = 0) {m : ℕ} (hm : m ≠ 0) :
    (Matrix.GeneralLinearGroup.map (Polynomial.evalRingHom ((m : k)⁻¹))
        (unipotentPolynomialPowersUnit ((U : Matrix ι ι k) - 1) hU)) ^ m = U := by
  apply Units.ext
  simpa only [Matrix.GeneralLinearGroup.val_map_apply, unipotentPolynomialPowersUnit_val,
    Units.val_pow_eq_pow_val, add_sub_cancel] using
    unipotentPolynomialPowers_eval_inv_natCast_pow ((U : Matrix ι ι k) - 1) hU hm

def unipotentPowerCoordinate (U : Matrix.GeneralLinearGroup (Fin n) k)
    {d : ℕ} (hU : ((U : Matrix (Fin n) (Fin n) k) - 1) ^ d = 0) :
    TauCeti.GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] Polynomial k :=
  (TauCeti.GeneralLinear.generalLinearToPoint (R := k) n
    (unipotentPolynomialPowersUnit ((U : Matrix (Fin n) (Fin n) k) - 1) hU)).ofConv

theorem unipotentPowerCoordinate_eval (U : Matrix.GeneralLinearGroup (Fin n) k)
    {d : ℕ} (hU : ((U : Matrix (Fin n) (Fin n) k) - 1) ^ d = 0) (t : k) :
    WithConv.toConv ((Polynomial.aeval t).comp (unipotentPowerCoordinate U hU)) =
      TauCeti.GeneralLinear.generalLinearToPoint (R := k) n
        (Matrix.GeneralLinearGroup.map (Polynomial.evalRingHom t)
          (unipotentPolynomialPowersUnit ((U : Matrix (Fin n) (Fin n) k) - 1) hU)) := by
  have h := TauCeti.GeneralLinear.mapValue_pointsMulEquiv_symm_apply n
    (Polynomial.aeval t : Polynomial k →ₐ[k] k)
    (unipotentPolynomialPowersUnit ((U : Matrix (Fin n) (Fin n) k) - 1) hU)
  have heval : (Polynomial.aeval t : Polynomial k →ₐ[k] k).toRingHom =
      Polynomial.evalRingHom t := by
    apply RingHom.ext
    intro p
    simp
  have heval' : (Polynomial.aeval t : Polynomial k →ₐ[k] k) =
      (Polynomial.evalRingHom t : Polynomial k →+* k) := heval
  simpa only [TauCeti.AlgHom.mapValue_apply, TauCeti.GeneralLinear.pointsMulEquiv_symm_apply,
    unipotentPowerCoordinate, heval, heval'] using h

theorem unipotentPowerCoordinate_eval_natCast (U : Matrix.GeneralLinearGroup (Fin n) k)
    {d : ℕ} (hU : ((U : Matrix (Fin n) (Fin n) k) - 1) ^ d = 0) (m : ℕ) :
    WithConv.toConv ((Polynomial.aeval (m : k)).comp (unipotentPowerCoordinate U hU)) =
      (TauCeti.GeneralLinear.generalLinearToPoint (R := k) n U) ^ m := by
  rw [unipotentPowerCoordinate_eval, map_unipotentPolynomialPowersUnit_natCast]
  simpa only [TauCeti.GeneralLinear.pointsMulEquiv_symm_apply] using
    map_pow (TauCeti.GeneralLinear.pointsMulEquiv (R := k) (A := k) n).symm U m

theorem unipotentPolynomialPowers_of_pow_eval_inv_natCast
    (U : Matrix.GeneralLinearGroup ι k) {d : ℕ}
    (hU : ((U : Matrix ι ι k) - 1) ^ d = 0) {m : ℕ} (hm : m ≠ 0) :
    (unipotentPolynomialPowers (((U ^ m : Matrix.GeneralLinearGroup ι k) : Matrix ι ι k) - 1) d).map
      (Polynomial.evalRingHom ((m : k)⁻¹)) = (U : Matrix ι ι k) := by
  let N := (U : Matrix ι ι k) - 1
  have hzero : (((U ^ m : Matrix.GeneralLinearGroup ι k) : Matrix ι ι k) - 1) ^ d = 0 := by
    have hp := unipotentPolynomialPowers_sub_one_pow_eq_zero N hU
    have h := congrArg (fun P : Matrix ι ι (Polynomial k) => P.map (Polynomial.evalRingHom (m : k))) hp
    rw [Matrix.map_pow, Matrix.map_sub _ (map_sub (Polynomial.evalRingHom (m : k))),
      Matrix.map_one _ (map_zero _) (map_one _), unipotentPolynomialPowers_eval_natCast N hU m] at h
    simpa only [Matrix.map_zero _ (map_zero _), Units.val_pow_eq_pow_val, N, add_sub_cancel] using h
  have hpoly : unipotentPolynomialPowers
        (((U ^ m : Matrix.GeneralLinearGroup ι k) : Matrix ι ι k) - 1) d =
      (unipotentPolynomialPowers N d).map (fun p => p.comp (C (m : k) * X)) := by
    apply Matrix.ext
    intro a b
    apply polynomial_eq_of_eval_natCast
    intro r
    have hL := unipotentPolynomialPowers_eval_natCast
      (((U ^ m : Matrix.GeneralLinearGroup ι k) : Matrix ι ι k) - 1) hzero r
    have hR := unipotentPolynomialPowers_eval_natCast N hU (m * r)
    have heL := congrFun (congrFun hL a) b
    have heR := congrFun (congrFun hR a) b
    simp only [Matrix.map_apply, Polynomial.coe_evalRingHom] at heL heR
    rw [heL, Matrix.map_apply, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, ← Nat.cast_mul]
    simpa only [Units.val_pow_eq_pow_val, add_sub_cancel, pow_mul, N] using heR.symm
  rw [hpoly]
  have hc : ((unipotentPolynomialPowers N d).map (fun p => p.comp (C (m : k) * X))).map
      (Polynomial.evalRingHom ((m : k)⁻¹)) =
    (unipotentPolynomialPowers N d).map (Polynomial.evalRingHom 1) := by
    apply Matrix.ext
    intro a b
    simp only [Matrix.map_apply, Polynomial.coe_evalRingHom, Polynomial.eval_comp,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hm : (m : k) ≠ 0)]
  rw [hc]
  have h1 := unipotentPolynomialPowers_eval_natCast N hU 1
  simpa only [Nat.cast_one, pow_one, N, add_sub_cancel] using h1

theorem eq_of_pow_eq_of_isUnipotent
    (U V : Matrix.GeneralLinearGroup ι k)
    (hU : IsNilpotent ((U : Matrix ι ι k) - 1))
    (hV : IsNilpotent ((V : Matrix ι ι k) - 1))
    {m : ℕ} (hm : m ≠ 0) (hpow : U ^ m = V ^ m) : U = V := by
  obtain ⟨dU, hdU⟩ := hU
  obtain ⟨dV, hdV⟩ := hV
  have hdU' : ((U : Matrix ι ι k) - 1) ^ (max dU dV) = 0 :=
    pow_eq_zero_of_le (le_max_left _ _) hdU
  have hdV' : ((V : Matrix ι ι k) - 1) ^ (max dU dV) = 0 :=
    pow_eq_zero_of_le (le_max_right _ _) hdV
  have hUr := unipotentPolynomialPowers_of_pow_eval_inv_natCast U hdU' hm
  have hVr := unipotentPolynomialPowers_of_pow_eval_inv_natCast V hdV' hm
  rw [hpow] at hUr
  exact Units.ext (hUr.symm.trans hVr)

end CFSG.LinearAlgebra
