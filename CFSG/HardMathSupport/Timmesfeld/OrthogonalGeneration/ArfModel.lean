module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.ArfNondeg
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Trace.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module

@[expose] def HasFpfModel (n p : ℕ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : FiniteDimensional (ZMod 2) V)
    (Q : QuadraticForm (ZMod 2) V), PolarNondeg Q ∧ finrank (ZMod 2) V = 2 * n ∧
    ∃ T g : V ≃ₗ[ZMod 2] V, (∀ v, Q (T v) = Q v) ∧ (∀ v, Q (g v) = Q v) ∧ orderOf T = p ∧
      (∀ v, T v = v → v = 0) ∧ g * T * g⁻¹ = T⁻¹

section Field

variable {L : Type} [Field L] [Finite L] [Algebra (ZMod 2) L]

theorem eq_zero_of_trace_mul_eq_zero {z : L}
    (h : ∀ w : L, Algebra.trace (ZMod 2) L (z * w) = 0) : z = 0 :=
  (traceForm_nondegenerate (ZMod 2) L).1 z h

@[expose] def mulEquivU (u : Lˣ) : L ≃ₗ[ZMod 2] L :=
  LinearEquiv.ofLinearMap (LinearMap.mulLeft (ZMod 2) (u : L)) (LinearMap.mulLeft (ZMod 2) (↑u⁻¹ : L))
    (by ext; simp) (by ext; simp)

omit [Finite L] in
@[simp] theorem mulEquivU_apply (u : Lˣ) (x : L) : mulEquivU u x = u * x := rfl

@[expose] noncomputable def plusBil (L : Type) [Field L] [Finite L] [Algebra (ZMod 2) L] :
    LinearMap.BilinForm (ZMod 2) (L × L) :=
  (Algebra.traceForm (ZMod 2) L).compl₁₂ (LinearMap.fst (ZMod 2) L L) (LinearMap.snd (ZMod 2) L L)

@[expose] noncomputable def plusQ (L : Type) [Field L] [Finite L] [Algebra (ZMod 2) L] :
    QuadraticForm (ZMod 2) (L × L) :=
  LinearMap.BilinMap.toQuadraticMap (plusBil L)

theorem plusQ_apply (v : L × L) : plusQ L v = Algebra.trace (ZMod 2) L (v.1 * v.2) := by
  rw [plusQ, LinearMap.BilinMap.toQuadraticMap_apply]; rfl

theorem polar_plusQ (v w : L × L) :
    polar (plusQ L) v w =
      Algebra.trace (ZMod 2) L (v.1 * w.2) + Algebra.trace (ZMod 2) L (w.1 * v.2) := by
  rw [plusQ, LinearMap.BilinMap.polar_toQuadraticMap]; rfl

theorem polarNondeg_plusQ : PolarNondeg (plusQ L) := by
  refine PolarNondeg.of_forall fun v hv => ?_
  have h1 : v.1 = 0 := eq_zero_of_trace_mul_eq_zero fun z => by
    simpa [polar_plusQ] using hv (0, z)
  have h2 : v.2 = 0 := eq_zero_of_trace_mul_eq_zero fun z => by
    simpa [polar_plusQ, mul_comm] using hv (z, 0)
  exact Prod.ext h1 h2

@[expose] def torusPlus (L : Type) [Field L] [Finite L] [Algebra (ZMod 2) L] :
    Lˣ →* ((L × L) ≃ₗ[ZMod 2] (L × L)) where
  toFun u := LinearEquiv.prodCongr (mulEquivU u) (mulEquivU u⁻¹)
  map_one' := LinearEquiv.ext fun v => by simp
  map_mul' u v := LinearEquiv.ext fun v => by
    refine Prod.ext ?_ ?_ <;> simp <;> ring

@[simp] theorem torusPlus_apply (u : Lˣ) (v : L × L) :
    torusPlus L u v = (u * v.1, ↑u⁻¹ * v.2) := rfl

theorem plusQ_torusPlus (u : Lˣ) (v : L × L) : plusQ L (torusPlus L u v) = plusQ L v := by
  rw [plusQ_apply, plusQ_apply, torusPlus_apply]
  congr 1
  calc (u : L) * v.1 * (↑u⁻¹ * v.2) = (u * ↑u⁻¹) * (v.1 * v.2) := by ring
    _ = v.1 * v.2 := by simp

theorem torusPlus_injective : Function.Injective (torusPlus L) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have := congrArg (fun T => T (1, 0)) hu
  simp at this
  exact this

theorem torusPlus_fpf {u : Lˣ} (hu : u ≠ 1) (v : L × L) (hv : torusPlus L u v = v) : v = 0 := by
  rw [Prod.ext_iff] at hv
  simp only [torusPlus_apply] at hv
  have hne : (u : L) ≠ 1 := fun h => hu (Units.ext h)
  have hne' : (↑u⁻¹ : L) ≠ 1 := fun h => hu (inv_eq_one.mp (Units.ext h))
  have h1 : v.1 = 0 := by
    by_contra h
    apply hne
    exact mul_right_cancel₀ h (by simpa using hv.1)
  have h2 : v.2 = 0 := by
    by_contra h
    apply hne'
    exact mul_right_cancel₀ h (by simpa using hv.2)
  exact Prod.ext h1 h2

theorem plusQ_swap (v : L × L) : plusQ L (LinearEquiv.prodComm (ZMod 2) L L v) = plusQ L v := by
  rw [plusQ_apply, plusQ_apply]
  simp [mul_comm]

theorem swap_mul_torusPlus (u : Lˣ) :
    LinearEquiv.prodComm (ZMod 2) L L * torusPlus L u =
      torusPlus L u⁻¹ * LinearEquiv.prodComm (ZMod 2) L L := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [torusPlus_apply, LinearEquiv.prodComm_apply, Prod.swap, inv_inv]

end Field

theorem hasFpfModel_plus {n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hdvd : p ∣ 2 ^ n - 1) :
    HasFpfModel n p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let L := GaloisField 2 n
  have hcard : Nat.card L = 2 ^ n := GaloisField.card 2 n (by omega)
  have : Fintype L := Fintype.ofFinite L
  have hunits : Nat.card Lˣ = 2 ^ n - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcard]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p (hunits ▸ hdvd)
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at ha
    exact hp.one_lt.ne ha
  refine ⟨L × L, inferInstance, inferInstance, inferInstance, plusQ L, polarNondeg_plusQ, ?_,
    torusPlus L a, LinearEquiv.prodComm (ZMod 2) L L, plusQ_torusPlus a, plusQ_swap, ?_,
    torusPlus_fpf ha1, ?_⟩
  · rw [Module.finrank_prod, GaloisField.finrank 2 (by omega)]; ring
  · rw [orderOf_injective _ torusPlus_injective a, ha]
  · rw [← map_inv, mul_inv_eq_iff_eq_mul, swap_mul_torusPlus]



section Minus

variable {M : Type} [Field M] [Finite M] [Algebra (ZMod 2) M]


variable {M : Type} [Field M] [Finite M] [Algebra (ZMod 2) M]

theorem eq_zero_of_trace_mul_eq_zero' {z : M}
    (h : ∀ w : M, Algebra.trace (ZMod 2) M (z * w) = 0) : z = 0 :=
  eq_zero_of_trace_mul_eq_zero h

@[expose] noncomputable def frobAlg (M : Type) [Field M] [Finite M] [Algebra (ZMod 2) M] (n : ℕ) :
    M ≃ₐ[ZMod 2] M :=
  FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) M ^ n

theorem frobAlg_apply (n : ℕ) (x : M) : frobAlg M n x = x ^ 2 ^ n := by
  have h := congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate (K := ZMod 2) (L := M) n) x
  rw [ZMod.card] at h
  simpa [frobAlg] using h

theorem trace_pow (n : ℕ) (x : M) :
    Algebra.trace (ZMod 2) M (x ^ 2 ^ n) = Algebra.trace (ZMod 2) M x := by
  rw [← frobAlg_apply, Algebra.trace_eq_of_algEquiv]


@[expose] noncomputable def minusBil (M : Type) [Field M] [Finite M] [Algebra (ZMod 2) M] (n : ℕ)
    (γ : M) : LinearMap.BilinForm (ZMod 2) M :=
  (Algebra.traceForm (ZMod 2) M).compl₁₂ (LinearMap.mulLeft (ZMod 2) γ)
    (frobAlg M n).toLinearMap

@[expose] noncomputable def minusQ (M : Type) [Field M] [Finite M] [Algebra (ZMod 2) M] (n : ℕ)
    (γ : M) : QuadraticForm (ZMod 2) M :=
  LinearMap.BilinMap.toQuadraticMap (minusBil M n γ)

theorem minusQ_apply (n : ℕ) (γ x : M) :
    minusQ M n γ x = Algebra.trace (ZMod 2) M (γ * x * x ^ 2 ^ n) := by
  rw [minusQ, LinearMap.BilinMap.toQuadraticMap_apply]
  simp [minusBil, frobAlg_apply]

theorem polar_minusQ (n : ℕ) (γ x y : M) :
    polar (minusQ M n γ) x y =
      Algebra.trace (ZMod 2) M (γ * x * y ^ 2 ^ n) +
        Algebra.trace (ZMod 2) M (γ * y * x ^ 2 ^ n) := by
  rw [minusQ, LinearMap.BilinMap.polar_toQuadraticMap]
  simp [minusBil, frobAlg_apply]

theorem polarNondeg_minusQ {n : ℕ} (hM : Nat.card M = (2 ^ n) ^ 2) {γ : M}
    (hγ : γ ^ 2 ^ n ≠ γ) : PolarNondeg (minusQ M n γ) := by
  have : Fintype M := Fintype.ofFinite M
  have hcard : Fintype.card M = (2 ^ n) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hM
  have hpow : ∀ x : M, (x ^ 2 ^ n) ^ 2 ^ n = x := fun x => by
    rw [← pow_mul, ← pow_two, ← hcard, FiniteField.pow_card]
  have hchar : CharP M 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) M).injective 2
  refine PolarNondeg.of_forall fun x hx => ?_
  have hz : (γ ^ 2 ^ n + γ) * x ^ 2 ^ n = 0 := by
    refine eq_zero_of_trace_mul_eq_zero' fun y => ?_
    have h := hx y
    rw [polar_minusQ] at h
    have e : Algebra.trace (ZMod 2) M (γ * x * y ^ 2 ^ n) =
        Algebra.trace (ZMod 2) M (γ ^ 2 ^ n * x ^ 2 ^ n * y) := by
      rw [← trace_pow n (γ * x * y ^ 2 ^ n), mul_pow, mul_pow, hpow]
    rw [e] at h
    have e2 : (γ ^ 2 ^ n + γ) * x ^ 2 ^ n * y =
        γ ^ 2 ^ n * x ^ 2 ^ n * y + γ * y * x ^ 2 ^ n := by ring
    rw [e2, map_add]
    exact h
  have hne : γ ^ 2 ^ n + γ ≠ 0 := by
    intro h
    apply hγ
    have := CharTwo.add_eq_zero.mp h
    exact this
  have : x ^ 2 ^ n = 0 := (mul_eq_zero.mp hz).resolve_left hne
  exact pow_eq_zero_iff (by positivity) |>.mp this


@[expose] def mulEquivM (u : Mˣ) : M ≃ₗ[ZMod 2] M :=
  LinearEquiv.ofLinearMap (LinearMap.mulLeft (ZMod 2) (u : M)) (LinearMap.mulLeft (ZMod 2) (↑u⁻¹ : M))
    (by ext; simp) (by ext; simp)

omit [Finite M] in
@[simp] theorem mulEquivM_apply (u : Mˣ) (x : M) : mulEquivM u x = u * x := rfl

@[expose] def torusMinus (M : Type) [Field M] [Finite M] [Algebra (ZMod 2) M] :
    Mˣ →* (M ≃ₗ[ZMod 2] M) where
  toFun := mulEquivM
  map_one' := LinearEquiv.ext fun x => by simp
  map_mul' u v := LinearEquiv.ext fun x => by simp [LinearEquiv.mul_apply, mul_assoc]

@[simp] theorem torusMinus_apply (u : Mˣ) (x : M) : torusMinus M u x = u * x := rfl

theorem torusMinus_injective : Function.Injective (torusMinus M) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have := congrArg (fun T => T 1) hu
  simpa using this

theorem torusMinus_fpf {u : Mˣ} (hu : u ≠ 1) (x : M) (hx : torusMinus M u x = x) : x = 0 := by
  rw [torusMinus_apply] at hx
  by_contra h
  apply hu
  exact Units.ext (mul_right_cancel₀ h (by simpa using hx))

theorem minusQ_torusMinus {n : ℕ} (γ : M) {u : Mˣ} (hu : u ^ (2 ^ n + 1) = 1) (x : M) :
    minusQ M n γ (torusMinus M u x) = minusQ M n γ x := by
  rw [minusQ_apply, minusQ_apply, torusMinus_apply]
  congr 1
  have h1 : (u : M) ^ (2 ^ n + 1) = 1 := by
    have := congrArg (fun w : Mˣ => (w : M)) hu
    simpa [Units.val_pow_eq_pow_val] using this
  calc γ * (↑u * x) * (↑u * x) ^ 2 ^ n = γ * x * x ^ 2 ^ n * ((u : M) ^ (2 ^ n + 1)) := by
        rw [mul_pow, pow_succ]; ring
    _ = γ * x * x ^ 2 ^ n := by rw [h1, mul_one]

theorem minusQ_frobAlg {n : ℕ} (hM : Nat.card M = (2 ^ n) ^ 2) (γ x : M) :
    minusQ M n γ (frobAlg M n x) = minusQ M n γ x := by
  have : Fintype M := Fintype.ofFinite M
  have hcard : Fintype.card M = (2 ^ n) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hM
  have hpow : ∀ x : M, (x ^ 2 ^ n) ^ 2 ^ n = x := fun x => by
    rw [← pow_mul, ← pow_two, ← hcard, FiniteField.pow_card]
  rw [minusQ_apply, minusQ_apply, frobAlg_apply, hpow]
  congr 1
  ring

theorem frobAlg_mul_torusMinus {n : ℕ} {u : Mˣ} (hu : u ^ (2 ^ n + 1) = 1) :
    (frobAlg M n).toLinearEquiv * torusMinus M u =
      torusMinus M u⁻¹ * (frobAlg M n).toLinearEquiv := by
  refine LinearEquiv.ext fun x => ?_
  have h1 : u ^ 2 ^ n = u⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hu)
  have h2 : (u : M) ^ 2 ^ n = ↑u⁻¹ := by
    rw [← h1, Units.val_pow_eq_pow_val]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [torusMinus_apply, AlgEquiv.toLinearEquiv_apply, frobAlg_apply, mul_pow, h2]

omit [Algebra (ZMod 2) M] in
theorem exists_pow_ne {n : ℕ} (hM : Nat.card M = (2 ^ n) ^ 2) (hn : 1 ≤ n) :
    ∃ γ : M, γ ^ 2 ^ n ≠ γ := by
  have : Fintype M := Fintype.ofFinite M
  have hcard : Fintype.card M = (2 ^ n) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hM
  by_contra hall
  push Not at hall
  have hq : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq M hq
  have hne : (Polynomial.X ^ 2 ^ n - Polynomial.X : Polynomial M) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset M).val ⊆ (Polynomial.X ^ 2 ^ n - Polynomial.X : Polynomial M).roots := by
    intro x _
    rw [Polynomial.mem_roots hne]
    simp [hall x]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg, Finset.card_univ, hcard] at this
  have h2 : 2 ^ n * 2 ^ n ≤ 2 ^ n := by rw [← pow_two]; exact this
  nlinarith


end Minus

theorem hasFpfModel_minus {n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hdvd : p ∣ 2 ^ n + 1) :
    HasFpfModel n p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let M := GaloisField 2 (2 * n)
  have hcard : Nat.card M = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]
  have : Fintype M := Fintype.ofFinite M
  have hunits : Nat.card Mˣ = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcard]
    have := Nat.sq_sub_sq (2 ^ n) 1
    simpa using this
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Mˣ) p
    (hunits ▸ dvd_mul_of_dvd_left hdvd _)
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at ha
    exact hp.one_lt.ne ha
  have haq : a ^ (2 ^ n + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (ha ▸ hdvd)
  obtain ⟨γ, hγ⟩ := exists_pow_ne hcard hn
  refine ⟨M, inferInstance, inferInstance, inferInstance, minusQ M n γ,
    polarNondeg_minusQ hcard hγ, ?_, torusMinus M a, (frobAlg M n).toLinearEquiv,
    minusQ_torusMinus γ haq, minusQ_frobAlg hcard γ, ?_, torusMinus_fpf ha1, ?_⟩
  · rw [GaloisField.finrank 2 (by omega)]
  · rw [orderOf_injective _ torusMinus_injective a, ha]
  · rw [← map_inv, mul_inv_eq_iff_eq_mul, frobAlg_mul_torusMinus haq]

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
