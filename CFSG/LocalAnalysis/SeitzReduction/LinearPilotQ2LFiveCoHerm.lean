module

public import CFSG.Fischer.F4
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCoGF
import all CFSG.Fischer.F4
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.Fischer

structure HFormF4 {n : ℕ} (h : (Fin n → F4) → (Fin n → F4) → F4) : Prop where
  add_left : ∀ x x' y, h (x + x') y = h x y + h x' y
  smul_left : ∀ (c : F4) x y, h (c • x) y = c * h x y
  swap : ∀ x y, h y x = (h x y) ^ 2
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0

theorem f4_sq_sq : ∀ c : F4, (c ^ 2) ^ 2 = c := by decide

theorem f4_sq_add : ∀ a b : F4, (a + b) ^ 2 = a ^ 2 + b ^ 2 := by decide

theorem f4_eq_zero_of_sq_eq : ∀ c : F4, c ^ 2 = c → c ≠ 1 → c = 0 := by decide

theorem f4_polar_key : ∀ a : F4, a + a ^ 2 = 0 → F4.ω ^ 2 * a + F4.ω * a ^ 2 = 0 → a = 0 := by
  decide

namespace HFormF4

variable {n : ℕ} {h : (Fin n → F4) → (Fin n → F4) → F4} (hh : HFormF4 h)
include hh

theorem add_right (x y y' : Fin n → F4) : h x (y + y') = h x y + h x y' := by
  rw [hh.swap (y + y') x, hh.add_left, f4_sq_add, ← hh.swap y x, ← hh.swap y' x]

theorem smul_right (c : F4) (x y : Fin n → F4) : h x (c • y) = c ^ 2 * h x y := by
  rw [hh.swap (c • y) x, hh.smul_left, mul_pow, ← hh.swap y x]

theorem zero_left (y : Fin n → F4) : h 0 y = 0 := by
  have := hh.smul_left 0 0 y
  rwa [zero_smul, zero_mul] at this

theorem zero_right (x : Fin n → F4) : h x 0 = 0 := by
  rw [hh.swap 0 x, hh.zero_left]
  decide

theorem self_sq (x : Fin n → F4) : (h x x) ^ 2 = h x x := (hh.swap x x).symm

theorem sum_right {k : ℕ} (x : Fin n → F4) (c : Fin k → F4) (b : Fin k → Fin n → F4) :
    h x (∑ i, c i • b i) = ∑ i, (c i) ^ 2 * h x (b i) := by
  induction k with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty, hh.zero_right]
  | succ k ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hh.add_right, hh.smul_right,
      ih (fun i => c i.succ) (fun i => b i.succ)]

theorem sum_left {k : ℕ} (c : Fin k → F4) (b : Fin k → Fin n → F4) (z : Fin n → F4) :
    h (∑ i, c i • b i) z = ∑ i, c i * h (b i) z := by
  induction k with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty, hh.zero_left]
  | succ k ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hh.add_left, hh.smul_left,
      ih (fun i => c i.succ) (fun i => b i.succ)]

theorem sub_left (x x' y : Fin n → F4) : h (x - x') y = h x y - h x' y := by
  have := hh.add_left (x - x') x' y
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

theorem polar {x w : Fin n → F4} (hx : h x x = 0) (hw : h w w = 0) (h1 : h (x + w) (x + w) = 0)
    (h2 : h (x + F4.ω • w) (x + F4.ω • w) = 0) : h x w = 0 := by
  have e1 : h (x + w) (x + w) = h x w + (h x w) ^ 2 := by
    rw [hh.add_left, hh.add_right, hh.add_right, hx, hw, hh.swap x w]; ring
  have e2 : h (x + F4.ω • w) (x + F4.ω • w) = F4.ω ^ 2 * h x w + F4.ω * (h x w) ^ 2 := by
    rw [hh.add_left, hh.add_right, hh.add_right, hx, hh.smul_left, hh.smul_left, hh.smul_right,
      hh.smul_right, hw, hh.swap x w]; ring
  rw [e1] at h1
  rw [e2] at h2
  exact f4_polar_key _ h1 h2

noncomputable def toLin {k : ℕ} (b : Fin k → Fin n → F4) : (Fin n → F4) →ₗ[F4] (Fin k → F4) where
  toFun x i := h x (b i)
  map_add' x y := by funext i; exact hh.add_left x y (b i)
  map_smul' c x := by funext i; exact hh.smul_left c x (b i)

theorem exists_perp_ne_zero {k : ℕ} (hk : k < n) (b : Fin k → Fin n → F4) :
    ∃ x ≠ 0, ∀ i, h x (b i) = 0 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (hh.toLin b)
  have h2 : Module.finrank F4 (LinearMap.range (hh.toLin b)) ≤ k := by
    have := Submodule.finrank_le (LinearMap.range (hh.toLin b))
    rwa [Module.finrank_fin_fun] at this
  rw [Module.finrank_fin_fun] at h1
  have h3 : LinearMap.ker (hh.toLin b) ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h1
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h3
  exact ⟨x, hx0, fun i => congrFun (LinearMap.mem_ker.1 hx) i⟩

theorem exists_unit_perp {k : ℕ} (hk : k < n) (b : Fin k → Fin n → F4)
    (hb : ∀ i j, h (b i) (b j) = if i = j then 1 else 0) :
    ∃ x, (∀ i, h x (b i) = 0) ∧ h x x = 1 := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hiso : ∀ x, (∀ i, h x (b i) = 0) → h x x = 0 :=
    fun x hx => f4_eq_zero_of_sq_eq _ (hh.self_sq x) (hne x hx)
  obtain ⟨x0, hx00, hx0⟩ := hh.exists_perp_ne_zero hk b
  apply hx00
  apply hh.nondeg
  intro y
  set w := y - ∑ i, h y (b i) • b i with hw
  have hwp : ∀ j, h w (b j) = 0 := by
    intro j
    rw [hw, hh.sub_left, hh.sum_left]
    simp only [hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      sub_self]
  have hadd : ∀ c : F4, ∀ j, h (x0 + c • w) (b j) = 0 := by
    intro c j
    rw [hh.add_left, hh.smul_left, hx0 j, hwp j, mul_zero, add_zero]
  have hxw : h x0 w = 0 := by
    refine hh.polar (hiso _ hx0) (hiso _ hwp) ?_ (hiso _ (hadd F4.ω))
    have := hiso _ (hadd 1)
    rwa [one_smul] at this
  have hy : y = w + ∑ i, h y (b i) • b i := by rw [hw, sub_add_cancel]
  rw [hy, hh.add_right, hxw, hh.sum_right]
  simp only [hx0, mul_zero, Finset.sum_const_zero, add_zero]

theorem exists_orthonormal_family : ∀ k ≤ n, ∃ b : Fin k → Fin n → F4,
    ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  intro k
  induction k with
  | zero => intro _; exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro hk
    obtain ⟨b, hb⟩ := ih (by omega)
    obtain ⟨x, hxb, hxx⟩ := hh.exists_unit_perp (by omega) b hb
    refine ⟨Fin.snoc b x, fun i j => ?_⟩
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [hxx]
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc, hxb j]
        rw [ite_eq_right (Fin.castSucc_lt_last j).ne']
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [hh.swap, hxb i, ite_eq_right (Fin.castSucc_lt_last i).ne]
        decide
      | cast j =>
        simp only [Fin.snoc_castSucc, hb i j, Fin.castSucc_inj]

theorem exists_orthonormal : ∃ b : Fin n → Fin n → F4,
    ∀ i j, h (b i) (b j) = if i = j then 1 else 0 :=
  hh.exists_orthonormal_family n le_rfl

end HFormF4

section Matrix

@[expose] def hermF4 {n : ℕ} (A : Matrix (Fin n) (Fin n) F4) (x y : Fin n → F4) : F4 :=
  ∑ i, ∑ j, x i * A i j * y j ^ 2

theorem f4_sum_sq {ι : Type*} (s : Finset ι) (f : ι → F4) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 :=
  sum_pow_char 2 s f

theorem hFormF4_hermF4 {n : ℕ} {A : Matrix (Fin n) (Fin n) F4} (hA : ∀ i j, A j i = A i j ^ 2)
    (hdet : A.det ≠ 0) : HFormF4 (hermF4 A) where
  add_left x x' y := by simp only [hermF4, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  smul_left c x y := by
    simp only [hermF4, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  swap x y := by
    have key : ∀ i j, y j * A j i * x i ^ 2 = (x i * A i j * y j ^ 2) ^ 2 := by
      intro i j
      rw [mul_pow, mul_pow, ← hA, f4_sq_sq]
      ring
    calc hermF4 A y x = ∑ j, ∑ i, y j * A j i * x i ^ 2 := rfl
      _ = ∑ i, ∑ j, y j * A j i * x i ^ 2 := Finset.sum_comm
      _ = ∑ i, ∑ j, (x i * A i j * y j ^ 2) ^ 2 := by simp only [key]
      _ = (hermF4 A x y) ^ 2 := by
        rw [hermF4, f4_sum_sq]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [f4_sum_sq]
  nondeg x hx := by
    by_contra hx0
    apply hdet
    rw [← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨x, hx0, ?_⟩
    funext j
    have h1 := hx (Pi.single j 1)
    rw [hermF4] at h1
    have h2 : ∀ i, ∑ k, x i * A i k * (Pi.single j (1 : F4) : Fin n → F4) k ^ 2 =
        x i * A i j := by
      intro i
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj
        simp [hkj]
      · simp
    simp only [h2] at h1
    simpa [Matrix.vecMul, dotProduct] using h1

theorem transpose_mul_mul_map_eq_one {n : ℕ} {A : Matrix (Fin n) (Fin n) F4}
    {b : Fin n → Fin n → F4} (hb : ∀ i j, hermF4 A (b i) (b j) = if i = j then 1 else 0) :
    (Matrix.of fun i k => b k i)ᵀ * A * (frobenius F4 2).mapMatrix (Matrix.of fun i k => b k i) =
      1 := by
  ext k l
  rw [Matrix.one_apply, ← hb k l, hermF4]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, frobenius_def, Finset.sum_mul]
  rw [Finset.sum_comm]

end Matrix

section Lang

theorem coe_mul_graphFieldSL_inv {F : Type*} [Field F] [CharP F 2]
    (Q : SpecialLinearGroup (Fin 3) F) :
    ((Q * graphFieldSL F Q⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (Q : Matrix (Fin 3) (Fin 3) F) * ((frobenius F 2).mapMatrix (Q : Matrix (Fin 3) (Fin 3) F))ᵀ
      := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, graphFieldSL_apply, inv_inv,
    RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply, frobenius_def]

theorem f4_mul_sq_eq_one : ∀ c : F4, c ≠ 0 → c * c ^ 2 = 1 := by decide

theorem exists_eq_inv_mul_graphFieldSL (x : SpecialLinearGroup (Fin 3) F4)
    (hx : x * graphFieldSL F4 x = 1) :
    ∃ C : SpecialLinearGroup (Fin 3) F4, x = C⁻¹ * graphFieldSL F4 C := by
  set fr := (frobenius F4 2).mapMatrix (m := Fin 3) with hfr
  have hfr_apply : ∀ (M : Matrix (Fin 3) (Fin 3) F4) i j, fr M i j = M i j ^ 2 := fun M i j => by
    rw [hfr, RingHom.mapMatrix_apply, Matrix.map_apply, frobenius_def]
  set A : Matrix (Fin 3) (Fin 3) F4 :=
    ((x⁻¹ : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) with hAdef
  have hθx : graphFieldSL F4 x = x⁻¹ := eq_inv_of_mul_eq_one_right hx
  have hA : ∀ i j, A j i = A i j ^ 2 := by
    intro i j
    have h1 : (graphFieldSL F4 x : Matrix (Fin 3) (Fin 3) F4) j i = A j i := by rw [hθx]
    rw [graphFieldSL_apply] at h1
    exact h1.symm
  have hdet : A.det ≠ 0 := by
    rw [hAdef, Matrix.SpecialLinearGroup.det_coe]
    exact one_ne_zero
  obtain ⟨b, hb⟩ := (hFormF4_hermF4 hA hdet).exists_orthonormal
  have hP := transpose_mul_mul_map_eq_one hb
  set P : Matrix (Fin 3) (Fin 3) F4 := Matrix.of fun i k => b k i with hPdef
  set Q := fr P with hQdef
  have hQQ : fr Q = P := by
    ext i j
    rw [hfr_apply, hQdef, hfr_apply, f4_sq_sq]
  have hxA : (x : Matrix (Fin 3) (Fin 3) F4) * A = 1 := by
    rw [hAdef, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hQx : Q * (fr Q)ᵀ = x := by
    rw [hQQ]
    have h1 : Pᵀ * (A * Q) = 1 := by rw [← Matrix.mul_assoc]; exact hP
    have h2 : A * Q * Pᵀ = 1 := mul_eq_one_comm.1 h1
    calc Q * Pᵀ = ((x : Matrix (Fin 3) (Fin 3) F4) * A) * (Q * Pᵀ) := by
          rw [hxA, Matrix.one_mul]
      _ = x * (A * Q * Pᵀ) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [h2, Matrix.mul_one]
  have hδ0 : Q.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hQx
    rw [Matrix.det_mul, h0, zero_mul, Matrix.SpecialLinearGroup.det_coe] at h1
    exact zero_ne_one h1
  set D : Matrix (Fin 3) (Fin 3) F4 :=
    Matrix.diagonal fun i => if i = 0 then (Q.det)⁻¹ else 1 with hD
  have hQD : (Q * D).det = 1 := by
    rw [Matrix.det_mul, hD, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [mul_inv_cancel₀ hδ0]
  have hDD : D * (fr D)ᵀ = 1 := by
    have key : (Q.det)⁻¹ * ((Q.det) ^ 2)⁻¹ = 1 := by
      rw [← inv_pow]
      exact f4_mul_sq_eq_one _ (inv_ne_zero hδ0)
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    simp only [Matrix.transpose_apply, hfr_apply, hD, Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;> simp [key]
  set Q' : SpecialLinearGroup (Fin 3) F4 := ⟨Q * D, hQD⟩ with hQ'def
  refine ⟨Q'⁻¹, ?_⟩
  rw [inv_inv]
  apply Subtype.ext
  rw [coe_mul_graphFieldSL_inv]
  change (x : Matrix (Fin 3) (Fin 3) F4) = Q * D * (fr (Q * D))ᵀ
  rw [map_mul, Matrix.transpose_mul, ← hQx]
  calc Q * (fr Q)ᵀ = Q * (D * (fr D)ᵀ) * (fr Q)ᵀ := by rw [hDD, Matrix.mul_one]
    _ = Q * D * ((fr D)ᵀ * (fr Q)ᵀ) := by simp only [Matrix.mul_assoc]

end Lang

end CFSG.SeitzReduction.LinearPilot
