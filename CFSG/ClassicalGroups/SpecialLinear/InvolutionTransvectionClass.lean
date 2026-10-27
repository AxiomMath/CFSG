module

public import CFSG.ClassicalGroups.SpecialLinear.InvolutionTransvection
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix

theorem exists_vecMulVec_of_involution {K : Type*} [Field K] [CharP K 2]
    {t : Matrix (Fin 3) (Fin 3) K} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ v w : Fin 3 → K, w ⬝ᵥ v = 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
      t = 1 + Matrix.vecMulVec v w := by
  classical
  have hadd : ∀ M : Matrix (Fin 3) (Fin 3) K, M + M = 0 := by
    intro M
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hNN : (t - 1) * (t - 1) = 0 := by
    have h : (t - 1) * (t - 1) = t * t + 1 - (t + t) := by noncomm_ring
    rw [h, ht2, hadd t, sub_zero, hadd 1]
  have hN0 : t - 1 ≠ 0 := by
    intro h
    exact ht1 (sub_eq_zero.mp h)
  obtain ⟨x0, hx0⟩ : ∃ x0 : Fin 3 → K, (t - 1) *ᵥ x0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hN0
    ext i j
    have h := congrFun (hcon (Pi.single j 1)) i
    rwa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] at h
  let v : Fin 3 → K := (t - 1) *ᵥ x0
  have hv : v ≠ 0 := hx0
  let f : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := (t - 1).mulVecLin
  have hf : ∀ x : Fin 3 → K, f x = (t - 1) *ᵥ x := fun x => Matrix.mulVecLin_apply _ _
  have hrange_le : LinearMap.range f ≤ LinearMap.ker f := by
    rintro y ⟨x, rfl⟩
    show f (f x) = 0
    rw [hf, hf, Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  have hfin : Module.finrank K (Fin 3 → K) = 3 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hle : Module.finrank K (LinearMap.range f) ≤ Module.finrank K (LinearMap.ker f) :=
    Submodule.finrank_mono hrange_le
  have h2 : 2 * Module.finrank K (LinearMap.range f) ≤ 3 := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    omega
  have hle1 : Module.finrank K (LinearMap.range f) ≤ 1 := by omega
  have hne_bot : LinearMap.range f ≠ ⊥ := by
    intro hbot
    apply hN0
    ext i j
    have hmem : (t - 1) *ᵥ Pi.single j 1 ∈ LinearMap.range f :=
      ⟨Pi.single j 1, by rw [hf]⟩
    rw [hbot] at hmem
    have hz : (t - 1) *ᵥ Pi.single j 1 = 0 := by simpa using hmem
    have hzij := congrFun hz i
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at hzij
  have hge1 : 1 ≤ Module.finrank K (LinearMap.range f) := by
    rw [Submodule.one_le_finrank_iff]
    exact hne_bot
  have hfr : Module.finrank K (LinearMap.range f) = 1 := le_antisymm hle1 hge1
  have hspan : LinearMap.range f = K ∙ v :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfr ⟨x0, by rw [hf]⟩ hv
  have hmem : ∀ y : Fin 3 → K, ∃ s : K, (t - 1) *ᵥ y = s • v := by
    intro y
    have hy : (t - 1) *ᵥ y ∈ LinearMap.range f := ⟨y, by rw [hf]⟩
    rw [hspan] at hy
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨s, hs.symm⟩
  choose s hs using hmem
  let w : Fin 3 → K := fun j => s (Pi.single j 1)
  have hNvec : t - 1 = Matrix.vecMulVec v w := by
    ext i j
    have hj := congrFun (hs (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hj
    show (t - 1) i j = v i * w j
    rw [hj]
    exact mul_comm _ _
  have hNv : (t - 1) *ᵥ v = 0 := by
    show (t - 1) *ᵥ ((t - 1) *ᵥ x0) = 0
    rw [Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  have hwv : w ⬝ᵥ v = 0 := by
    have hvec : Matrix.vecMulVec v w *ᵥ v = (w ⬝ᵥ v) • v := by
      rw [Matrix.vecMulVec_mulVec]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [op_smul_eq_mul, mul_comm]
    rw [← hNvec, hNv] at hvec
    exact (smul_eq_zero.mp hvec.symm).resolve_right hv
  have hw : w ≠ 0 := by
    intro hw0
    apply hN0
    rw [hNvec, hw0, Matrix.vecMulVec_zero]
  refine ⟨v, w, hwv, hv, hw, ?_⟩
  calc t = t - 1 + 1 := (sub_add_cancel t 1).symm
    _ = 1 + (t - 1) := add_comm _ _
    _ = 1 + Matrix.vecMulVec v w := by rw [hNvec]

theorem matrix_mul_comm_one_add_vecMulVec_iff {K : Type*} [Field K] [CharP K 2]
    {v w : Fin 3 → K} (hvw : w ⬝ᵥ v = 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (g : Matrix (Fin 3) (Fin 3) K) :
    g * (1 + Matrix.vecMulVec v w) = (1 + Matrix.vecMulVec v w) * g ↔
      ∃ a : K, g *ᵥ v = a • v ∧ gᵀ *ᵥ w = a • w := by
  have hvec : ∀ x : Fin 3 → K, Matrix.vecMulVec v w *ᵥ x = (w ⬝ᵥ x) • v := by
    intro x
    rw [Matrix.vecMulVec_mulVec]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [op_smul_eq_mul, mul_comm]
  constructor
  · intro h
    have hgn : g * Matrix.vecMulVec v w = Matrix.vecMulVec v w * g := by
      have h' : g + g * Matrix.vecMulVec v w =
          g + Matrix.vecMulVec v w * g := by
        simpa only [mul_add, mul_one, add_mul, one_mul] using h
      exact add_left_cancel h'
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, w j ≠ 0 := Function.ne_iff.mp hw
    let x0 : Fin 3 → K := Pi.single j (w j)⁻¹
    have hx0 : w ⬝ᵥ x0 = 1 := by
      simp only [x0, dotProduct_single, Pi.single_eq_same]
      exact mul_inv_cancel₀ hj
    let a : K := w ⬝ᵥ (g *ᵥ x0)
    have hgv : g *ᵥ v = a • v := by
      calc g *ᵥ v = g *ᵥ (Matrix.vecMulVec v w *ᵥ x0) := by rw [hvec x0, hx0, one_smul]
        _ = (g * Matrix.vecMulVec v w) *ᵥ x0 := Matrix.mulVec_mulVec x0 g _
        _ = (Matrix.vecMulVec v w * g) *ᵥ x0 := by rw [hgn]
        _ = Matrix.vecMulVec v w *ᵥ (g *ᵥ x0) := (Matrix.mulVec_mulVec _ _ _).symm
        _ = a • v := hvec _
    have hkey : ∀ x : Fin 3 → K, w ⬝ᵥ (g *ᵥ x) = a * (w ⬝ᵥ x) := by
      intro x
      have hx : (w ⬝ᵥ (g *ᵥ x)) • v = ((w ⬝ᵥ x) * a) • v := by
        calc (w ⬝ᵥ (g *ᵥ x)) • v = Matrix.vecMulVec v w *ᵥ (g *ᵥ x) := (hvec _).symm
          _ = (Matrix.vecMulVec v w * g) *ᵥ x := Matrix.mulVec_mulVec _ _ _
          _ = (g * Matrix.vecMulVec v w) *ᵥ x := by rw [hgn]
          _ = g *ᵥ (Matrix.vecMulVec v w *ᵥ x) := (Matrix.mulVec_mulVec _ _ _).symm
          _ = g *ᵥ ((w ⬝ᵥ x) • v) := by rw [hvec x]
          _ = (w ⬝ᵥ x) • (g *ᵥ v) := by rw [Matrix.mulVec_smul]
          _ = (w ⬝ᵥ x) • (a • v) := by rw [hgv]
          _ = ((w ⬝ᵥ x) * a) • v := by rw [smul_smul]
      rw [← mul_comm (w ⬝ᵥ x) a]
      exact (smul_left_inj hv).mp hx
    have hgw : gᵀ *ᵥ w = a • w := by
      refine dotProduct_eq _ _ fun x => ?_
      calc gᵀ *ᵥ w ⬝ᵥ x = w ⬝ᵥ (g *ᵥ x) := by
            rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
        _ = a * (w ⬝ᵥ x) := hkey x
        _ = (a • w) ⬝ᵥ x := by rw [smul_dotProduct, smul_eq_mul]
    exact ⟨a, hgv, hgw⟩
  · rintro ⟨a, hgv, hgw⟩
    have hgn : g * Matrix.vecMulVec v w = Matrix.vecMulVec v w * g := by
      calc g * Matrix.vecMulVec v w = Matrix.vecMulVec (g *ᵥ v) w :=
            Matrix.mul_vecMulVec g v w
        _ = Matrix.vecMulVec (a • v) w := by rw [hgv]
        _ = a • Matrix.vecMulVec v w := Matrix.smul_vecMulVec a v w
        _ = Matrix.vecMulVec v (a • w) := (Matrix.vecMulVec_smul a v w).symm
        _ = Matrix.vecMulVec v (w ᵥ* g) := by
            rw [← Matrix.mulVec_transpose, hgw]
        _ = Matrix.vecMulVec v w * g := (Matrix.vecMulVec_mul v w g).symm
    rw [mul_add, mul_one, add_mul, one_mul, hgn]

theorem mul_comm_one_add_vecMulVec_iff {K : Type*} [Field K] [CharP K 2]
    {v w : Fin 3 → K} (hvw : w ⬝ᵥ v = 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (g : GL (Fin 3) K) :
    (g : Matrix (Fin 3) (Fin 3) K) * (1 + Matrix.vecMulVec v w) =
        (1 + Matrix.vecMulVec v w) * (g : Matrix (Fin 3) (Fin 3) K) ↔
      ∃ a : K, a ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = a • v ∧
        (g : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ w = a • w := by
  rw [matrix_mul_comm_one_add_vecMulVec_iff hvw hv hw (g : Matrix (Fin 3) (Fin 3) K)]
  constructor
  · rintro ⟨a, hgv, hgw⟩
    refine ⟨a, ?_, hgv, hgw⟩
    rintro rfl
    have hzero : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = 0 := by rw [hgv, zero_smul]
    have hv0 : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ≠ 0 := by
      intro h
      apply hv
      exact Matrix.mulVec_injective_of_isUnit (Units.isUnit g) (by simpa using h)
    exact hv0 hzero
  · rintro ⟨a, -, hgv, hgw⟩
    exact ⟨a, hgv, hgw⟩

end CFSG.ClassicalGroups.SpecialLinear
