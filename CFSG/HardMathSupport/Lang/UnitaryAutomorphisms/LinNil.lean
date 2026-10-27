module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix

variable {K : Type} [Field K] {n : ℕ}

@[expose] def rk1 (u ψ : Fin n → K) (a : K) : Matrix (Fin n) (Fin n) K :=
  1 + a • Matrix.vecMulVec u ψ

theorem rk1_vecMulVec_mulVec (a b v : Fin n → K) :
    Matrix.vecMulVec a b *ᵥ v = (b ⬝ᵥ v) • a := by
  ext i
  simp [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Finset.mul_sum, mul_comm,
    mul_left_comm]

theorem rk1_mulVec (u ψ : Fin n → K) (a : K) (v : Fin n → K) :
    rk1 u ψ a *ᵥ v = v + (a * (ψ ⬝ᵥ v)) • u := by
  rw [rk1, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, rk1_vecMulVec_mulVec,
    smul_smul]

theorem rk1_zero (u ψ : Fin n → K) : rk1 u ψ 0 = 1 := by
  simp [rk1]

theorem rk1_mul {u ψ : Fin n → K} (h : ψ ⬝ᵥ u = 0) (a b : K) :
    rk1 u ψ a * rk1 u ψ b = rk1 u ψ (a + b) := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec, rk1_mulVec, rk1_mulVec, rk1_mulVec, dotProduct_add,
    dotProduct_smul, h, smul_eq_mul]
  module

theorem rk1_pow {u ψ : Fin n → K} (h : ψ ⬝ᵥ u = 0) (a : K) (m : ℕ) :
    rk1 u ψ a ^ m = rk1 u ψ (m • a) := by
  induction m with
  | zero => simp [rk1_zero]
  | succ m ih => rw [pow_succ, ih, rk1_mul h, succ_nsmul]

theorem rk1_pow_char {u ψ : Fin n → K} (h : ψ ⬝ᵥ u = 0) (a : K) (p : ℕ) [CharP K p] :
    rk1 u ψ a ^ p = 1 := by
  rw [rk1_pow h, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, rk1_zero]

theorem det_rk1 {u ψ : Fin n → K} (h : ψ ⬝ᵥ u = 0) (a : K) : (rk1 u ψ a).det = 1 := by
  have : rk1 u ψ a = 1 + Matrix.replicateCol Unit (a • u) *
      Matrix.replicateRow Unit ψ := by
    ext i j
    simp [rk1, Matrix.vecMulVec, Matrix.replicateCol, Matrix.replicateRow,
      Matrix.mul_apply, mul_assoc]
  rw [this, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have : ψ ⬝ᵥ (a • u) = a * (ψ ⬝ᵥ u) := by
    simp [dotProduct, Finset.mul_sum, mul_left_comm]
  rw [this, h]
  simp

@[expose] def rk1SL {u ψ : Fin n → K} (h : ψ ⬝ᵥ u = 0) (a : K) :
    Matrix.SpecialLinearGroup (Fin n) K :=
  ⟨rk1 u ψ a, det_rk1 h a⟩

theorem coe_rk1SL {u ψ : Fin n → K} (h : ψ ⬝ᵥ u = 0) (a : K) :
    ((rk1SL h a : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      rk1 u ψ a := rfl

theorem conj_rk1 {g g' : Matrix (Fin n) (Fin n) K} (hgg : g * g' = 1) (u ψ : Fin n → K) (a : K) :
    g * rk1 u ψ a * g' = rk1 (g *ᵥ u) (ψ ᵥ* g') a := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  have h1 : g *ᵥ (g' *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rk1_mulVec, rk1_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul, h1, Matrix.dotProduct_mulVec]

theorem map_rk1 (σ : K →+* K) (u ψ : Fin n → K) (a : K) :
    (rk1 u ψ a).map σ = rk1 (fun i => σ (u i)) (fun i => σ (ψ i)) (σ a) := by
  ext i j
  simp [rk1, Matrix.vecMulVec, Matrix.one_apply, apply_ite σ]

theorem rk1_pair_apply {u u' ψ ψ' : Fin n → K} {a b : K} (v : Fin n → K) :
    (rk1 u ψ a * rk1 u' ψ' b) *ᵥ v =
      v + (a * (ψ ⬝ᵥ v) + a * b * (ψ ⬝ᵥ u') * (ψ' ⬝ᵥ v)) • u + (b * (ψ' ⬝ᵥ v)) • u' := by
  rw [← Matrix.mulVec_mulVec, rk1_mulVec, rk1_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  module

theorem rk1_pair_cube {u u' ψ ψ' : Fin n → K} (h1 : ψ ⬝ᵥ u = 0) (h2 : ψ' ⬝ᵥ u' = 0)
    (h3 : ψ ⬝ᵥ u' = 1) (h4 : ψ' ⬝ᵥ u = 1) {a b : K} (hab : a * b = -3) :
    (rk1 u ψ a * rk1 u' ψ' b) ^ 3 = 1 := by
  set T := rk1 u ψ a * rk1 u' ψ' b with hT
  have hTe : T *ᵥ u = (1 + a * b) • u + b • u' := by
    rw [hT, rk1_pair_apply, h1, h3, h4]
    module
  have hTe' : T *ᵥ u' = a • u + u' := by
    rw [hT, rk1_pair_apply, h2, h3]
    module
  have hz : ∀ α β : K, ∀ z, z = α • u + β • u' → z + T *ᵥ z + T *ᵥ (T *ᵥ z) = 0 := by
    intro α β z hz
    have hTz : T *ᵥ z = (α * (1 + a * b) + β * a) • u + (α * b + β) • u' := by
      rw [hz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hTe, hTe']
      module
    have hTTz : T *ᵥ (T *ᵥ z) = ((α * (1 + a * b) + β * a) * (1 + a * b) + (α * b + β) * a) • u +
        ((α * (1 + a * b) + β * a) * b + (α * b + β)) • u' := by
      rw [hTz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hTe, hTe']
      module
    rw [hTTz, hTz, hz]
    have e1 : α + (α * (1 + a * b) + β * a) +
        ((α * (1 + a * b) + β * a) * (1 + a * b) + (α * b + β) * a) = 0 := by
      linear_combination (α * (a * b + 1) + β * a) * hab
    have e2 : β + (α * b + β) + ((α * (1 + a * b) + β * a) * b + (α * b + β)) = 0 := by
      linear_combination (α * b + β) * hab
    calc _ = (α + (α * (1 + a * b) + β * a) +
        ((α * (1 + a * b) + β * a) * (1 + a * b) + (α * b + β) * a)) • u +
        (β + (α * b + β) + ((α * (1 + a * b) + β * a) * b + (α * b + β))) • u' := by module
      _ = 0 := by rw [e1, e2]; simp
  rw [Matrix.ext_iff_mulVec]
  intro v
  obtain ⟨z, hzdef⟩ : ∃ z : Fin n → K,
      z = (a * (ψ ⬝ᵥ v) + a * b * (ψ' ⬝ᵥ v)) • u + (b * (ψ' ⬝ᵥ v)) • u' := ⟨_, rfl⟩
  have hTv : T *ᵥ v = v + z := by
    rw [hzdef, hT, rk1_pair_apply, h3]
    module
  have h5 := hz _ _ z hzdef
  have hpow : T ^ 3 = T * (T * T) := by
    simp [pow_succ, mul_assoc]
  have h6 : T *ᵥ (T *ᵥ (T *ᵥ v)) = v + (z + T *ᵥ z + T *ᵥ (T *ᵥ z)) := by
    simp only [Matrix.mulVec_add, hTv]
    abel
  have h7 : (T * (T * T)) *ᵥ v = T *ᵥ (T *ᵥ (T *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec v T (T * T), ← Matrix.mulVec_mulVec v T T]
  rw [hpow, h7, h6, h5, Matrix.one_mulVec]
  simp

theorem rk1_pair_not_scalar {u u' ψ ψ' : Fin n → K} (h1 : ψ ⬝ᵥ u = 0) (h2 : ψ' ⬝ᵥ u' = 0)
    (h3 : ψ ⬝ᵥ u' = 1) (h4 : ψ' ⬝ᵥ u = 1) {a b : K} (hab : a * b = -3) (h3K : (3 : K) ≠ 0)
    (hn : 3 ≤ n) (s : K) :
    rk1 u ψ a * rk1 u' ψ' b ≠ s • (1 : Matrix (Fin n) (Fin n) K) := by
  intro hs
  let φ : (Fin n → K) →ₗ[K] K × K :=
    { toFun := fun v => (ψ ⬝ᵥ v, ψ' ⬝ᵥ v)
      map_add' := fun x y => by simp [dotProduct_add]
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hker : LinearMap.ker φ ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
    omega
  obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hv1 : ψ ⬝ᵥ v = 0 := by
    have := (LinearMap.mem_ker.mp hvker); exact congrArg Prod.fst this
  have hv2 : ψ' ⬝ᵥ v = 0 := by
    have := (LinearMap.mem_ker.mp hvker); exact congrArg Prod.snd this
  have hTv : (rk1 u ψ a * rk1 u' ψ' b) *ᵥ v = v := by
    rw [rk1_pair_apply, hv1, hv2]
    simp
  rw [hs, Matrix.smul_mulVec, Matrix.one_mulVec] at hTv
  have hs1 : s = 1 := by
    have h1 : (s - 1) • v = 0 := by rw [sub_smul, hTv, one_smul, sub_self]
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact sub_eq_zero.mp h2
    · exact absurd h2 hv0
  subst hs1
  have ha : a ≠ 0 := by
    rintro rfl
    apply h3K
    have : (0 : K) = -3 := by simpa using hab
    linear_combination this
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h4
  have hTe' : (rk1 u ψ a * rk1 u' ψ' b) *ᵥ u' = u' := by
    rw [hs, one_smul, Matrix.one_mulVec]
  rw [rk1_pair_apply, h2, h3] at hTe'
  have h5 : a • u = 0 := by
    have h7 : a • u =
        (u' + (a * 1 + a * b * 1 * 0) • u + (b * 0) • u') - u' := by module
    rw [h7, hTe', sub_self]
  rcases smul_eq_zero.mp h5 with h6 | h6
  · exact ha h6
  · exact hu h6

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
