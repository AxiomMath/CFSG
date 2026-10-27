module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

@[expose] noncomputable def hpair (x y : Fin n → K) : K := ∑ i, h.bar (x i) * y i

@[expose] noncomputable def transvMat (e : Fin n → K) (β : K) : Matrix (Fin n) (Fin n) K :=
  1 + β • Matrix.vecMulVec e (fun i => h.bar (e i))

variable {h}

theorem vecMulVec_mulVec' (a b v : Fin n → K) :
    Matrix.vecMulVec a b *ᵥ v = (b ⬝ᵥ v) • a := by
  ext i
  simp [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Finset.mul_sum, mul_comm,
    mul_left_comm]

theorem hpair_add_right (x y z : Fin n → K) : hpair h x (y + z) = hpair h x y + hpair h x z := by
  simp [hpair, mul_add, Finset.sum_add_distrib]

theorem hpair_smul_right (x y : Fin n → K) (c : K) : hpair h x (c • y) = c * hpair h x y := by
  simp [hpair, Finset.mul_sum, mul_left_comm]

theorem hpair_comm (x y : Fin n → K) : hpair h y x = h.bar (hpair h x y) := by
  simp [hpair, map_sum, h.bar_bar, mul_comm]

theorem transvMat_mulVec (e : Fin n → K) (β : K) (v : Fin n → K) :
    transvMat h e β *ᵥ v = v + (β * hpair h e v) • e := by
  rw [transvMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec']
  simp [hpair, dotProduct, smul_smul, mul_comm]

theorem transvMat_zero (e : Fin n → K) : transvMat h e 0 = 1 := by
  simp [transvMat]

theorem transvMat_mul {e : Fin n → K} (hiso : hpair h e e = 0) (β β' : K) :
    transvMat h e β * transvMat h e β' = transvMat h e (β + β') := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec, transvMat_mulVec, transvMat_mulVec, transvMat_mulVec,
    hpair_add_right, hpair_smul_right, hiso]
  module

theorem transvMat_pow {e : Fin n → K} (hiso : hpair h e e = 0) (β : K) (m : ℕ) :
    transvMat h e β ^ m = transvMat h e (m • β) := by
  induction m with
  | zero => simp [transvMat_zero]
  | succ m ih => rw [pow_succ, ih, transvMat_mul hiso, succ_nsmul]

theorem transvMat_pow_char {e : Fin n → K} (hiso : hpair h e e = 0) (β : K) :
    transvMat h e β ^ p = 1 := by
  have := h.charP
  rw [transvMat_pow hiso, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, transvMat_zero]

theorem det_transvMat {e : Fin n → K} (hiso : hpair h e e = 0) (β : K) :
    (transvMat h e β).det = 1 := by
  have : transvMat h e β = 1 + Matrix.replicateCol Unit (β • e) *
      Matrix.replicateRow Unit (fun i => h.bar (e i)) := by
    ext i j
    simp [transvMat, Matrix.vecMulVec, Matrix.replicateCol, Matrix.replicateRow,
      Matrix.mul_apply, mul_assoc]
  rw [this, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have : (fun i => h.bar (e i)) ⬝ᵥ (β • e) = β * hpair h e e := by
    simp [hpair, dotProduct, Finset.mul_sum, mul_left_comm]
  rw [this, hiso]
  simp

theorem transvMat_unitary {e : Fin n → K} (hiso : hpair h e e = 0) {β : K}
    (hβ : β + h.bar β = 0) :
    ((transvMat h e β).map h.bar)ᵀ * transvMat h e β = 1 := by
  have hT : ((transvMat h e β).map h.bar)ᵀ = transvMat h e (h.bar β) := by
    ext i j
    simp [transvMat, Matrix.vecMulVec, Matrix.one_apply, h.bar_bar, mul_comm, eq_comm,
      apply_ite h.bar]
  rw [hT, transvMat_mul hiso, add_comm, hβ, transvMat_zero]

@[expose] noncomputable def transvGL {e : Fin n → K} (hiso : hpair h e e = 0) (β : K) :
    GL (Fin n) K :=
  ⟨transvMat h e β, transvMat h e (-β), by
    rw [transvMat_mul hiso, add_neg_cancel, transvMat_zero], by
    rw [transvMat_mul hiso, neg_add_cancel, transvMat_zero]⟩

theorem coe_transvGL {e : Fin n → K} (hiso : hpair h e e = 0) (β : K) :
    ((transvGL hiso β : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = transvMat h e β := rfl

theorem hpair_mulVec {g : Matrix (Fin n) (Fin n) K} (hg : (g.map h.bar)ᵀ * g = 1)
    (v w : Fin n → K) : hpair h (g *ᵥ v) (g *ᵥ w) = hpair h v w := by
  have e1 : ∀ x : Fin n → K, (fun i => h.bar ((g *ᵥ x) i)) = (g.map h.bar) *ᵥ (fun i => h.bar (x i)) := by
    intro x
    ext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  have e2 : hpair h (g *ᵥ v) (g *ᵥ w) = ((g.map h.bar) *ᵥ (fun i => h.bar (v i))) ⬝ᵥ (g *ᵥ w) := by
    rw [← e1]; rfl
  have key : ((g.map h.bar) *ᵥ (fun i => h.bar (v i))) ᵥ* g = fun i => h.bar (v i) := by
    rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hg, Matrix.vecMul_one]
  rw [e2, Matrix.dotProduct_mulVec, key]
  rfl

theorem conj_transvMat {g g' : Matrix (Fin n) (Fin n) K} (hg : (g.map h.bar)ᵀ * g = 1)
    (hgg : g * g' = 1) (e : Fin n → K) (β : K) :
    g * transvMat h e β * g' = transvMat h (g *ᵥ e) β := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  have h1 : g *ᵥ (g' *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  have h2 : hpair h e (g' *ᵥ v) = hpair h (g *ᵥ e) v := by
    rw [← hpair_mulVec hg e (g' *ᵥ v), h1]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, transvMat_mulVec, transvMat_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul, h1, h2]

theorem map_transvMat (φ : K ≃+* K) (hφ : ∀ c, φ (h.bar c) = h.bar (φ c)) (e : Fin n → K)
    (β : K) : (transvMat h e β).map φ = transvMat h (fun i => φ (e i)) (φ β) := by
  ext i j
  simp [transvMat, Matrix.vecMulVec, Matrix.one_apply, hφ, apply_ite φ]

theorem transvMat_pair_apply {e e' : Fin n → K} {β β' : K}
    (v : Fin n → K) :
    (transvMat h e β * transvMat h e' β') *ᵥ v =
      v + (β * hpair h e v + β * β' * hpair h e e' * hpair h e' v) • e +
        (β' * hpair h e' v) • e' := by
  rw [← Matrix.mulVec_mulVec, transvMat_mulVec, transvMat_mulVec, hpair_add_right,
    hpair_smul_right]
  module

theorem transvMat_pair_cube {e e' : Fin n → K} (he : hpair h e e = 0) (he' : hpair h e' e' = 0)
    {β β' : K} (hc : hpair h e e' ≠ 0)
    (hββ : β * β' * (hpair h e e' * h.bar (hpair h e e')) = -3) :
    (transvMat h e β * transvMat h e' β') ^ 3 = 1 := by
  have _ := hc
  set T := transvMat h e β * transvMat h e' β' with hT
  set c := hpair h e e' with hcdef
  have hc' : hpair h e' e = h.bar c := hpair_comm e e'
  have hTe : T *ᵥ e = (1 + β * β' * (c * h.bar c)) • e + (β' * h.bar c) • e' := by
    rw [hT, transvMat_pair_apply, he, hc', ← hcdef]
    module
  have hTe' : T *ᵥ e' = (β * c) • e + e' := by
    rw [hT, transvMat_pair_apply, he', ← hcdef]
    module
  have hz : ∀ a b : K, ∀ z, z = a • e + b • e' → z + T *ᵥ z + T *ᵥ (T *ᵥ z) = 0 := by
    intro a b z hz
    have hTz : T *ᵥ z = (a * (1 + β * β' * (c * h.bar c)) + b * (β * c)) • e +
        (a * (β' * h.bar c) + b) • e' := by
      rw [hz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hTe, hTe']
      module
    have hTTz : T *ᵥ (T *ᵥ z) = ((a * (1 + β * β' * (c * h.bar c)) + b * (β * c)) *
          (1 + β * β' * (c * h.bar c)) + (a * (β' * h.bar c) + b) * (β * c)) • e +
        ((a * (1 + β * β' * (c * h.bar c)) + b * (β * c)) * (β' * h.bar c) +
          (a * (β' * h.bar c) + b)) • e' := by
      rw [hTz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hTe, hTe']
      module
    rw [hTTz, hTz, hz]
    have h1 : a + (a * (1 + β * β' * (c * h.bar c)) + b * (β * c)) +
        ((a * (1 + β * β' * (c * h.bar c)) + b * (β * c)) * (1 + β * β' * (c * h.bar c)) +
          (a * (β' * h.bar c) + b) * (β * c)) = 0 := by
      linear_combination (a * (β * β' * (c * h.bar c) + 1) + b * (β * c)) * hββ
    have h2 : b + (a * (β' * h.bar c) + b) +
        ((a * (1 + β * β' * (c * h.bar c)) + b * (β * c)) * (β' * h.bar c) +
          (a * (β' * h.bar c) + b)) = 0 := by
      linear_combination (a * (β' * h.bar c) + b) * hββ
    calc _ = (a + (a * (1 + β * β' * (c * h.bar c)) + b * (β * c)) +
        ((a * (1 + β * β' * (c * h.bar c)) + b * (β * c)) * (1 + β * β' * (c * h.bar c)) +
          (a * (β' * h.bar c) + b) * (β * c))) • e +
        (b + (a * (β' * h.bar c) + b) +
        ((a * (1 + β * β' * (c * h.bar c)) + b * (β * c)) * (β' * h.bar c) +
          (a * (β' * h.bar c) + b))) • e' := by module
      _ = 0 := by rw [h1, h2]; simp
  rw [Matrix.ext_iff_mulVec]
  intro v
  obtain ⟨z, hzdef⟩ : ∃ z : Fin n → K, z = (β * hpair h e v + β * β' * c * hpair h e' v) • e +
      (β' * hpair h e' v) • e' := ⟨_, rfl⟩
  have hTv : T *ᵥ v = v + z := by
    rw [hzdef, hT, transvMat_pair_apply, ← hcdef]
    module
  have h3 := hz _ _ z hzdef
  have hpow : T ^ 3 = T * (T * T) := by
    simp [pow_succ, mul_assoc]
  have h4 : T *ᵥ (T *ᵥ (T *ᵥ v)) = v + (z + T *ᵥ z + T *ᵥ (T *ᵥ z)) := by
    simp only [Matrix.mulVec_add, hTv]
    abel
  have h5 : (T * (T * T)) *ᵥ v = T *ᵥ (T *ᵥ (T *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec v T (T * T), ← Matrix.mulVec_mulVec v T T]
  rw [hpow, h5, h4, h3, Matrix.one_mulVec]
  simp

theorem transvMat_pair_not_scalar {e e' : Fin n → K} (he : hpair h e e = 0)
    (he' : hpair h e' e' = 0) {β β' : K} (hc : hpair h e e' ≠ 0)
    (hββ : β * β' * (hpair h e e' * h.bar (hpair h e e')) = -3) (h3 : (3 : K) ≠ 0) (hn : 3 ≤ n) (s : K) :
    transvMat h e β * transvMat h e' β' ≠ s • (1 : Matrix (Fin n) (Fin n) K) := by
  intro hs
  have _ := he
  set c := hpair h e e' with hcdef
  have hc' : hpair h e' e = h.bar c := hpair_comm e e'
  let φ : (Fin n → K) →ₗ[K] K × K :=
    { toFun := fun v => (hpair h e v, hpair h e' v)
      map_add' := fun x y => by simp [hpair_add_right]
      map_smul' := fun a x => by simp [hpair_smul_right] }
  have hker : LinearMap.ker φ ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
    omega
  obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hv1 : hpair h e v = 0 := by
    have := (LinearMap.mem_ker.mp hvker); exact congrArg Prod.fst this
  have hv2 : hpair h e' v = 0 := by
    have := (LinearMap.mem_ker.mp hvker); exact congrArg Prod.snd this
  have hTv : (transvMat h e β * transvMat h e' β') *ᵥ v = v := by
    rw [transvMat_pair_apply, hv1, hv2]
    simp
  rw [hs, Matrix.smul_mulVec, Matrix.one_mulVec] at hTv
  have hs1 : s = 1 := by
    have h1 : (s - 1) • v = 0 := by rw [sub_smul, hTv, one_smul, sub_self]
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact sub_eq_zero.mp h2
    · exact absurd h2 hv0
  subst hs1
  have hβ : β ≠ 0 := by
    rintro rfl
    apply h3
    have : (0 : K) = -3 := by simpa using hββ
    linear_combination this
  have hTe' : (transvMat h e β * transvMat h e' β') *ᵥ e' = e' := by
    rw [hs, one_smul, Matrix.one_mulVec]
  rw [transvMat_pair_apply, he', ← hcdef] at hTe'
  have h5 : (β * c) • e = 0 := by
    have h7 : (β * c) • e =
        (e' + (β * c + β * β' * c * 0) • e + (β' * 0) • e') - e' := by module
    rw [h7, hTe', sub_self]
  rcases smul_eq_zero.mp h5 with h6 | h6
  · exact mul_ne_zero hβ hc h6
  · apply hc
    rw [hcdef, h6]
    simp [hpair]

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
