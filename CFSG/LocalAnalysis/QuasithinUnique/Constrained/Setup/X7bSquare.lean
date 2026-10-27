module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bFlag
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bTensor

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Semidihedral.Principal Representation

section MatrixLevel

variable {k : Type} [Field k] [CharP k 2]

theorem conj_alt_apply (H X : Matrix (Fin 4) (Fin 4) k) (hX : ∀ i j, X j i = X i j)
    (hd : ∀ i, X i i = 0) (a b : Fin 4) :
    (H * X * Hᵀ) a b =
      (H a 0 * H b 1 - H a 1 * H b 0) * X 0 1 + (H a 0 * H b 2 - H a 2 * H b 0) * X 0 2 +
      (H a 0 * H b 3 - H a 3 * H b 0) * X 0 3 + (H a 1 * H b 2 - H a 2 * H b 1) * X 1 2 +
      (H a 1 * H b 3 - H a 3 * H b 1) * X 1 3 + (H a 2 * H b 3 - H a 3 * H b 2) * X 2 3 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, hd, hX 0 1, hX 0 2,
    hX 0 3, hX 1 2, hX 1 3, hX 2 3]
  linear_combination (H a 1 * H b 0 * X 0 1 + H a 2 * H b 0 * X 0 2 + H a 3 * H b 0 * X 0 3 +
    H a 2 * H b 1 * X 1 2 + H a 3 * H b 1 * X 1 3 + H a 3 * H b 2 * X 2 3) * h2

theorem conj_alt_coord (H X : Matrix (Fin 4) (Fin 4) k) (hX : ∀ i j, X j i = X i j)
    (hd : ∀ i, X i i = 0) (hk : X 1 2 = X 0 3) (a b : Fin 4)
    (hab : H a 0 * H b 3 + H a 1 * H b 2 + H a 2 * H b 1 + H a 3 * H b 0 = 0) :
    (H * X * Hᵀ) a b =
      (H a 0 * H b 1 - H a 1 * H b 0) * X 0 1 + (H a 0 * H b 2 - H a 2 * H b 0) * X 0 2 +
      (H a 1 * H b 3 - H a 3 * H b 1) * X 1 3 + (H a 2 * H b 3 - H a 3 * H b 2) * X 2 3 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [conj_alt_apply H X hX hd]
  linear_combination X 0 3 * hab - X 0 3 * (H a 3 * H b 0 + H a 2 * H b 1) * h2 +
    (H a 1 * H b 2 - H a 2 * H b 1) * hk

theorem conj_diag_apply (H X : Matrix (Fin 4) (Fin 4) k) (hX : ∀ i j, X j i = X i j) (a : Fin 4) :
    (H * X * Hᵀ) a a =
      H a 0 ^ 2 * X 0 0 + H a 1 ^ 2 * X 1 1 + H a 2 ^ 2 * X 2 2 + H a 3 ^ 2 * X 3 3 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, hX 0 1, hX 0 2,
    hX 0 3, hX 1 2, hX 1 3, hX 2 3]
  linear_combination (H a 0 * H a 1 * X 0 1 + H a 0 * H a 2 * X 0 2 + H a 0 * H a 3 * X 0 3 +
    H a 1 * H a 2 * X 1 2 + H a 1 * H a 3 * X 1 3 + H a 2 * H a 3 * X 2 3) * h2

theorem conj_alt_kappa (H X : Matrix (Fin 4) (Fin 4) k) (hX : ∀ i j, X j i = X i j)
    (hd : ∀ i, X i i = 0) (hH : Hᵀ * minorJ k * H = minorJ k) :
    (H * X * Hᵀ) 0 3 + (H * X * Hᵀ) 1 2 = X 0 3 + X 1 2 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have e : ∀ c d : Fin 4, H 0 c * H 3 d + H 1 c * H 2 d + H 2 c * H 1 d + H 3 c * H 0 d =
      minorJ k c d := fun c d => by
    have := congrFun (congrFun hH c) d
    rwa [transpose_mul_minorJ_mul_apply] at this
  have e01 : H 0 0 * H 3 1 + H 1 0 * H 2 1 + H 2 0 * H 1 1 + H 3 0 * H 0 1 = 0 := by
    simpa [minorJ_apply] using e 0 1
  have e02 : H 0 0 * H 3 2 + H 1 0 * H 2 2 + H 2 0 * H 1 2 + H 3 0 * H 0 2 = 0 := by
    simpa [minorJ_apply] using e 0 2
  have e03 : H 0 0 * H 3 3 + H 1 0 * H 2 3 + H 2 0 * H 1 3 + H 3 0 * H 0 3 = 1 := by
    simpa [minorJ_apply] using e 0 3
  have e12 : H 0 1 * H 3 2 + H 1 1 * H 2 2 + H 2 1 * H 1 2 + H 3 1 * H 0 2 = 1 := by
    simpa [minorJ_apply] using e 1 2
  have e13 : H 0 1 * H 3 3 + H 1 1 * H 2 3 + H 2 1 * H 1 3 + H 3 1 * H 0 3 = 0 := by
    simpa [minorJ_apply] using e 1 3
  have e23 : H 0 2 * H 3 3 + H 1 2 * H 2 3 + H 2 2 * H 1 3 + H 3 2 * H 0 3 = 0 := by
    simpa [minorJ_apply] using e 2 3
  rw [conj_alt_apply H X hX hd, conj_alt_apply H X hX hd]
  linear_combination X 0 1 * e01 + X 0 2 * e02 + X 0 3 * e03 + X 1 2 * e12 + X 1 3 * e13 +
    X 2 3 * e23 - (X 0 1 * (H 0 1 * H 3 0 + H 1 1 * H 2 0) +
      X 0 2 * (H 0 2 * H 3 0 + H 1 2 * H 2 0) + X 0 3 * (H 0 3 * H 3 0 + H 1 3 * H 2 0) +
      X 1 2 * (H 0 2 * H 3 1 + H 1 2 * H 2 1) + X 1 3 * (H 0 3 * H 3 1 + H 1 3 * H 2 1) +
      X 2 3 * (H 0 3 * H 3 2 + H 1 3 * H 2 2)) * h2

end MatrixLevel

section Spaces

variable (k : Type) [Field k]

@[expose] def pMap : Matrix (Fin 4) (Fin 4) k →ₗ[k] Matrix (Fin 4) (Fin 4) k where
  toFun X := X + Xᵀ
  map_add' X Y := by
    rw [Matrix.transpose_add]
    abel
  map_smul' c X := by
    rw [Matrix.transpose_smul, smul_add]
    rfl

@[expose] def entryL (i j : Fin 4) : Matrix (Fin 4) (Fin 4) k →ₗ[k] k :=
  Matrix.entryLinearMap k k i j

@[expose] def kapL : Matrix (Fin 4) (Fin 4) k →ₗ[k] k := entryL k 0 3 + entryL k 1 2

@[expose] def tauL : Matrix (Fin 4) (Fin 4) k →ₗ[k] k :=
  entryL k 0 3 + entryL k 3 0 + entryL k 1 2 + entryL k 2 1

@[expose] def pairL : Matrix (Fin 4) (Fin 4) k →ₗ[k] k := entryL k 0 3 + entryL k 3 0

@[expose] def diagL : Matrix (Fin 4) (Fin 4) k →ₗ[k] (Fin 4 → k) :=
  LinearMap.pi fun i => entryL k i i

@[expose] def coordL : Matrix (Fin 4) (Fin 4) k →ₗ[k] (Fin 4 → k) :=
  LinearMap.pi fun q => entryL k (minorIdx q).1 (minorIdx q).2

@[expose] def coordPL : Matrix (Fin 4) (Fin 4) k →ₗ[k] (Fin 4 → k) := coordL k ∘ₗ pMap k

@[expose] def wJ : Submodule k (Matrix (Fin 4) (Fin 4) k) := Submodule.span k {minorJ k}

@[expose] def symSub : Submodule k (Matrix (Fin 4) (Fin 4) k) := LinearMap.ker (pMap k)

@[expose] def altSub : Submodule k (Matrix (Fin 4) (Fin 4) k) :=
  symSub k ⊓ LinearMap.ker (diagL k)

@[expose] def kerKap : Submodule k (Matrix (Fin 4) (Fin 4) k) := altSub k ⊓ LinearMap.ker (kapL k)

@[expose] def preJ : Submodule k (Matrix (Fin 4) (Fin 4) k) := (wJ k).comap (pMap k)

@[expose] def kerTau : Submodule k (Matrix (Fin 4) (Fin 4) k) := LinearMap.ker (tauL k)

@[expose] def sqChain : Fin 8 → Submodule k (Matrix (Fin 4) (Fin 4) k) :=
  ![⊥, wJ k, kerKap k, altSub k, symSub k, preJ k, kerTau k, ⊤]

variable {k}

theorem pMap_apply (X : Matrix (Fin 4) (Fin 4) k) : pMap k X = X + Xᵀ := rfl

theorem entryL_apply (i j : Fin 4) (X : Matrix (Fin 4) (Fin 4) k) : entryL k i j X = X i j := rfl

theorem mem_wJ {X : Matrix (Fin 4) (Fin 4) k} : X ∈ wJ k ↔ ∃ c : k, X = c • minorJ k := by
  rw [wJ, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

theorem mem_preJ {X : Matrix (Fin 4) (Fin 4) k} : X ∈ preJ k ↔ ∃ c : k, X + Xᵀ = c • minorJ k := by
  rw [preJ, Submodule.mem_comap, mem_wJ]
  rfl

theorem mem_kerTau {X : Matrix (Fin 4) (Fin 4) k} :
    X ∈ kerTau k ↔ X 0 3 + X 3 0 + X 1 2 + X 2 1 = 0 := by
  simp only [kerTau, LinearMap.mem_ker, tauL, LinearMap.add_apply, entryL_apply]

variable [CharP k 2]

theorem mem_symSub {X : Matrix (Fin 4) (Fin 4) k} :
    X ∈ symSub k ↔ ∀ i j, X j i = X i j := by
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simp only [pMap_apply] at this
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply] at this
    exact (CharTwo.add_eq_zero.mp this).symm
  · intro h
    show X + Xᵀ = 0
    ext i j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply]
    rw [h i j]
    exact CharTwo.add_self_eq_zero _

theorem mem_altSub {X : Matrix (Fin 4) (Fin 4) k} :
    X ∈ altSub k ↔ (∀ i j, X j i = X i j) ∧ ∀ i, X i i = 0 := by
  rw [altSub, Submodule.mem_inf, mem_symSub]
  simp only [LinearMap.mem_ker]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i => ?_⟩
    have := congrFun h2 i
    exact this
  · rintro ⟨h1, h2⟩
    exact ⟨h1, funext h2⟩

theorem mem_kerKap {X : Matrix (Fin 4) (Fin 4) k} :
    X ∈ kerKap k ↔ ((∀ i j, X j i = X i j) ∧ ∀ i, X i i = 0) ∧ X 1 2 = X 0 3 := by
  rw [kerKap, Submodule.mem_inf, mem_altSub]
  simp only [LinearMap.mem_ker, kapL, LinearMap.add_apply, entryL_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (CharTwo.add_eq_zero.mp h2).symm⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h2]
    exact CharTwo.add_self_eq_zero _

end Spaces

section Action

variable {k : Type} [Field k]

@[expose] def actL (H : Matrix (Fin 4) (Fin 4) k) :
    Matrix (Fin 4) (Fin 4) k →ₗ[k] Matrix (Fin 4) (Fin 4) k where
  toFun X := H * X * Hᵀ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

theorem actL_apply (H X : Matrix (Fin 4) (Fin 4) k) : actL H X = H * X * Hᵀ := rfl

theorem pMap_actL (H X : Matrix (Fin 4) (Fin 4) k) : pMap k (actL H X) = actL H (pMap k X) := by
  simp only [pMap_apply, actL_apply, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem tauL_eq_trace (X : Matrix (Fin 4) (Fin 4) k) : tauL k X = (minorJ k * X).trace := by
  simp [tauL, entryL_apply, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply]
  ring

theorem tauL_actL (H X : Matrix (Fin 4) (Fin 4) k) (hH : Hᵀ * minorJ k * H = minorJ k) :
    tauL k (actL H X) = tauL k X := by
  rw [tauL_eq_trace, tauL_eq_trace, actL_apply]
  have h1 : minorJ k * (H * X * Hᵀ) = (minorJ k * H * X) * Hᵀ := by
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  have h2 : Hᵀ * (minorJ k * H * X) = (Hᵀ * minorJ k * H) * X := by
    simp only [Matrix.mul_assoc]
  rw [h2, hH]

end Action

section Invariance

variable {k : Type} [Field k] [CharP k 2] {H : Matrix (Fin 4) (Fin 4) k}

omit [CharP k 2] in
theorem actL_mem_wJ (hH2 : H * minorJ k * Hᵀ = minorJ k) {X : Matrix (Fin 4) (Fin 4) k}
    (hX : X ∈ wJ k) : actL H X ∈ wJ k := by
  obtain ⟨c, rfl⟩ := mem_wJ.mp hX
  refine mem_wJ.mpr ⟨c, ?_⟩
  rw [map_smul, actL_apply, hH2]

omit [CharP k 2] in
theorem actL_mem_symSub {X : Matrix (Fin 4) (Fin 4) k} (hX : X ∈ symSub k) :
    actL H X ∈ symSub k := by
  have h : pMap k X = 0 := hX
  show pMap k (actL H X) = 0
  rw [pMap_actL, h, map_zero]

theorem actL_mem_altSub {X : Matrix (Fin 4) (Fin 4) k} (hX : X ∈ altSub k) :
    actL H X ∈ altSub k := by
  obtain ⟨hs, hd⟩ := mem_altSub.mp hX
  have hs' := mem_symSub.mp (actL_mem_symSub (H := H) (mem_symSub.mpr hs))
  refine mem_altSub.mpr ⟨hs', fun i => ?_⟩
  rw [actL_apply, conj_diag_apply H X hs i, hd 0, hd 1, hd 2, hd 3]
  ring

theorem actL_mem_kerKap (hH : Hᵀ * minorJ k * H = minorJ k) {X : Matrix (Fin 4) (Fin 4) k}
    (hX : X ∈ kerKap k) : actL H X ∈ kerKap k := by
  obtain ⟨⟨hs, hd⟩, hk⟩ := mem_kerKap.mp hX
  have hA := mem_altSub.mp (actL_mem_altSub (H := H) (mem_altSub.mpr ⟨hs, hd⟩))
  refine mem_kerKap.mpr ⟨hA, ?_⟩
  have h := conj_alt_kappa H X hs hd hH
  rw [hk] at h
  show (H * X * Hᵀ) 1 2 = (H * X * Hᵀ) 0 3
  have h2 : (X 0 3 + X 0 3 : k) = 0 := CharTwo.add_self_eq_zero _
  rw [h2] at h
  exact (CharTwo.add_eq_zero.mp h).symm

omit [CharP k 2] in
theorem actL_mem_preJ (hH2 : H * minorJ k * Hᵀ = minorJ k) {X : Matrix (Fin 4) (Fin 4) k}
    (hX : X ∈ preJ k) : actL H X ∈ preJ k := by
  obtain ⟨c, hc⟩ := mem_preJ.mp hX
  refine mem_preJ.mpr ⟨c, ?_⟩
  have h : pMap k X = c • minorJ k := hc
  have h2 : pMap k (actL H X) = c • minorJ k := by
    rw [pMap_actL, h, map_smul]
    have : actL H (minorJ k) = minorJ k := hH2
    rw [this]
  exact h2

omit [CharP k 2] in
theorem actL_mem_kerTau (hH : Hᵀ * minorJ k * H = minorJ k) {X : Matrix (Fin 4) (Fin 4) k}
    (hX : X ∈ kerTau k) : actL H X ∈ kerTau k := by
  have h : tauL k X = 0 := hX
  show tauL k (actL H X) = 0
  rw [tauL_actL H X hH, h]

end Invariance

section Equivariance

variable {k : Type} [Field k] [CharP k 2] {H : Matrix (Fin 4) (Fin 4) k}

omit [CharP k 2] in
theorem coordL_apply (X : Matrix (Fin 4) (Fin 4) k) (q : Fin 4) :
    coordL k X q = X (minorIdx q).1 (minorIdx q).2 := rfl

omit [CharP k 2] in
theorem diagL_apply (X : Matrix (Fin 4) (Fin 4) k) (i : Fin 4) : diagL k X i = X i i := rfl

omit [CharP k 2] in
theorem eqv0 (hH2 : H * minorJ k * Hᵀ = minorJ k) {X : Matrix (Fin 4) (Fin 4) k}
    (hX : X ∈ wJ k) : entryL k 0 3 (actL H X) = entryL k 0 3 X := by
  obtain ⟨c, rfl⟩ := mem_wJ.mp hX
  have h : actL H (minorJ k) = minorJ k := hH2
  simp only [map_smul, h]

theorem eqv1 (hH2 : H * minorJ k * Hᵀ = minorJ k) {X : Matrix (Fin 4) (Fin 4) k}
    (hX : X ∈ kerKap k) : coordL k (actL H X) = (minorMap H) *ᵥ coordL k X := by
  obtain ⟨⟨hs, hd⟩, hk⟩ := mem_kerKap.mp hX
  funext q
  have hab : H (minorIdx q).1 0 * H (minorIdx q).2 3 + H (minorIdx q).1 1 * H (minorIdx q).2 2 +
      H (minorIdx q).1 2 * H (minorIdx q).2 1 + H (minorIdx q).1 3 * H (minorIdx q).2 0 = 0 := by
    have := congrFun (congrFun hH2 (minorIdx q).1) (minorIdx q).2
    rw [mul_minorJ_mul_transpose_apply] at this
    rw [this]
    exact minorJ_minorIdx q
  rw [coordL_apply, actL_apply, conj_alt_coord H X hs hd hk _ _ hab]
  simp only [Matrix.mulVec, dotProduct, coordL_apply, Fin.sum_univ_four, minorMap_apply,
    minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three]

theorem eqv2 (hH : Hᵀ * minorJ k * H = minorJ k) {X : Matrix (Fin 4) (Fin 4) k}
    (hX : X ∈ altSub k) : kapL k (actL H X) = kapL k X := by
  obtain ⟨hs, hd⟩ := mem_altSub.mp hX
  simp only [kapL, LinearMap.add_apply, entryL_apply, actL_apply]
  exact conj_alt_kappa H X hs hd hH

theorem eqv3 {X : Matrix (Fin 4) (Fin 4) k} (hX : X ∈ symSub k) :
    diagL k (actL H X) = (H.map fun x => x ^ 2) *ᵥ diagL k X := by
  have hs := mem_symSub.mp hX
  funext a
  rw [diagL_apply, actL_apply, conj_diag_apply H X hs a]
  simp only [Matrix.mulVec, dotProduct, diagL_apply, Fin.sum_univ_four, Matrix.map_apply]

omit [CharP k 2] in
theorem pairL_eq (X : Matrix (Fin 4) (Fin 4) k) : pairL k X = pMap k X 0 3 := by
  simp [pairL, pMap_apply, entryL_apply]

omit [CharP k 2] in
theorem eqv4 (hH2 : H * minorJ k * Hᵀ = minorJ k) {X : Matrix (Fin 4) (Fin 4) k}
    (hX : X ∈ preJ k) : pairL k (actL H X) = pairL k X := by
  obtain ⟨c, hc⟩ := mem_preJ.mp hX
  have h : pMap k X = c • minorJ k := hc
  have hJ : actL H (minorJ k) = minorJ k := hH2
  rw [pairL_eq, pairL_eq, pMap_actL, h, map_smul, hJ]

theorem pMap_mem_kerKap {X : Matrix (Fin 4) (Fin 4) k} (hX : X ∈ kerTau k) :
    pMap k X ∈ kerKap k := by
  have h : X 0 3 + X 3 0 + X 1 2 + X 2 1 = 0 := mem_kerTau.mp hX
  refine mem_kerKap.mpr ⟨⟨fun i j => ?_, fun i => ?_⟩, ?_⟩
  · simp only [pMap_apply, Matrix.add_apply, Matrix.transpose_apply]
    ring
  · simp only [pMap_apply, Matrix.add_apply, Matrix.transpose_apply]
    exact CharTwo.add_self_eq_zero _
  · simp only [pMap_apply, Matrix.add_apply, Matrix.transpose_apply]
    have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
    linear_combination h + (-(X 0 3 + X 3 0)) * h2

theorem eqv5 (hH2 : H * minorJ k * Hᵀ = minorJ k) {X : Matrix (Fin 4) (Fin 4) k}
    (hX : X ∈ kerTau k) : coordPL k (actL H X) = (minorMap H) *ᵥ coordPL k X := by
  have h := eqv1 hH2 (pMap_mem_kerKap hX)
  simp only [coordPL, LinearMap.comp_apply]
  rw [pMap_actL]
  exact h

omit [CharP k 2] in
theorem eqv6 (hH : Hᵀ * minorJ k * H = minorJ k) (X : Matrix (Fin 4) (Fin 4) k) :
    tauL k (actL H X) = tauL k X := tauL_actL H X hH

end Equivariance

section KerSurj

variable {k : Type} [Field k] [CharP k 2]

omit [CharP k 2] in
theorem ker0 {X : Matrix (Fin 4) (Fin 4) k} (hX : X ∈ wJ k) :
    entryL k 0 3 X = 0 ↔ X ∈ (⊥ : Submodule k (Matrix (Fin 4) (Fin 4) k)) := by
  obtain ⟨c, rfl⟩ := mem_wJ.mp hX
  have hJ03 : minorJ k 0 3 = 1 := by simp [minorJ_apply]
  simp only [Submodule.mem_bot, entryL_apply, Matrix.smul_apply, smul_eq_mul, hJ03, mul_one]
  constructor
  · intro h
    rw [h, zero_smul]
  · intro h
    have := congrFun (congrFun h 0) 3
    simpa [hJ03] using this

omit [CharP k 2] in
theorem surj0 (y : k) : ∃ X ∈ wJ k, entryL k 0 3 X = y :=
  ⟨y • minorJ k, mem_wJ.mpr ⟨y, rfl⟩, by simp [entryL_apply, minorJ_apply]⟩

theorem ker1 {X : Matrix (Fin 4) (Fin 4) k} (hX : X ∈ kerKap k) :
    coordL k X = 0 ↔ X ∈ wJ k := by
  obtain ⟨⟨hs, hd⟩, hk⟩ := mem_kerKap.mp hX
  constructor
  · intro h
    have h0 : X 0 1 = 0 := congrFun h 0
    have h1 : X 0 2 = 0 := congrFun h 1
    have h2 : X 1 3 = 0 := congrFun h 2
    have h3 : X 2 3 = 0 := congrFun h 3
    have e10 := hs 0 1
    have e20 := hs 0 2
    have e30 := hs 0 3
    have e21 := hs 1 2
    have e31 := hs 1 3
    have e32 := hs 2 3
    refine mem_wJ.mpr ⟨X 0 3, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [minorJ_apply, hd, h0, h1, h2, h3, e10, e20, e30, e21, e31, e32, hk]
  · intro h
    obtain ⟨c, rfl⟩ := mem_wJ.mp h
    funext q
    simp [coordL_apply, minorJ_minorIdx]

theorem surj1 (y : Fin 4 → k) : ∃ X ∈ kerKap k, coordL k X = y := by
  refine ⟨!![0, y 0, y 1, 0; y 0, 0, 0, y 2; y 1, 0, 0, y 3; 0, y 2, y 3, 0], ?_, ?_⟩
  · refine mem_kerKap.mpr ⟨⟨fun i j => ?_, fun i => ?_⟩, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp
    · fin_cases i <;> simp
    · simp
  · funext q
    fin_cases q <;> simp [coordL_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three]

omit [CharP k 2] in
theorem ker2 {X : Matrix (Fin 4) (Fin 4) k} (hX : X ∈ altSub k) :
    kapL k X = 0 ↔ X ∈ kerKap k := by
  rw [kerKap, Submodule.mem_inf]
  simp only [LinearMap.mem_ker]
  exact ⟨fun h => ⟨hX, h⟩, fun h => h.2⟩

theorem surj2 (y : k) : ∃ X ∈ altSub k, kapL k X = y := by
  refine ⟨!![0, 0, 0, y; 0, 0, 0, 0; 0, 0, 0, 0; y, 0, 0, 0], ?_, ?_⟩
  · refine mem_altSub.mpr ⟨fun i j => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp
    · fin_cases i <;> simp
  · simp [kapL, entryL_apply]

omit [CharP k 2] in
theorem ker3 {X : Matrix (Fin 4) (Fin 4) k} (hX : X ∈ symSub k) :
    diagL k X = 0 ↔ X ∈ altSub k := by
  rw [altSub, Submodule.mem_inf]
  simp only [LinearMap.mem_ker]
  exact ⟨fun h => ⟨hX, h⟩, fun h => h.2⟩

theorem surj3 (y : Fin 4 → k) : ∃ X ∈ symSub k, diagL k X = y := by
  refine ⟨Matrix.diagonal y, mem_symSub.mpr fun i j => ?_, ?_⟩
  · by_cases h : i = j
    · subst h
      rfl
    · simp [h, Ne.symm h]
  · funext i
    simp [diagL_apply]

omit [CharP k 2] in
theorem ker4 {X : Matrix (Fin 4) (Fin 4) k} (hX : X ∈ preJ k) :
    pairL k X = 0 ↔ X ∈ symSub k := by
  obtain ⟨c, hc⟩ := mem_preJ.mp hX
  have h : pMap k X = c • minorJ k := hc
  have hJ03 : minorJ k 0 3 = 1 := by simp [minorJ_apply]
  have hp : pairL k X = c := by
    rw [pairL_eq, h]
    simp [hJ03]
  rw [hp]
  constructor
  · intro hc0
    show pMap k X = 0
    rw [h, hc0, zero_smul]
  · intro hs
    have h0 : pMap k X = 0 := hs
    rw [h] at h0
    have := congrFun (congrFun h0 0) 3
    simpa [hJ03] using this

omit [CharP k 2] in
theorem surj4 (y : k) : ∃ X ∈ preJ k, pairL k X = y := by
  refine ⟨!![0, 0, 0, y; 0, 0, y, 0; 0, 0, 0, 0; 0, 0, 0, 0], ?_, ?_⟩
  · refine mem_preJ.mpr ⟨y, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [minorJ_apply]
  · simp [pairL, entryL_apply]

theorem ker5 {X : Matrix (Fin 4) (Fin 4) k} (hX : X ∈ kerTau k) :
    coordPL k X = 0 ↔ X ∈ preJ k := ker1 (pMap_mem_kerKap hX)

omit [CharP k 2] in
theorem surj5 (y : Fin 4 → k) : ∃ X ∈ kerTau k, coordPL k X = y := by
  refine ⟨!![0, y 0, y 1, 0; 0, 0, 0, y 2; 0, 0, 0, y 3; 0, 0, 0, 0], ?_, ?_⟩
  · exact mem_kerTau.mpr (by simp)
  · funext q
    fin_cases q <;> simp [coordPL, coordL_apply, pMap_apply, minorIdx_zero, minorIdx_one,
      minorIdx_two, minorIdx_three]

omit [CharP k 2] in
theorem ker6 {X : Matrix (Fin 4) (Fin 4) k} : tauL k X = 0 ↔ X ∈ kerTau k := Iff.rfl

omit [CharP k 2] in
theorem surj6 (y : k) : ∃ X ∈ (⊤ : Submodule k (Matrix (Fin 4) (Fin 4) k)), tauL k X = y :=
  ⟨!![0, 0, 0, y; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], Submodule.mem_top, by
    simp [tauL, entryL_apply]⟩

end KerSurj

section ChainLemmas

variable {k : Type} [Field k] [CharP k 2]

theorem wJ_le_kerKap : wJ k ≤ kerKap k := by
  intro X hX
  obtain ⟨c, rfl⟩ := mem_wJ.mp hX
  refine mem_kerKap.mpr ⟨⟨fun i j => ?_, fun i => ?_⟩, ?_⟩
  · simp only [Matrix.smul_apply, minorJ_apply, add_comm i.val j.val]
  · fin_cases i <;> simp [minorJ_apply]
  · simp [minorJ_apply]

omit [CharP k 2] in
theorem symSub_le_preJ : symSub k ≤ preJ k := by
  intro X hX
  refine mem_preJ.mpr ⟨0, ?_⟩
  have h : pMap k X = 0 := hX
  rw [zero_smul]
  exact h

theorem preJ_le_kerTau : preJ k ≤ kerTau k := by
  intro X hX
  obtain ⟨c, hc⟩ := mem_preJ.mp hX
  have h03 : X 0 3 + X 3 0 = c := by
    have := congrFun (congrFun hc 0) 3
    simpa [minorJ_apply] using this
  have h12 : X 1 2 + X 2 1 = c := by
    have := congrFun (congrFun hc 1) 2
    simpa [minorJ_apply] using this
  refine mem_kerTau.mpr ?_
  have h2 : (c + c : k) = 0 := CharTwo.add_self_eq_zero c
  linear_combination h03 + h12 + h2

end ChainLemmas

section Rep

open CFSG.QuasithinUnique.Setup.X7 (matRep)

variable {F : Type} [Field F] [CharP F 2] [Finite F] (k : Type) [Field k] [Algebra F k]
  [CharP k 2]

omit [CharP k 2] in
theorem natRepS_symp (i : ℕ) (g : antiSp F) :
    (natRepS k i g)ᵀ * minorJ k * natRepS k i g = minorJ k ∧
      natRepS k i g * minorJ k * (natRepS k i g)ᵀ = minorJ k := by
  have h := ((minorAut F ^ i) g).2
  have h1 := mem_antiSp.mp h
  have h2 := mul_minorJ_mul_transpose_of_mem h
  simp only [natRepS_apply]
  constructor
  · have := congrArg (fun M => M.map (algebraMap F k)) h1
    simpa only [Matrix.map_mul, Matrix.transpose_map, minorJ_map] using this
  · have := congrArg (fun M => M.map (algebraMap F k)) h2
    simpa only [Matrix.map_mul, Matrix.transpose_map, minorJ_map] using this

omit [CharP F 2] [Finite F] [CharP k 2] in
theorem minorMap_map {L : Type} [Field L] (f : F →+* L) (A : Matrix (Fin 4) (Fin 4) F) :
    (minorMap A).map f = minorMap (A.map f) := by
  ext a b
  simp [minorMap_apply]

omit [CharP k 2] in
theorem natRepS_add_two' (i : ℕ) (g : antiSp F) :
    natRepS k (i + 2) g = (natRepS k i g).map fun x => x ^ 2 := by
  have := Fintype.ofFinite F
  exact natRepS_add_two k i g

omit [CharP k 2] in
theorem natRepS_succ (i : ℕ) (g : antiSp F) :
    natRepS k (i + 1) g = minorMap (natRepS k i g) := by
  rw [natRepS_apply, natRepS_apply]
  have : ((minorAut F ^ (i + 1)) g) = minorHom F ((minorAut F ^ i) g) := by
    rw [pow_succ', MulAut.mul_apply]
    rfl
  rw [this, glMat_minorHom, minorMap_map]

@[expose] noncomputable def sqRep (i : ℕ) :
    Representation k (antiSp F) (Matrix (Fin 4) (Fin 4) k) where
  toFun g := actL (natRepS k i g)
  map_one' := by
    refine LinearMap.ext fun X => ?_
    simp [actL_apply]
  map_mul' g h := by
    refine LinearMap.ext fun X => ?_
    simp [actL_apply, map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

@[expose] def trivFRep : FRep k (antiSp F) := ⟨k, Representation.trivial k (antiSp F) k⟩

@[expose] noncomputable def NFRep (i : ℕ) : FRep k (antiSp F) :=
  ⟨Fin 4 → k, matRep (natRepS k i)⟩

@[expose] noncomputable def sqQ (i : ℕ) : Fin 7 → FRep k (antiSp F) :=
  ![trivFRep k, NFRep k (i + 1), trivFRep k, NFRep k (i + 2), trivFRep k, NFRep k (i + 1),
    trivFRep k]

@[expose] noncomputable def sqPhi (i : ℕ) :
    ∀ s : Fin 7, Matrix (Fin 4) (Fin 4) k →ₗ[k] (sqQ (F := F) k i s).V :=
  Fin.cons (entryL k 0 3) (Fin.cons (coordL k) (Fin.cons (kapL k) (Fin.cons (diagL k)
    (Fin.cons (pairL k) (Fin.cons (coordPL k) (Fin.cons (tauL k) finZeroElim))))))

noncomputable def sqChainData (i : ℕ) : Chain (sqRep (F := F) k i) (sqQ k i) where
  W := sqChain k
  inv := by
    intro s g x hx
    obtain ⟨hH1, hH2⟩ := natRepS_symp k i g
    show actL (natRepS k i g) x ∈ sqChain k s
    fin_cases s
    · have h0 : x = 0 := hx
      show actL (natRepS k i g) x ∈ (⊥ : Submodule k (Matrix (Fin 4) (Fin 4) k))
      rw [h0, map_zero]
      exact Submodule.zero_mem _
    · exact actL_mem_wJ hH2 hx
    · exact actL_mem_kerKap hH1 hx
    · exact actL_mem_altSub hx
    · exact actL_mem_symSub hx
    · exact actL_mem_preJ hH2 hx
    · exact actL_mem_kerTau hH1 hx
    · exact Submodule.mem_top
  bot := rfl
  top := rfl
  mono := by
    intro s
    fin_cases s
    · exact bot_le
    · exact wJ_le_kerKap
    · exact inf_le_left
    · exact inf_le_left
    · exact symSub_le_preJ
    · exact preJ_le_kerTau
    · exact le_top
  φ := sqPhi k i
  surj := by
    intro s y
    fin_cases s
    · exact surj0 (k := k) y
    · exact surj1 (k := k) y
    · exact surj2 (k := k) y
    · exact surj3 (k := k) y
    · exact surj4 (k := k) y
    · exact surj5 (k := k) y
    · exact surj6 (k := k) y
  ker := by
    intro s x hx
    fin_cases s
    · exact ker0 (k := k) hx
    · exact ker1 (k := k) hx
    · exact ker2 (k := k) hx
    · exact ker3 (k := k) hx
    · exact ker4 (k := k) hx
    · exact ker5 (k := k) hx
    · exact ker6 (k := k)
  comm := by
    intro s g x hx
    obtain ⟨hH1, hH2⟩ := natRepS_symp k i g
    fin_cases s
    · exact eqv0 hH2 hx
    · show coordL k (actL (natRepS k i g) x) =
        (CFSG.QuasithinUnique.Setup.X7.matRep (natRepS k (i + 1)) g) (coordL k x)
      rw [CFSG.QuasithinUnique.Setup.X7.matRep_apply, natRepS_succ]
      exact eqv1 hH2 hx
    · exact eqv2 hH1 hx
    · show diagL k (actL (natRepS k i g) x) =
        (CFSG.QuasithinUnique.Setup.X7.matRep (natRepS k (i + 2)) g) (diagL k x)
      rw [CFSG.QuasithinUnique.Setup.X7.matRep_apply, natRepS_add_two']
      exact eqv3 hx
    · exact eqv4 hH2 hx
    · show coordPL k (actL (natRepS k i g) x) =
        (CFSG.QuasithinUnique.Setup.X7.matRep (natRepS k (i + 1)) g) (coordPL k x)
      rw [CFSG.QuasithinUnique.Setup.X7.matRep_apply, natRepS_succ]
      exact eqv5 hH2 hx
    · exact eqv6 hH1 x

omit [CharP F 2] [Finite F] [Algebra F k] [CharP k 2] in
theorem actL_vecMulVec (H : Matrix (Fin 4) (Fin 4) k) (w v : Fin 4 → k) :
    actL H (Matrix.vecMulVec w v) = Matrix.vecMulVec (H *ᵥ w) (H *ᵥ v) := by
  rw [actL_apply, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

@[expose] noncomputable def sqEquiv (i : ℕ) :
    Representation.Equiv (tprod (matRep (natRepS (F := F) k i)) (matRep (natRepS (F := F) k i)))
      (sqRep k i) :=
  Representation.Equiv.mk (TensorProduct.piScalarRight k k (Fin 4 → k) (Fin 4)) (fun g => by
    refine TensorProduct.ext' fun v w => ?_
    simp only [LinearMap.comp_apply, tprod_apply, TensorProduct.map_tmul]
    show Matrix.vecMulVec ((natRepS k i g).mulVec w) ((natRepS k i g).mulVec v) =
      actL (natRepS k i g) (Matrix.vecMulVec w v)
    rw [actL_vecMulVec])

theorem sqFlag (i : ℕ) :
    FlagTop (sqRep (F := F) k i) [trivFRep k, NFRep k (i + 1), trivFRep k, NFRep k (i + 2),
      trivFRep k, NFRep k (i + 1), trivFRep k] := by
  have h := flagTop_of_chain 7 (sqRep (F := F) k i) (sqQ k i) (sqChainData k i)
  have hl : (List.ofFn (sqQ (F := F) k i)).reverse = [trivFRep k, NFRep k (i + 1), trivFRep k,
      NFRep k (i + 2), trivFRep k, NFRep k (i + 1), trivFRep k] := by
    simp [sqQ, List.ofFn_succ]
  rw [hl] at h
  exact h

theorem fundamental_tensor_square_filtration (i : ℕ) :
    FlagTop (tprod (matRep (natRepS (F := F) k i)) (matRep (natRepS (F := F) k i)))
      [trivFRep k, NFRep k (i + 1), trivFRep k, NFRep k (i + 2), trivFRep k, NFRep k (i + 1),
        trivFRep k] :=
  FlagTop.congr _ (sqEquiv k i).symm (sqFlag k i)

end Rep

end CFSG.QuasithinUnique.Setup.X7b
