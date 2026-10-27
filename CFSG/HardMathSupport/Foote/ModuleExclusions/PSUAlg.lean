module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.StatedDefs

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open Matrix CFSG.Open

section Form

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] (fb : K →+* K)

@[expose] def uCj (x : ι → K) : ι → K := fun i => fb (x i)

@[expose] def uHh (x y : ι → K) : K := uCj fb x ⬝ᵥ y

theorem uCj_smul (c : K) (x : ι → K) : uCj fb (c • x) = fb c • uCj fb x := by
  funext i; simp [uCj]

theorem uCj_add (x y : ι → K) : uCj fb (x + y) = uCj fb x + uCj fb y := by
  funext i; simp [uCj]

theorem uHh_swap (hfb : ∀ x, fb (fb x) = x) (x y : ι → K) :
    uHh fb x y = fb (uHh fb y x) := by
  simp only [uHh, uCj, dotProduct, map_sum, map_mul, hfb]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem uHh_smul_left (c : K) (x y : ι → K) : uHh fb (c • x) y = fb c * uHh fb x y := by
  simp [uHh, uCj_smul, smul_dotProduct]

theorem uHh_smul_right (c : K) (x y : ι → K) : uHh fb x (c • y) = c * uHh fb x y := by
  simp [uHh, dotProduct_smul]

theorem uHh_add_left (x y z : ι → K) : uHh fb (x + y) z = uHh fb x z + uHh fb y z := by
  simp [uHh, uCj_add, add_dotProduct]

theorem uHh_add_right (x y z : ι → K) : uHh fb x (y + z) = uHh fb x y + uHh fb x z := by
  simp [uHh, dotProduct_add]

theorem uHh_eq_zero_of_forall {x : ι → K} (h : ∀ y, uHh fb x y = 0) : x = 0 := by
  funext i
  have := h (Pi.single i 1)
  simp only [uHh, uCj, dotProduct_single, mul_one] at this
  have h2 : fb (x i) = 0 := by simpa [dotProduct, Pi.single_apply] using this
  simpa using (map_eq_zero_iff fb (RingHom.injective fb)).mp h2

theorem uCj_mulVec (A : Matrix ι ι K) (x : ι → K) :
    uCj fb (A *ᵥ x) = (A.map fb) *ᵥ uCj fb x := by
  funext i
  simp [uCj, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem uHh_mulVec_left (A : Matrix ι ι K) (x y : ι → K) :
    uHh fb (A *ᵥ x) y = uHh fb x ((A.map fb)ᵀ *ᵥ y) := by
  rw [uHh, uCj_mulVec, uHh]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem uHh_unitary {U : Matrix ι ι K} (hU : (U.map fb)ᵀ * U = 1) (x y : ι → K) :
    uHh fb (U *ᵥ x) (U *ᵥ y) = uHh fb x y := by
  rw [uHh_mulVec_left, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

theorem uCj_mulVec_vecMul {U : Matrix ι ι K} (hU : (U.map fb)ᵀ * U = 1) (b : ι → K) :
    uCj fb (U *ᵥ b) ᵥ* U = uCj fb b := by
  rw [uCj_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hU, Matrix.vecMul_one]

@[expose] def uX (a b : ι → K) (α : K) : Matrix ι ι K :=
  α • vecMulVec a (uCj fb b) - fb α • vecMulVec b (uCj fb a)

theorem uX_add (a b : ι → K) (α β : K) : uX fb a b (α + β) = uX fb a b α + uX fb a b β := by
  simp only [uX, map_add, add_smul]
  abel

theorem uX_mul_fixed (a b : ι → K) {r : K} (hr : fb r = r) (γ : K) :
    uX fb a b (r * γ) = r • uX fb a b γ := by
  simp only [uX, map_mul, hr, mul_smul, smul_sub]

theorem uX_mulVec (a b : ι → K) (α : K) (x : ι → K) :
    uX fb a b α *ᵥ x = (α * uHh fb b x) • a - (fb α * uHh fb a x) • b := by
  simp only [uX, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul]
  rfl

theorem uX_mul_uX (a b a' b' : ι → K) (α β : K) :
    uX fb a b α * uX fb a' b' β =
      (α * β * uHh fb b a') • vecMulVec a (uCj fb b') -
      (α * fb β * uHh fb b b') • vecMulVec a (uCj fb a') -
      (fb α * β * uHh fb a a') • vecMulVec b (uCj fb b') +
      (fb α * fb β * uHh fb a b') • vecMulVec b (uCj fb a') := by
  simp only [uX, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_vecMulVec, uHh, smul_smul]
  module

theorem uX_mul (a b : ι → K) (haa : uHh fb a a = 0) (hab : uHh fb a b = 0)
    (hba : uHh fb b a = 0) (hbb : uHh fb b b = 0) (α β : K) :
    uX fb a b α * uX fb a b β = 0 := by
  rw [uX_mul_uX, hbb, hba, haa, hab]
  simp

theorem uX_adj (hfb : ∀ x, fb (fb x) = x) (a b : ι → K) (α : K) :
    ((uX fb a b α).map fb)ᵀ = -uX fb a b α := by
  ext i j
  simp only [uX, uCj, Matrix.transpose_apply, Matrix.map_apply, Matrix.sub_apply,
    Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, map_sub, map_mul, hfb, Matrix.neg_apply]
  ring

theorem uX_unitary (hfb : ∀ x, fb (fb x) = x) (a b : ι → K) (haa : uHh fb a a = 0)
    (hab : uHh fb a b = 0) (hba : uHh fb b a = 0) (hbb : uHh fb b b = 0) (γ : K) :
    (((1 : Matrix ι ι K) + uX fb a b γ).map fb)ᵀ * (1 + uX fb a b γ) = 1 := by
  have hXX := uX_mul fb a b haa hab hba hbb γ γ
  rw [Matrix.map_add fb (map_add fb), Matrix.map_one fb (map_zero fb) (map_one fb),
    Matrix.transpose_add, Matrix.transpose_one, uX_adj fb hfb]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul,
    hXX]
  abel

theorem uX_eq_zero {a b : ι → K} (hli : LinearIndependent K ![a, b]) {α : K}
    (h : uX fb a b α = 0) : α = 0 := by
  rw [LinearIndependent.pair_iff] at hli
  have hb : b ≠ 0 := by
    intro h0
    have := hli 0 1 (by simp [h0])
    exact one_ne_zero this.2
  obtain ⟨x, hx⟩ : ∃ x, uHh fb b x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hb (uHh_eq_zero_of_forall fb hcon)
  have h1 := congrArg (fun N : Matrix ι ι K => N *ᵥ x) h
  simp only [uX_mulVec, Matrix.zero_mulVec] at h1
  have h2 := hli (α * uHh fb b x) (-(fb α * uHh fb a x)) (by
    rw [neg_smul, ← sub_eq_add_neg]
    exact h1)
  exact (mul_eq_zero.mp h2.1).resolve_right hx

theorem uX_smul_smul (hfb : ∀ x, fb (fb x) = x) (a b : ι → K) {r t : K} (h : r * fb t = -1)
    (α : K) : uX fb (r • a) (t • b) α = -uX fb a b α := by
  have h' : fb r * t = -1 := by
    have := congrArg fb h
    rw [map_mul, hfb, map_neg, map_one] at this
    exact this
  simp only [uX, uCj_smul, vecMulVec_smul, smul_vecMulVec, smul_smul, smul_sub]
  have e1 : α * (fb t * r) = -α := by rw [mul_comm (fb t), h]; ring
  have e2 : fb α * (fb r * t) = -fb α := by rw [h']; ring
  rw [e1, e2]
  module

theorem mul_uX {U : Matrix ι ι K} (hU : (U.map fb)ᵀ * U = 1) (a b : ι → K) (α : K) :
    U * uX fb a b α = uX fb (U *ᵥ a) (U *ᵥ b) α * U := by
  have h1 : ∀ x y : ι → K, U * vecMulVec x (uCj fb y) =
      vecMulVec (U *ᵥ x) (uCj fb (U *ᵥ y)) * U := by
    intro x y
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, uCj_mulVec_vecMul fb hU]
  simp only [uX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h1]

theorem uX_anticomm (hfb : ∀ x, fb (fb x) = x) {U : Matrix ι ι K} (hU : (U.map fb)ᵀ * U = 1)
    {a b : ι → K} {ε₁ ε₂ : K} (ha : U *ᵥ a = ε₁ • a) (hb : U *ᵥ b = ε₂ • b)
    (h : ε₁ * fb ε₂ = -1) (α : K) : U * uX fb a b α = -(uX fb a b α * U) := by
  rw [mul_uX fb hU, ha, hb, uX_smul_smul fb hfb a b h, Matrix.neg_mul]

end Form

section Heis

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] (fb : K →+* K)

@[expose] def uZ (u : ι → K) : Matrix ι ι K := vecMulVec u (uCj fb u)

@[expose] def uCc (w : ι → K) (α β : K) : K := -(α * fb β * uHh fb w w)

@[expose] def uE (u w : ι → K) (α : K) : Matrix ι ι K :=
  1 + uX fb u w α + (2⁻¹ * uCc fb w α α) • uZ fb u

theorem adj_add (N P : Matrix ι ι K) : ((N + P).map fb)ᵀ = (N.map fb)ᵀ + (P.map fb)ᵀ := by
  ext i j; simp

theorem adj_smul (c : K) (N : Matrix ι ι K) : ((c • N).map fb)ᵀ = fb c • (N.map fb)ᵀ := by
  ext i j; simp

theorem adj_one : ((1 : Matrix ι ι K).map fb)ᵀ = 1 := by
  ext i j
  simp [Matrix.one_apply, eq_comm]

omit [DecidableEq ι] in
theorem uX_zero (a b : ι → K) : uX fb a b 0 = 0 := by simp [uX]

omit [DecidableEq ι] in
theorem uX_neg (a b : ι → K) (α : K) : uX fb a b (-α) = -uX fb a b α := by
  simp only [uX, map_neg, neg_smul]
  abel

variable {fb} {u w : ι → K} (huu : uHh fb u u = 0) (huw : uHh fb u w = 0) (hwu : uHh fb w u = 0)

include huu huw hwu in
theorem uX_mul_uX_heis (α β : K) : uX fb u w α * uX fb u w β = uCc fb w α β • uZ fb u := by
  rw [uX_mul_uX, huu, huw, hwu]
  simp [uCc, uZ, uHh]

include huu huw hwu in
theorem uZ_mul_uX (α : K) : uZ fb u * uX fb u w α = 0 := by
  simp only [uZ, uX, Matrix.mul_sub, Matrix.mul_smul, vecMulVec_mul_vecMulVec]
  have h1 : uCj fb u ⬝ᵥ u = 0 := huu
  have h2 : uCj fb u ⬝ᵥ w = 0 := huw
  simp [h1, h2]

include huu huw hwu in
theorem uX_mul_uZ (α : K) : uX fb u w α * uZ fb u = 0 := by
  simp only [uZ, uX, Matrix.sub_mul, Matrix.smul_mul, vecMulVec_mul_vecMulVec]
  have h1 : uCj fb u ⬝ᵥ u = 0 := huu
  have h2 : uCj fb w ⬝ᵥ u = 0 := hwu
  simp [h1, h2]

include huu in
theorem uZ_mul_uZ : uZ fb u * uZ fb u = 0 := by
  simp only [uZ, vecMulVec_mul_vecMulVec]
  have h1 : uCj fb u ⬝ᵥ u = 0 := huu
  simp [h1]

include huu huw hwu in
theorem uE_mul (α β : K) : uE fb u w α * uE fb u w β =
    1 + uX fb u w (α + β) +
      (2⁻¹ * uCc fb w α α + 2⁻¹ * uCc fb w β β + uCc fb w α β) • uZ fb u := by
  have hAB := uX_mul_uX_heis huu huw hwu α β
  have hZB := uZ_mul_uX huu huw hwu β
  have hAZ := uX_mul_uZ huu huw hwu α
  have hZZ := uZ_mul_uZ huu
  simp only [uE, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, hAB, hZB, hAZ, hZZ, smul_zero, add_zero, uX_add, add_smul]
  module

include huu huw hwu in
theorem uE_mul_neg (h2 : (2 : K) ≠ 0) (α : K) : uE fb u w α * uE fb u w (-α) = 1 := by
  rw [uE_mul huu huw hwu, add_neg_cancel, uX_zero]
  have h22 : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have : 2⁻¹ * uCc fb w α α + 2⁻¹ * uCc fb w (-α) (-α) + uCc fb w α (-α) = 0 := by
    simp only [uCc, map_neg]
    linear_combination (-(α * fb α * uHh fb w w)) * h22
  rw [this]
  simp

include huu huw hwu in
theorem uE_mul_sub (h2 : (2 : K) ≠ 0) (α β : K) : uE fb u w α * uE fb u w β =
    uE fb u w (α + β) + (2⁻¹ * (uCc fb w α β - uCc fb w β α)) • uZ fb u := by
  rw [uE_mul huu huw hwu]
  have h22 : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have : 2⁻¹ * uCc fb w α α + 2⁻¹ * uCc fb w β β + uCc fb w α β =
      2⁻¹ * uCc fb w (α + β) (α + β) + 2⁻¹ * (uCc fb w α β - uCc fb w β α) := by
    simp only [uCc, map_add]
    linear_combination (α * fb β * uHh fb w w) * h22
  rw [this]
  simp only [uE, add_assoc, add_smul]

include huu huw hwu in
theorem uE_mul_of_comm (h2 : (2 : K) ≠ 0) {α β : K} (h : α * fb β = β * fb α) :
    uE fb u w α * uE fb u w β = uE fb u w (α + β) := by
  rw [uE_mul_sub huu huw hwu h2]
  have : uCc fb w α β - uCc fb w β α = 0 := by
    simp only [uCc]
    linear_combination (-(uHh fb w w)) * h
  rw [this]
  simp

include huu huw hwu in
theorem uZ_mul_uE (α : K) : uZ fb u * uE fb u w α = uZ fb u := by
  simp only [uE, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, uZ_mul_uX huu huw hwu,
    uZ_mul_uZ huu]
  simp

include huu huw hwu in
theorem uE_mul_uZ (α : K) : uE fb u w α * uZ fb u = uZ fb u := by
  simp only [uE, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, uX_mul_uZ huu huw hwu,
    uZ_mul_uZ huu]
  simp

include huu huw hwu in
theorem eq_zero_of_uE_eq_scalar (hu0 : u ≠ 0) (hww : uHh fb w w ≠ 0) {α s : K}
    (h : uE fb u w α = s • (1 : Matrix ι ι K)) : α = 0 := by
  have hAu : uX fb u w α *ᵥ u = 0 := by
    rw [uX_mulVec, hwu, huu]
    simp
  have hZu : uZ fb u *ᵥ u = 0 := by
    have h1 : uCj fb u ⬝ᵥ u = 0 := huu
    simp [uZ, Matrix.vecMulVec_mulVec, h1]
  have hZw : uZ fb u *ᵥ w = 0 := by
    have h1 : uCj fb u ⬝ᵥ w = 0 := huw
    simp [uZ, Matrix.vecMulVec_mulVec, h1]
  have hAw : uX fb u w α *ᵥ w = (α * uHh fb w w) • u := by
    rw [uX_mulVec, huw]
    simp
  have e1 := congrArg (fun N : Matrix ι ι K => N *ᵥ u) h
  simp only [uE, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAu, hZu,
    smul_zero, add_zero] at e1
  have hs : s = 1 := by
    have : (1 - s) • u = 0 := by rw [sub_smul, one_smul]; exact sub_eq_zero.mpr e1
    have := (smul_eq_zero.mp this).resolve_right hu0
    linear_combination -this
  have e2 := congrArg (fun N : Matrix ι ι K => N *ᵥ w) h
  simp only [uE, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAw, hZw,
    smul_zero, add_zero, hs, one_smul] at e2
  have : (α * uHh fb w w) • u = 0 := by
    have := e2
    rw [add_eq_left] at this
    exact this
  have := (smul_eq_zero.mp this).resolve_right hu0
  exact (mul_eq_zero.mp this).resolve_right hww

theorem uZ_adj (hfb : ∀ x, fb (fb x) = x) (u : ι → K) : ((uZ fb u).map fb)ᵀ = uZ fb u := by
  ext i j
  simp [uZ, uCj, vecMulVec_apply, hfb, mul_comm]

include huu huw hwu in
theorem uE_adj (hfb : ∀ x, fb (fb x) = x) (α : K) : ((uE fb u w α).map fb)ᵀ = uE fb u w (-α) := by
  have hκ : fb (uHh fb w w) = uHh fb w w := (uHh_swap fb hfb w w).symm
  have hs : fb (2⁻¹ * uCc fb w α α) = 2⁻¹ * uCc fb w α α := by
    simp only [uCc, map_mul, map_neg, map_inv₀, hκ, hfb, map_ofNat]
    ring
  have hs' : uCc fb w (-α) (-α) = uCc fb w α α := by
    simp only [uCc, map_neg]
    ring
  have e1 : ((uX fb u w α).map fb)ᵀ = -uX fb u w α := uX_adj fb hfb u w α
  have e2 : ((uZ fb u).map fb)ᵀ = uZ fb u := uZ_adj hfb u
  simp only [uE, adj_add, adj_one, adj_smul, e1, uX_neg, hs', e2, hs]

include huu huw hwu in
theorem uE_unitary (h2 : (2 : K) ≠ 0) (hfb : ∀ x, fb (fb x) = x) (α : K) :
    ((uE fb u w α).map fb)ᵀ * uE fb u w α = 1 := by
  rw [uE_adj huu huw hwu hfb]
  have := uE_mul_neg huu huw hwu h2 (-α)
  rwa [neg_neg] at this

include huu huw hwu in
theorem uE_anticomm_Z {U : Matrix ι ι K} (hU : (U.map fb)ᵀ * U = 1) {ε : K}
    (hu : U *ᵥ u = ε • u) (hε : ε * fb ε = 1) : U * uZ fb u = uZ fb u * U := by
  have h1 : U * vecMulVec u (uCj fb u) = vecMulVec (U *ᵥ u) (uCj fb (U *ᵥ u)) * U := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, uCj_mulVec_vecMul fb hU]
  have hε' : fb ε * ε = 1 := by rw [mul_comm]; exact hε
  simp only [uZ, h1, hu, uCj_smul, vecMulVec_smul, smul_vecMulVec, smul_smul, hε', one_smul]

end Heis


section Eigen

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] (fb : K →+* K)

theorem uHh_eigen_zero {U : Matrix ι ι K} (hU : (U.map fb)ᵀ * U = 1) {ε ε' : K}
    {x y : ι → K} (hx : U *ᵥ x = ε • x) (hy : U *ᵥ y = ε' • y) (h : fb ε * ε' ≠ 1) :
    uHh fb x y = 0 := by
  have h1 := uHh_unitary fb hU x y
  rw [hx, hy, uHh_smul_left, uHh_smul_right] at h1
  have : (fb ε * ε' - 1) * uHh fb x y = 0 := by linear_combination h1
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h)

theorem li_of_eigen {M : Matrix ι ι K} {ε₁ ε₂ : K} (hne : ε₂ - ε₁ ≠ 0)
    {a b : ι → K} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : M *ᵥ a = ε₁ • a)
    (hb : M *ᵥ b = ε₂ • b) : LinearIndependent K ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun v => M *ᵥ v) hst
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ha, hb, Matrix.mulVec_zero] at h1
  have h3 : ((ε₂ - ε₁) * s) • a = 0 := by
    have e : ((ε₂ - ε₁) * s) • a =
        ε₂ • (s • a + t • b) - (s • ε₁ • a + t • ε₂ • b) := by module
    rw [e, hst, h1]
    simp
  have hs : s = 0 := by
    have := (smul_eq_zero.mp h3).resolve_right ha0
    exact (mul_eq_zero.mp this).resolve_left hne
  rw [hs, zero_smul, zero_add] at hst
  exact ⟨hs, (smul_eq_zero.mp hst).resolve_right hb0⟩

end Eigen

section Finite

variable {K : Type} [Field K]

theorem unitary_of_mem_statedSU (fb : K →+* K) {n q : ℕ} (hfbq : ∀ x : K, fb x = x ^ q)
    {A : GL (Fin n) K} (hA : A ∈ StatedSU n q K) :
    (((A : Matrix (Fin n) (Fin n) K).map fb)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1) ∧
      (A : Matrix (Fin n) (Fin n) K).det = 1 := by
  have e : (fun x : K => x ^ q) = ⇑fb := funext fun x => (hfbq x).symm
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h1, h2⟩ := hx
    rw [e] at h2
    exact ⟨h2, h1⟩
  | one => simp
  | mul x y _ _ hx hy =>
    refine ⟨?_, by simp [Matrix.det_mul, hx.2, hy.2]⟩
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    calc ((y : Matrix (Fin n) (Fin n) K).map fb)ᵀ * ((x : Matrix (Fin n) (Fin n) K).map fb)ᵀ *
        (↑x * ↑y) = ((y : Matrix (Fin n) (Fin n) K).map fb)ᵀ *
          (((x : Matrix (Fin n) (Fin n) K).map fb)ᵀ * ↑x) * ↑y := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hx.1, Matrix.mul_one, hy.1]
  | inv x _ hx =>
    refine ⟨?_, by simp [Matrix.coe_units_inv, Matrix.det_nonsing_inv, hx.2]⟩
    set B : Matrix (Fin n) (Fin n) K := ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hB
    have h1 : (↑x : Matrix (Fin n) (Fin n) K) * B = 1 := Units.mul_inv x
    calc (B.map fb)ᵀ * B = (B.map fb)ᵀ * (((x : Matrix (Fin n) (Fin n) K).map fb)ᵀ * ↑x) * B := by
          rw [hx.1, Matrix.mul_one]
      _ = (((x : Matrix (Fin n) (Fin n) K) * B).map fb)ᵀ * (↑x * B) := by
          simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h1]; simp

variable [Finite K]

theorem exists_not_fixed {q : ℕ} (hq : 1 < q) (hK : Nat.card K = q ^ 2) : ∃ s : K, s ^ q ≠ s := by
  by_contra h
  push Not at h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have h5 : g ^ q = g := Units.ext (h g)
  have h4 : g ^ (q - 1) = 1 := by
    have : g * g ^ (q - 1) = g * 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega), h5, mul_one]
    exact mul_left_cancel this
  have hd := orderOf_dvd_of_pow_eq_one h4
  rw [hord] at hd
  have := Nat.le_of_dvd (by omega) hd
  have h3 : q ^ 2 = q * q := sq q
  have h6 : q * q ≥ 2 * q := Nat.mul_le_mul_right q hq
  omega

theorem exists_pow_succ_eq {q : ℕ} (hq : 1 < q) (hK : Nat.card K = q ^ 2) {γ : K} (hγ : γ ≠ 0)
    (hγq : γ ^ q = γ) : ∃ s : K, s ^ (q + 1) = γ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 γ hγ))
  have hγ1 : γ ^ (q - 1) = 1 := by
    have : γ * γ ^ (q - 1) = γ * 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega), hγq, mul_one]
    exact mul_left_cancel₀ hγ this
  have h4 : g ^ (k * ((q - 1 : ℕ) : ℤ)) = 1 := by
    rw [_root_.zpow_mul, hk]
    apply Units.ext
    simpa using hγ1
  have hdvd : ((q ^ 2 - 1 : ℕ) : ℤ) ∣ k * ((q - 1 : ℕ) : ℤ) := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr h4
    rw [hord] at h
    exact h
  have e1 : ((q ^ 2 - 1 : ℕ) : ℤ) = ((q - 1 : ℕ) : ℤ) * ((q + 1 : ℕ) : ℤ) := by
    have : 1 ≤ q := by omega
    push_cast [Nat.cast_sub this, Nat.cast_sub hq2]
    ring
  rw [e1, mul_comm k] at hdvd
  have hq1 : ((q - 1 : ℕ) : ℤ) ≠ 0 := by
    have : q - 1 ≠ 0 := by omega
    exact_mod_cast this
  obtain ⟨j, hj⟩ := (mul_dvd_mul_iff_left hq1).mp hdvd
  refine ⟨((g ^ j : Kˣ) : K), ?_⟩
  have e2 : ((g ^ j : Kˣ) : K) ^ (q + 1) = (((g ^ j) ^ (q + 1) : Kˣ) : K) := by simp
  have e3 : (g ^ j) ^ (q + 1) = g ^ k := by
    rw [← zpow_natCast, ← _root_.zpow_mul, hj, mul_comm]
  rw [e2, e3, hk]
  rfl

theorem exists_isotropic_in_plane {ι : Type} [Fintype ι] [DecidableEq ι] (fb : K →+* K) {q : ℕ}
    (hq : 1 < q) (hK : Nat.card K = q ^ 2) (hfb : ∀ x, fb (fb x) = x)
    (hfbq : ∀ x : K, fb x = x ^ q) {x₁ x₂ : ι → K} (hli : LinearIndependent K ![x₁, x₂]) :
    ∃ s₁ s₂ : K, s₁ • x₁ + s₂ • x₂ ≠ 0 ∧
      uHh fb (s₁ • x₁ + s₂ • x₂) (s₁ • x₁ + s₂ • x₂) = 0 := by
  have hli' := LinearIndependent.pair_iff.mp hli
  by_contra hno
  push Not at hno
  have hne : ∀ s₁ s₂ : K, (s₁ ≠ 0 ∨ s₂ ≠ 0) → s₁ • x₁ + s₂ • x₂ ≠ 0 := by
    intro s₁ s₂ hs h0
    have := hli' s₁ s₂ h0
    rcases hs with hs | hs
    · exact hs this.1
    · exact hs this.2
  have ha : uHh fb x₁ x₁ ≠ 0 := by
    have := hno 1 0 (by simpa using hne 1 0 (Or.inl one_ne_zero))
    simpa using this
  set α := uHh fb x₁ x₁ with hα
  have hαfix : fb α = α := (uHh_swap fb hfb x₁ x₁).symm
  set lam : K := uHh fb x₁ x₂ / α with hlam
  set e₂ : ι → K := x₂ + (-lam) • x₁ with he₂
  have he₂span : e₂ = (-lam) • x₁ + (1 : K) • x₂ := by rw [he₂, one_smul, add_comm]
  have he₂ne : e₂ ≠ 0 := by rw [he₂span]; exact hne (-lam) 1 (Or.inr one_ne_zero)
  have hx₁e₂ : uHh fb x₁ e₂ = 0 := by
    rw [he₂, uHh_add_right, uHh_smul_right, hlam, neg_mul, div_mul_cancel₀ _ ha]
    ring
  have he₂x₁ : uHh fb e₂ x₁ = 0 := by rw [uHh_swap fb hfb, hx₁e₂, map_zero]
  have hβ : uHh fb e₂ e₂ ≠ 0 := by
    have := hno (-lam) 1 (by rw [← he₂span]; exact he₂ne)
    rwa [← he₂span] at this
  set β := uHh fb e₂ e₂ with hβdef
  have hβfix : fb β = β := (uHh_swap fb hfb e₂ e₂).symm
  set γ : K := -α / β with hγ
  have hγ0 : γ ≠ 0 := div_ne_zero (neg_ne_zero.mpr ha) hβ
  have hγfix : fb γ = γ := by rw [hγ, map_div₀, map_neg, hαfix, hβfix]
  have hγq : γ ^ q = γ := by rw [← hfbq, hγfix]
  obtain ⟨s, hs⟩ := exists_pow_succ_eq hq hK hγ0 hγq
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hs
    exact hγ0 hs.symm
  have hamem : x₁ + s • e₂ = (1 + s * (-lam)) • x₁ + s • x₂ := by
    rw [he₂, smul_add, smul_smul]
    module
  have hz := hno (1 + s * (-lam)) s (Or.inr hs0 |> hne _ _)
  rw [← hamem] at hz
  apply hz
  rw [uHh_add_left, uHh_add_right, uHh_add_right, uHh_smul_left, uHh_smul_left,
    uHh_smul_right, uHh_smul_right, hx₁e₂, he₂x₁, hfbq s]
  have : s ^ q * s = γ := by rw [← pow_succ]; exact hs
  have h1 : uHh fb x₁ x₁ + γ * uHh fb e₂ e₂ = 0 := by
    rw [hγ, div_mul_cancel₀ _ hβ]
    ring
  linear_combination h1 + (uHh fb e₂ e₂) * this

end Finite

end CFSG.HardMathSupport.Foote.ModuleExclusions
