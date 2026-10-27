module

public import CFSG.Assembly.LowTwoRankDefs

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Matrix
open scoped commutatorElement

namespace OrthogonalBlocks

variable {K : Type} [Field K]

section BlockDiag

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  {G : Type*} [Group G]

@[expose] def blockDiagHom (α : G →* GL m K) (β : G →* GL n K) : G →* GL (m ⊕ n) K where
  toFun g := ⟨fromBlocks (α g : Matrix m m K) 0 0 (β g : Matrix n n K),
    fromBlocks (α g⁻¹ : Matrix m m K) 0 0 (β g⁻¹ : Matrix n n K),
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp [fromBlocks_multiply])

theorem coe_blockDiagHom (α : G →* GL m K) (β : G →* GL n K) (g : G) :
    (blockDiagHom α β g : Matrix (m ⊕ n) (m ⊕ n) K) =
      fromBlocks (α g : Matrix m m K) 0 0 (β g : Matrix n n K) :=
  rfl

end BlockDiag

section InvTranspose

variable {m : Type} [Fintype m] [DecidableEq m]

@[expose] def invTranspose : GL m K →* GL m K where
  toFun A := ⟨((A⁻¹ : GL m K) : Matrix m m K)ᵀ, (A : Matrix m m K)ᵀ,
    by rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one],
    by rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' A B := Units.ext (by
    change (((A * B)⁻¹ : GL m K) : Matrix m m K)ᵀ =
      ((A⁻¹ : GL m K) : Matrix m m K)ᵀ * ((B⁻¹ : GL m K) : Matrix m m K)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul])

theorem coe_invTranspose (A : GL m K) :
    (invTranspose A : Matrix m m K) = ((A⁻¹ : GL m K) : Matrix m m K)ᵀ :=
  rfl

theorem mulVec_dotProduct_invTranspose (A : GL m K) (x z : m → K) :
    ((A : Matrix m m K) *ᵥ x) ⬝ᵥ ((invTranspose A : Matrix m m K) *ᵥ z) = x ⬝ᵥ z := by
  rw [← vecMul_transpose (A : Matrix m m K) x, ← dotProduct_mulVec, mulVec_mulVec,
    coe_invTranspose, ← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    transpose_one, one_mulVec]

end InvTranspose

structure HypForm (r : ℕ) (M : Type) [Fintype M] [DecidableEq M] (K : Type) [Field K] where
  P : Matrix (Fin r) M K
  P' : Matrix M (Fin r) K
  mul_P' : P * P' = 1
  σ : GL (Fin r) K →* GL M K
  P_mul_σ : ∀ A : GL (Fin r) K,
    P * (σ A : Matrix M M K) = (invTranspose A : Matrix (Fin r) (Fin r) K) * P
  q : (M → K) → K
  q_σ : ∀ (A : GL (Fin r) K) (u : M → K), q ((σ A : Matrix M M K) *ᵥ u) = q u

namespace HypForm

variable {r : ℕ} {M : Type} [Fintype M] [DecidableEq M] (F : HypForm r M K)

@[expose] def Q (v : Fin r ⊕ M → K) : K :=
  (v ∘ Sum.inl) ⬝ᵥ (F.P *ᵥ (v ∘ Sum.inr)) + F.q (v ∘ Sum.inr)

@[expose] def rho : GL (Fin r) K →* GL (Fin r ⊕ M) K :=
  blockDiagHom (MonoidHom.id _) F.σ

theorem coe_rho (A : GL (Fin r) K) :
    (F.rho A : Matrix (Fin r ⊕ M) (Fin r ⊕ M) K) =
      fromBlocks (A : Matrix (Fin r) (Fin r) K) 0 0 (F.σ A : Matrix M M K) :=
  rfl

theorem rho_isometry (A : GL (Fin r) K) (v : Fin r ⊕ M → K) :
    F.Q ((F.rho A : Matrix (Fin r ⊕ M) (Fin r ⊕ M) K) *ᵥ v) = F.Q v := by
  simp only [Q, coe_rho, fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
    Sum.elim_comp_inl, Sum.elim_comp_inr, F.q_σ]
  rw [mulVec_mulVec, F.P_mul_σ, ← mulVec_mulVec, mulVec_dotProduct_invTranspose]

@[expose] def tau (B : Matrix (Fin r) (Fin r) K) : GL (Fin r ⊕ M) K :=
  ⟨fromBlocks 1 (B * F.P) 0 1, fromBlocks 1 (-(B * F.P)) 0 1,
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩

theorem coe_tau (B : Matrix (Fin r) (Fin r) K) :
    (F.tau B : Matrix (Fin r ⊕ M) (Fin r ⊕ M) K) = fromBlocks 1 (B * F.P) 0 1 :=
  rfl

theorem tau_mul (B C : Matrix (Fin r) (Fin r) K) : F.tau B * F.tau C = F.tau (B + C) :=
  Units.ext (by
    rw [Units.val_mul, coe_tau, coe_tau, coe_tau, fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, Matrix.add_mul, add_comm (B * F.P)])

theorem tau_zero : F.tau 0 = 1 :=
  Units.ext (by rw [coe_tau, Matrix.zero_mul, Units.val_one, fromBlocks_one])

theorem tau_inv (B : Matrix (Fin r) (Fin r) K) : (F.tau B)⁻¹ = F.tau (-B) :=
  (eq_inv_of_mul_eq_one_left (by rw [tau_mul, neg_add_cancel, tau_zero])).symm

theorem tau_isometry {B : Matrix (Fin r) (Fin r) K} (hB : ∀ z, (B *ᵥ z) ⬝ᵥ z = 0)
    (v : Fin r ⊕ M → K) :
    F.Q ((F.tau B : Matrix (Fin r ⊕ M) (Fin r ⊕ M) K) *ᵥ v) = F.Q v := by
  simp only [Q, coe_tau, fromBlocks_mulVec, one_mulVec, Matrix.zero_mulVec, zero_add,
    Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [← mulVec_mulVec, add_dotProduct, hB, add_zero]

theorem tau_mulVec_inl (B : Matrix (Fin r) (Fin r) K) (x : Fin r → K) :
    (F.tau B : Matrix (Fin r ⊕ M) (Fin r ⊕ M) K) *ᵥ Sum.elim x 0 = Sum.elim x 0 := by
  simp [coe_tau, fromBlocks_mulVec]

theorem rho_tau_conj (A : GL (Fin r) K) (B : Matrix (Fin r) (Fin r) K) :
    F.rho A * F.tau B * (F.rho A)⁻¹ =
      F.tau ((A : Matrix (Fin r) (Fin r) K) * B * (A : Matrix (Fin r) (Fin r) K)ᵀ) := by
  have h1 : (A : Matrix (Fin r) (Fin r) K) * ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : (F.σ A : Matrix M M K) * (F.σ A⁻¹ : Matrix M M K) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h3 : F.P * (F.σ A⁻¹ : Matrix M M K) = (A : Matrix (Fin r) (Fin r) K)ᵀ * F.P := by
    rw [F.P_mul_σ, coe_invTranspose, inv_inv]
  rw [← map_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_rho, coe_rho, coe_tau, coe_tau, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h1, h2]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h3, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_assoc (A : Matrix (Fin r) (Fin r) K) B]

theorem commutator_rho_tau (A : GL (Fin r) K) (B : Matrix (Fin r) (Fin r) K) :
    ⁅F.rho A, F.tau B⁆ =
      F.tau ((A : Matrix (Fin r) (Fin r) K) * B * (A : Matrix (Fin r) (Fin r) K)ᵀ - B) := by
  rw [commutatorElement_def, F.rho_tau_conj, F.tau_inv, F.tau_mul, sub_eq_add_neg]

theorem tau_injective : Function.Injective F.tau := fun B C h => by
  have h' := congrArg (fun g : GL (Fin r ⊕ M) K => (g : Matrix (Fin r ⊕ M) (Fin r ⊕ M) K)) h
  simp only [coe_tau] at h'
  have hBC : B * F.P = C * F.P := (fromBlocks_inj.1 h').2.1
  calc B = B * F.P * F.P' := by rw [Matrix.mul_assoc, F.mul_P', Matrix.mul_one]
    _ = C * F.P * F.P' := by rw [hBC]
    _ = C := by rw [Matrix.mul_assoc, F.mul_P', Matrix.mul_one]

@[expose] def tail (r : ℕ) (W : Type) [Fintype W] [DecidableEq W] (qW : (W → K) → K) :
    HypForm r (Fin r ⊕ W) K where
  P := fromCols 1 0
  P' := fromRows 1 0
  mul_P' := by rw [fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero]
  σ := blockDiagHom invTranspose 1
  P_mul_σ A := by
    rw [coe_blockDiagHom, fromCols_mul_fromBlocks, mul_fromCols]
    simp
  q u := qW (u ∘ Sum.inr)
  q_σ A u := by simp [coe_blockDiagHom, fromBlocks_mulVec]

@[expose] def plus (r : ℕ) : HypForm r (Fin r) K where
  P := 1
  P' := 1
  mul_P' := Matrix.one_mul 1
  σ := invTranspose
  P_mul_σ A := by rw [Matrix.one_mul, Matrix.mul_one]
  q _ := 0
  q_σ _ _ := rfl

end HypForm

end OrthogonalBlocks

end CFSG.ComponentClassification.UnbalancingLocal
