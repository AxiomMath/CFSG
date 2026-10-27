module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Perm
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.HardMathSupport.Timmesfeld.LinearRank

open Matrix Equiv CFSG.SectionRank.OddCover CFSG.HardMathSupport.Timmesfeld.Tables.Census

variable {K : Type} [Field K] {n : ℕ}

@[expose] def permAct (n : ℕ) (K : Type) [Field K] : Perm (Fin n) →* MulAut (Fin n → Kˣ) where
  toFun σ :=
    { toFun := fun d i => d (σ.symm i)
      invFun := fun d i => d (σ i)
      left_inv := fun d => by funext i; simp
      right_inv := fun d => by funext i; simp
      map_mul' := fun a b => by funext i; rfl }
  map_one' := by ext d i; rfl
  map_mul' a b := by ext d i; rfl

theorem permAct_apply (σ : Perm (Fin n)) (d : Fin n → Kˣ) (i : Fin n) :
    permAct n K σ d i = d (σ.symm i) := rfl

abbrev MonoGroup (n : ℕ) (K : Type) [Field K] : Type := (Fin n → Kˣ) ⋊[permAct n K] Perm (Fin n)

theorem permGL_mul_diagHom_mul_inv (σ : Perm (Fin n)) (d : Fin n → Kˣ) :
    permGL n K σ * diagHom n d * (permGL n K σ)⁻¹ = diagHom n (permAct n K σ d) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagHom, coe_diagHom]
  have h1 : (((permGL n K σ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = σ.permMatrix K := by
    rw [← map_inv, coe_permGL, inv_inv]
  rw [h1, coe_permGL]
  ext i j
  simp only [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.diagonal_apply,
    permAct_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, mul_ite, mul_zero,
    ite_mul, zero_mul, one_mul, mul_one]
  rw [Finset.sum_eq_single (σ⁻¹ i)]
  · by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · intro x _ hx
    have hx' : ¬ (σ.symm i = x) := fun h => hx h.symm
    simp [hx']
  · simp

@[expose] noncomputable def monoHom (n : ℕ) (K : Type) [Field K] : MonoGroup n K →* GL (Fin n) K :=
  SemidirectProduct.lift (diagHom n) (permGL n K) fun σ => by
    refine MonoidHom.ext fun d => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (permGL_mul_diagHom_mul_inv σ d).symm

theorem monoHom_inl (d : Fin n → Kˣ) : monoHom n K (SemidirectProduct.inl d) = diagHom n d :=
  SemidirectProduct.lift_inl _ _ _ d

theorem monoHom_inr (σ : Perm (Fin n)) : monoHom n K (SemidirectProduct.inr σ) = permGL n K σ :=
  SemidirectProduct.lift_inr _ _ _ σ

theorem monoHom_apply (x : MonoGroup n K) :
    monoHom n K x = diagHom n x.left * permGL n K x.right := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul, monoHom_inl, monoHom_inr]

theorem right_eq_one_of_scalar {x : MonoGroup n K} {c : Kˣ}
    (h : monoHom n K x = Matrix.GeneralLinearGroup.scalar (Fin n) c) : x.right = 1 := by
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, x.right i ≠ i := by
    by_contra hall
    push Not at hall
    exact hne (Equiv.ext hall)
  rw [monoHom_apply] at h
  have h1 := congrArg
    (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) (x.right i) i) h
  simp only [Units.val_mul, coe_diagHom, coe_permGL, Matrix.diagonal_mul,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hi] at h1
  simp [Perm.permMatrix, PEquiv.toMatrix_apply] at h1

theorem monoHom_injective : Function.Injective (monoHom n K) := by
  intro x y hxy
  have h1 : monoHom n K (x⁻¹ * y) = Matrix.GeneralLinearGroup.scalar (Fin n) 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel, map_one]
  have h2 := right_eq_one_of_scalar h1
  have h3 : x⁻¹ * y = SemidirectProduct.inl (x⁻¹ * y).left := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right (x⁻¹ * y), h2, map_one, mul_one]
  rw [h3, monoHom_inl] at h1
  have h4 : (x⁻¹ * y).left = 1 := by
    apply diagHom_injective n
    rw [h1, map_one]
    ext i j
    simp [Matrix.one_apply]
  rw [h4, map_one] at h3
  exact inv_mul_eq_one.mp h3

theorem card_monoGroup [Finite K] :
    Nat.card (MonoGroup n K) = Nat.card Kˣ ^ n * n.factorial := by
  rw [SemidirectProduct.card, Nat.card_pi, Nat.card_perm]
  simp

theorem diagHom_const (c : Kˣ) :
    diagHom n (fun _ => c) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  apply Units.ext
  rw [coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar]
  rfl

theorem diagHom_eq_scalar_iff {d : Fin n → Kˣ} {c : Kˣ} :
    diagHom n d = Matrix.GeneralLinearGroup.scalar (Fin n) c ↔ ∀ i, d i = c := by
  constructor
  · intro h i
    have h1 := congrArg
      (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i i) h
    simp only [coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h1
    exact Units.ext (by simpa using h1)
  · intro h
    rw [← diagHom_const]
    congr 1
    funext i
    exact h i

end CFSG.HardMathSupport.Timmesfeld.LinearRank
