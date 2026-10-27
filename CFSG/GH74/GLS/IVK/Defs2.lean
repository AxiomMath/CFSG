module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open scoped Matrix

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] noncomputable def glAut (σ : F ≃+* F) : GL ι F ≃* GL ι F :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := ι) σ).toMulEquiv

theorem glAut_coe (σ : F ≃+* F) (g : GL ι F) (i j : ι) :
    ((glAut σ g : GL ι F) : Matrix ι ι F) i j = σ ((g : Matrix ι ι F) i j) :=
  rfl

@[expose] def FieldStable (H : Subgroup (GL ι F)) : Prop :=
  ∀ σ : F ≃+* F, ∀ g ∈ H, glAut σ g ∈ H

@[expose] noncomputable def stableAut (H : Subgroup (GL ι F)) (hH : FieldStable H)
    (σ : F ≃+* F) : H ≃* H where
  toFun g := ⟨glAut σ g, hH σ g g.2⟩
  invFun g := ⟨glAut σ.symm g, hH σ.symm g g.2⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp [glAut_coe]
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp [glAut_coe]
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (glAut σ) (g : GL ι F) (h : GL ι F)

theorem stableAut_mem_scalars (H : Subgroup (GL ι F)) (hH : FieldStable H) (τ : F ≃+* F)
    (y : H) (hy : y ∈ (StatedScalars ι F).subgroupOf H) :
    stableAut H hH τ y ∈ (StatedScalars ι F).subgroupOf H := by
  obtain ⟨c, hc⟩ : (y : GL ι F) ∈ StatedScalars ι F := hy
  refine ⟨Units.map τ.toRingHom.toMonoidHom c, ?_⟩
  show _ = glAut τ (y : GL ι F)
  rw [← hc]
  apply Units.ext
  ext i j
  by_cases h : i = j
  · subst h
    simp [glAut_coe]
  · simp [glAut_coe, h]

@[expose] noncomputable def projAut (H : Subgroup (GL ι F)) (hH : FieldStable H)
    (σ : F ≃+* F) : StatedProj H ≃* StatedProj H :=
  QuotientGroup.congr _ _ (stableAut H hH σ) (by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact stableAut_mem_scalars H hH σ y hy
    · intro x hx
      refine ⟨(stableAut H hH σ.symm) x, stableAut_mem_scalars H hH σ.symm x hx, ?_⟩
      apply Subtype.ext
      apply Units.ext
      ext i j
      simp [stableAut, glAut_coe])

@[expose] noncomputable def fieldAutProj (H : Subgroup (GL ι F)) (hH : FieldStable H) :
    (F ≃+* F) →* MulAut (StatedProj H) where
  toFun σ := projAut H hH σ
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with | H g => ?_
    have h : stableAut H hH 1 g = g := by
      apply Subtype.ext
      apply Units.ext
      ext i j
      simp [stableAut, glAut_coe]
    show QuotientGroup.mk (stableAut H hH 1 g) = QuotientGroup.mk g
    rw [h]
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with | H g => ?_
    have h : stableAut H hH (σ * τ) g = stableAut H hH σ (stableAut H hH τ g) := by
      apply Subtype.ext
      apply Units.ext
      ext i j
      simp [stableAut, glAut_coe]
    show QuotientGroup.mk (stableAut H hH (σ * τ) g) =
      QuotientGroup.mk (stableAut H hH σ (stableAut H hH τ g))
    rw [h]

theorem fieldStable_closure (S : Set (GL ι F)) (hS : ∀ σ : F ≃+* F, ∀ g ∈ S, glAut σ g ∈ S) :
    FieldStable (Subgroup.closure S) := by
  intro σ g hg
  have : Subgroup.closure S ≤ (Subgroup.closure S).comap (glAut σ).toMonoidHom :=
    (Subgroup.closure_le _).2 (fun a ha => Subgroup.subset_closure (hS σ a ha))
  exact this hg

theorem fieldStable_statedSL (n : ℕ) : FieldStable (StatedSL n F) := by
  apply fieldStable_closure
  intro σ g hg
  show ((glAut σ g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1
  have h : ((glAut σ g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (σ : F →+* F).mapMatrix (g : Matrix (Fin n) (Fin n) F) := rfl
  rw [h, ← RingHom.map_det, hg, map_one]

theorem fieldStable_statedSU (n q : ℕ) : FieldStable (StatedSU n q F) := by
  apply fieldStable_closure
  intro σ g hg
  obtain ⟨hdet, hform⟩ := hg
  refine ⟨?_, ?_⟩
  · have h : ((glAut σ g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (σ : F →+* F).mapMatrix (g : Matrix (Fin n) (Fin n) F) := rfl
    rw [h, ← RingHom.map_det, hdet, map_one]
  · have h : ((glAut σ g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (σ : F →+* F).mapMatrix (g : Matrix (Fin n) (Fin n) F) := rfl
    rw [h]
    have h2 : (((σ : F →+* F).mapMatrix (g : Matrix (Fin n) (Fin n) F)).map (· ^ q))ᵀ *
        (σ : F →+* F).mapMatrix (g : Matrix (Fin n) (Fin n) F) =
        (σ : F →+* F).mapMatrix
          (((g : Matrix (Fin n) (Fin n) F).map (· ^ q))ᵀ * (g : Matrix (Fin n) (Fin n) F)) := by
      ext i j
      simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_mul, map_pow]
    rw [h2, hform, map_one]

@[expose] def symplJ (n : ℕ) (F : Type) [Field F] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem fieldStable_statedSp (n : ℕ) : FieldStable (StatedSp n F) := by
  apply fieldStable_closure
  intro σ g hg
  have h : ((glAut σ g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (σ : F →+* F).mapMatrix (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := rfl
  have hg' : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * symplJ n F *
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = symplJ n F := hg
  show ((glAut σ g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ *
      symplJ n F * ((glAut σ g : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = symplJ n F
  rw [h]
  have hJ : (σ : F →+* F).mapMatrix (symplJ n F) = symplJ n F := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [symplJ, Matrix.fromBlocks, Matrix.one_apply, Matrix.neg_apply, apply_ite]
  have h2 : ((σ : F →+* F).mapMatrix (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))ᵀ *
      symplJ n F * (σ : F →+* F).mapMatrix
        (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (σ : F →+* F).mapMatrix ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ *
        symplJ n F * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) := by
    rw [map_mul, map_mul, hJ, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      Matrix.transpose_map]
  rw [h2, hg', hJ]

end Generic

section Models

variable {F : Type} [Field F]

@[expose] noncomputable def fieldAutSubOf {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι F)) (hH : FieldStable H) {K : Type} [Group K] (e : K ≃* StatedProj H) :
    Subgroup (MulAut K) :=
  (fieldAutProj H hH).range.comap (MulAut.congr e).toMonoidHom

@[expose] def IsSLnEps (n : ℕ) (X : Type) [Group X] (ε : ℤ) (q : ℕ) : Prop :=
  (ε = 1 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      Nonempty (X ≃* StatedSL n F)) ∨
  (ε = -1 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ^ 2 ∧
      Nonempty (X ≃* StatedSU n q F))

@[expose] def IsLnEps (n : ℕ) (K : Type) [Group K] (ε : ℤ) (q : ℕ) : Prop :=
  (ε = 1 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      Nonempty (K ≃* StatedProj (StatedSL n F))) ∨
  (ε = -1 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ^ 2 ∧
      Nonempty (K ≃* StatedProj (StatedSU n q F)))

@[expose] def IsPSp4 (K : Type) [Group K] (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (K ≃* StatedProj (StatedSp 2 F))

@[expose] def IsSp4L4U4 (K : Type) [Group K] (q : ℕ) : Prop :=
  IsPSp4 K q ∨ (q % 4 = 3 ∧ IsLnEps 4 K 1 q) ∨ (q % 4 = 1 ∧ IsLnEps 4 K (-1) q)

end Models

end CFSG.GH74.GLS.IVK
