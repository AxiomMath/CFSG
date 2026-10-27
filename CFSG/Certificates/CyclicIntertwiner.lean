module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public noncomputable section

namespace CFSG.Certificates

open Matrix

variable {K : Type*} [Field K] {d r : ℕ}

@[expose] def cyclicMatrix (P : Fin d → Matrix (Fin d) (Fin d) K) (v : Fin d → K) :
    Matrix (Fin d) (Fin d) K :=
  Matrix.of fun a j => (P j *ᵥ v) a

@[expose] def intertwinerSubmodule (A B : Fin r → Matrix (Fin d) (Fin d) K) :
    Submodule K (Matrix (Fin d) (Fin d) K) where
  carrier := {F | ∀ i, F * A i = B i * F}
  add_mem' := by
    intro F G hF hG i
    rw [add_mul, mul_add, hF i, hG i]
  zero_mem' := by
    intro i
    rw [zero_mul, mul_zero]
  smul_mem' := by
    intro c F hF i
    rw [smul_mul_assoc, mul_smul_comm, hF i]

@[expose] def intertwinerRelation (A B : Fin r → Matrix (Fin d) (Fin d) K)
    (P Q : Fin d → Matrix (Fin d) (Fin d) K) (v : Fin d → K) (i : Fin r) (j : Fin d) :
    Matrix (Fin d) (Fin d) K :=
  ∑ k, ((cyclicMatrix P v)⁻¹ * A i * cyclicMatrix P v) k j • Q k - B i * Q j

@[expose] def relationKernel (R : Fin r → Fin d → Matrix (Fin d) (Fin d) K)
    (E : Set (Fin r × Fin d)) : Submodule K (Fin d → K) :=
  ⨅ e ∈ E, LinearMap.ker (R e.1 e.2).mulVecLin

@[expose] def parentWordMatrix (A : Fin r → Matrix (Fin d) (Fin d) K) (p : Fin d → Fin d)
    (ℓ : Fin d → Fin r) (hp : ∀ j : Fin d, 0 < j.val → (p j).val < j.val) (j : Fin d) :
    Matrix (Fin d) (Fin d) K :=
  if h : j.val = 0 then 1
  else
    have : (p j).val < j.val := hp j (Nat.pos_of_ne_zero h)
    A (ℓ j) * parentWordMatrix A p ℓ hp (p j)
termination_by j.val

structure IsParentWordFamily (A : Fin r → Matrix (Fin d) (Fin d) K) (p : Fin d → Fin d)
    (ℓ : Fin d → Fin r) (P : Fin d → Matrix (Fin d) (Fin d) K) : Prop where
  parent_lt : ∀ j : Fin d, 0 < j.val → (p j).val < j.val
  root : ∀ j : Fin d, j.val = 0 → P j = 1
  succ : ∀ j : Fin d, 0 < j.val → P j = A (ℓ j) * P (p j)

theorem parentWordMatrix_isParentWordFamily (A : Fin r → Matrix (Fin d) (Fin d) K)
    (p : Fin d → Fin d) (ℓ : Fin d → Fin r) (hp : ∀ j : Fin d, 0 < j.val → (p j).val < j.val) :
    IsParentWordFamily A p ℓ (parentWordMatrix A p ℓ hp) where
  parent_lt := hp
  root j hj := by rw [parentWordMatrix, dite_eq_left hj]
  succ j hj := by rw [parentWordMatrix, dite_eq_right (Nat.pos_iff_ne_zero.1 hj)]

theorem mem_intertwinerSubmodule (A B : Fin r → Matrix (Fin d) (Fin d) K)
    (F : Matrix (Fin d) (Fin d) K) : F ∈ intertwinerSubmodule A B ↔ ∀ i, F * A i = B i * F :=
  Iff.rfl

theorem mem_relationKernel (R : Fin r → Fin d → Matrix (Fin d) (Fin d) K)
    (E : Set (Fin r × Fin d)) (y : Fin d → K) :
    y ∈ relationKernel R E ↔ ∀ e ∈ E, R e.1 e.2 *ᵥ y = 0 := by
  simp [relationKernel, Submodule.mem_iInf]

theorem mul_cyclicMatrix (X : Matrix (Fin d) (Fin d) K) (P : Fin d → Matrix (Fin d) (Fin d) K)
    (v : Fin d → K) : X * cyclicMatrix P v = cyclicMatrix (fun j => X * P j) v := by
  ext a j
  rw [cyclicMatrix, cyclicMatrix, Matrix.of_apply, ← Matrix.mulVec_mulVec, Matrix.mul_apply]
  simp only [Matrix.of_apply, Matrix.mulVec, dotProduct]

theorem cyclicMatrix_mul_apply (P : Fin d → Matrix (Fin d) (Fin d) K) (v : Fin d → K)
    (M : Matrix (Fin d) (Fin d) K) (a j : Fin d) :
    (cyclicMatrix P v * M) a j = (∑ k, M k j • (P k *ᵥ v)) a := by
  simp [cyclicMatrix, Matrix.mul_apply, Finset.sum_apply, mul_comm]

theorem cyclicMatrix_col (P : Fin d → Matrix (Fin d) (Fin d) K) (v : Fin d → K) (j : Fin d) :
    (fun a => cyclicMatrix P v a j) = P j *ᵥ v := rfl

theorem cyclicMatrix_congr {P P' : Fin d → Matrix (Fin d) (Fin d) K} {v v' : Fin d → K}
    (h : ∀ j, P j *ᵥ v = P' j *ᵥ v') : cyclicMatrix P v = cyclicMatrix P' v' := by
  ext a j
  exact congrFun (h j) a

section family

variable {A B : Fin r → Matrix (Fin d) (Fin d) K} {p : Fin d → Fin d} {ℓ : Fin d → Fin r}
  {P Q : Fin d → Matrix (Fin d) (Fin d) K} {v : Fin d → K}

theorem IsParentWordFamily.intertwine (hP : IsParentWordFamily A p ℓ P)
    (hQ : IsParentWordFamily B p ℓ Q) {F : Matrix (Fin d) (Fin d) K}
    (hF : F ∈ intertwinerSubmodule A B) (j : Fin d) : F * P j = Q j * F := by
  have all : ∀ a : ℕ, ∀ j : Fin d, j.val = a → F * P j = Q j * F := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja
      rcases Nat.eq_zero_or_pos j.val with h0 | hpos
      · rw [hP.root j h0, hQ.root j h0, mul_one, one_mul]
      · rw [hP.succ j hpos, hQ.succ j hpos, ← mul_assoc, hF (ℓ j), mul_assoc,
          ih (p j).val (hja ▸ hP.parent_lt j hpos) (p j) rfl, mul_assoc]
  exact all j.val j rfl

theorem cancel_cyclicMatrix (hC : IsUnit (cyclicMatrix P v)) {X Y : Matrix (Fin d) (Fin d) K}
    (h : X * cyclicMatrix P v = Y * cyclicMatrix P v) : X = Y := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hC
  calc X = X * cyclicMatrix P v * (cyclicMatrix P v)⁻¹ := by
        rw [mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
    _ = Y * cyclicMatrix P v * (cyclicMatrix P v)⁻¹ := by rw [h]
    _ = Y := by rw [mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]

theorem cyclicMatrix_coordinate_identity (hC : IsUnit (cyclicMatrix P v)) (i : Fin r)
    (j : Fin d) : A i *ᵥ (P j *ᵥ v) =
      ∑ k, ((cyclicMatrix P v)⁻¹ * A i * cyclicMatrix P v) k j • (P k *ᵥ v) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hC
  have hCM : cyclicMatrix P v * ((cyclicMatrix P v)⁻¹ * A i * cyclicMatrix P v) =
      A i * cyclicMatrix P v := by
    rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hdet, one_mul]
  ext a
  rw [← cyclicMatrix_mul_apply, hCM, mul_cyclicMatrix, Matrix.mulVec_mulVec]
  rfl

theorem intertwinerRelation_mulVec (i : Fin r) (j : Fin d) (y : Fin d → K) :
    intertwinerRelation A B P Q v i j *ᵥ y =
      ∑ k, ((cyclicMatrix P v)⁻¹ * A i * cyclicMatrix P v) k j • (Q k *ᵥ y) -
        B i *ᵥ (Q j *ᵥ y) := by
  rw [intertwinerRelation, Matrix.sub_mulVec, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec]
  simp only [Matrix.smul_mulVec]

theorem intertwinerRelation_mulVec_eval (hP : IsParentWordFamily A p ℓ P)
    (hQ : IsParentWordFamily B p ℓ Q) (hC : IsUnit (cyclicMatrix P v))
    {F : Matrix (Fin d) (Fin d) K} (hF : F ∈ intertwinerSubmodule A B) (i : Fin r) (j : Fin d) :
    intertwinerRelation A B P Q v i j *ᵥ (F *ᵥ v) = 0 := by
  have hQF : ∀ k, Q k *ᵥ (F *ᵥ v) = F *ᵥ (P k *ᵥ v) := fun k => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP.intertwine hQ hF k]
  have key : ∑ k, ((cyclicMatrix P v)⁻¹ * A i * cyclicMatrix P v) k j • (F *ᵥ (P k *ᵥ v)) =
      F *ᵥ (A i *ᵥ (P j *ᵥ v)) := by
    rw [cyclicMatrix_coordinate_identity hC i j, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
  rw [intertwinerRelation_mulVec, sub_eq_zero]
  simp only [hQF]
  rw [key, Matrix.mulVec_mulVec, hF i, ← Matrix.mulVec_mulVec]

theorem eval_mem_relationKernel (hP : IsParentWordFamily A p ℓ P)
    (hQ : IsParentWordFamily B p ℓ Q) (hC : IsUnit (cyclicMatrix P v))
    {F : Matrix (Fin d) (Fin d) K} (hF : F ∈ intertwinerSubmodule A B) (E : Set (Fin r × Fin d)) :
    F *ᵥ v ∈ relationKernel (intertwinerRelation A B P Q v) E :=
  (mem_relationKernel _ E _).2 fun e _ => intertwinerRelation_mulVec_eval hP hQ hC hF e.1 e.2

theorem intertwiner_mul_cyclicMatrix (hP : IsParentWordFamily A p ℓ P)
    (hQ : IsParentWordFamily B p ℓ Q) {F : Matrix (Fin d) (Fin d) K}
    (hF : F ∈ intertwinerSubmodule A B) :
    F * cyclicMatrix P v = cyclicMatrix Q (F *ᵥ v) := by
  rw [mul_cyclicMatrix]
  apply cyclicMatrix_congr
  intro j
  rw [hP.intertwine hQ hF j, Matrix.mulVec_mulVec]

theorem intertwiner_eq_zero_of_eval (hP : IsParentWordFamily A p ℓ P)
    (hQ : IsParentWordFamily B p ℓ Q) (hC : IsUnit (cyclicMatrix P v))
    {F : Matrix (Fin d) (Fin d) K} (hF : F ∈ intertwinerSubmodule A B) (h0 : F *ᵥ v = 0) :
    F = 0 := by
  apply cancel_cyclicMatrix hC
  rw [intertwiner_mul_cyclicMatrix hP hQ hF, h0, zero_mul]
  ext a j
  simp [cyclicMatrix]

theorem intertwiner_reconstruct (hP : IsParentWordFamily A p ℓ P)
    (hQ : IsParentWordFamily B p ℓ Q) (hC : IsUnit (cyclicMatrix P v))
    {F : Matrix (Fin d) (Fin d) K} (hF : F ∈ intertwinerSubmodule A B) :
    cyclicMatrix Q (F *ᵥ v) * (cyclicMatrix P v)⁻¹ = F := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hC
  rw [← intertwiner_mul_cyclicMatrix hP hQ hF, mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]

theorem intertwiner_of_relationKernel (hP : IsParentWordFamily A p ℓ P)
    (hQ : IsParentWordFamily B p ℓ Q) (hC : IsUnit (cyclicMatrix P v)) {y : Fin d → K}
    (hy : y ∈ relationKernel (intertwinerRelation A B P Q v) Set.univ) :
    cyclicMatrix Q y * (cyclicMatrix P v)⁻¹ ∈ intertwinerSubmodule A B ∧
      (cyclicMatrix Q y * (cyclicMatrix P v)⁻¹) *ᵥ v = y := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hC
  have hGC : cyclicMatrix Q y * (cyclicMatrix P v)⁻¹ * cyclicMatrix P v = cyclicMatrix Q y := by
    rw [mul_assoc, Matrix.nonsing_inv_mul _ hdet, mul_one]
  have hR := (mem_relationKernel _ _ _).1 hy
  constructor
  · intro i
    apply cancel_cyclicMatrix hC
    have hCM : cyclicMatrix P v * ((cyclicMatrix P v)⁻¹ * A i * cyclicMatrix P v) =
        A i * cyclicMatrix P v := by
      rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hdet, one_mul]
    have hL : cyclicMatrix Q y * (cyclicMatrix P v)⁻¹ * A i * cyclicMatrix P v =
        cyclicMatrix Q y * ((cyclicMatrix P v)⁻¹ * A i * cyclicMatrix P v) := by
      rw [mul_assoc, ← hCM, ← mul_assoc, hGC]
    have hR' : B i * (cyclicMatrix Q y * (cyclicMatrix P v)⁻¹) * cyclicMatrix P v =
        B i * cyclicMatrix Q y := by
      rw [mul_assoc, hGC]
    rw [hL, hR', mul_cyclicMatrix (B i) Q y]
    ext a j
    have hRij := hR (i, j) (Set.mem_univ _)
    rw [intertwinerRelation_mulVec, sub_eq_zero] at hRij
    rw [cyclicMatrix_mul_apply, hRij, Matrix.mulVec_mulVec]
    rfl
  · rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      funext a
      exact a.elim0
    · let z : Fin d := ⟨0, hd⟩
      have hz : (fun a => (cyclicMatrix Q y * (cyclicMatrix P v)⁻¹ * cyclicMatrix P v) a z) =
          fun a => cyclicMatrix Q y a z := by rw [hGC]
      rw [mul_cyclicMatrix, cyclicMatrix_col, cyclicMatrix_col, hP.root z rfl, hQ.root z rfl,
        mul_one, Matrix.one_mulVec] at hz
      exact hz

@[expose] def intertwinerEval (hP : IsParentWordFamily A p ℓ P)
    (hQ : IsParentWordFamily B p ℓ Q) (hC : IsUnit (cyclicMatrix P v))
    (E : Set (Fin r × Fin d)) :
    intertwinerSubmodule A B →ₗ[K] relationKernel (intertwinerRelation A B P Q v) E where
  toFun F := ⟨F.1 *ᵥ v, eval_mem_relationKernel hP hQ hC F.2 E⟩
  map_add' F G := Subtype.ext (Matrix.add_mulVec F.1 G.1 v)
  map_smul' c F := Subtype.ext (Matrix.smul_mulVec c F.1 v)

theorem intertwinerEval_injective (hP : IsParentWordFamily A p ℓ P)
    (hQ : IsParentWordFamily B p ℓ Q) (hC : IsUnit (cyclicMatrix P v))
    (E : Set (Fin r × Fin d)) : Function.Injective (intertwinerEval hP hQ hC E) :=
  (injective_iff_map_eq_zero _).2 fun F hF =>
    Subtype.ext (intertwiner_eq_zero_of_eval hP hQ hC F.2 (congrArg Subtype.val hF))

theorem intertwinerEval_surjective (hP : IsParentWordFamily A p ℓ P)
    (hQ : IsParentWordFamily B p ℓ Q) (hC : IsUnit (cyclicMatrix P v)) :
    Function.Surjective (intertwinerEval hP hQ hC Set.univ) := by
  intro y
  obtain ⟨hmem, heval⟩ := intertwiner_of_relationKernel hP hQ hC y.2
  exact ⟨⟨_, hmem⟩, Subtype.ext heval⟩

@[expose] def intertwinerEvalEquiv (hP : IsParentWordFamily A p ℓ P)
    (hQ : IsParentWordFamily B p ℓ Q) (hC : IsUnit (cyclicMatrix P v)) :
    intertwinerSubmodule A B ≃ₗ[K] relationKernel (intertwinerRelation A B P Q v) Set.univ :=
  LinearEquiv.ofBijective (intertwinerEval hP hQ hC Set.univ)
    ⟨intertwinerEval_injective hP hQ hC Set.univ, intertwinerEval_surjective hP hQ hC⟩

theorem intertwinerEvalEquiv_symm_apply (hP : IsParentWordFamily A p ℓ P)
    (hQ : IsParentWordFamily B p ℓ Q) (hC : IsUnit (cyclicMatrix P v))
    (y : relationKernel (intertwinerRelation A B P Q v) Set.univ) :
    ((intertwinerEvalEquiv hP hQ hC).symm y : Matrix (Fin d) (Fin d) K) =
      cyclicMatrix Q y * (cyclicMatrix P v)⁻¹ := by
  obtain ⟨hmem, heval⟩ := intertwiner_of_relationKernel hP hQ hC y.2
  have hy : (intertwinerEvalEquiv hP hQ hC).symm y = ⟨_, hmem⟩ :=
    (LinearEquiv.symm_apply_eq _).2 (Subtype.ext heval.symm)
  rw [hy]

theorem intertwinerSubmodule_eq_scalars (hP : IsParentWordFamily A p ℓ P)
    (hC : IsUnit (cyclicMatrix P v)) (E : Set (Fin r × Fin d))
    (hE : Module.finrank K (relationKernel (intertwinerRelation A A P P v) E) = 1) :
    (intertwinerSubmodule A A : Set (Matrix (Fin d) (Fin d) K)) =
      Set.range fun c : K => c • (1 : Matrix (Fin d) (Fin d) K) := by
  have hone : (1 : Matrix (Fin d) (Fin d) K) ∈ intertwinerSubmodule A A := fun i => by
    rw [one_mul, mul_one]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    ext F
    exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun ⟨c, hc⟩ => hc ▸ Submodule.smul_mem _ c hone⟩
  · have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have hle : K ∙ (1 : Matrix (Fin d) (Fin d) K) ≤ intertwinerSubmodule A A :=
      (Submodule.span_singleton_le_iff_mem _ _).2 hone
    have hbound : Module.finrank K (intertwinerSubmodule A A) ≤ 1 :=
      hE ▸ LinearMap.finrank_le_finrank_of_injective (intertwinerEval_injective hP hP hC E)
    have heq : K ∙ (1 : Matrix (Fin d) (Fin d) K) = intertwinerSubmodule A A :=
      Submodule.eq_of_le_of_finrank_le hle
        (by rw [finrank_span_singleton one_ne_zero]; exact hbound)
    ext F
    rw [SetLike.mem_coe, ← heq, Submodule.mem_span_singleton, Set.mem_range]

end family

theorem cyclic_intertwiner_relation_bound (A B : Fin r → Matrix (Fin d) (Fin d) K)
    (v : Fin d → K) (p : Fin d → Fin d) (ℓ : Fin d → Fin r)
    (hp : ∀ j : Fin d, 0 < j.val → (p j).val < j.val)
    (hC : IsUnit (cyclicMatrix (parentWordMatrix A p ℓ hp) v)) :
    (∀ E : Set (Fin r × Fin d), ∃ f : intertwinerSubmodule A B →ₗ[K]
        relationKernel (intertwinerRelation A B (parentWordMatrix A p ℓ hp)
          (parentWordMatrix B p ℓ hp) v) E,
        Function.Injective f ∧ ∀ F, (f F : Fin d → K) = (F : Matrix (Fin d) (Fin d) K) *ᵥ v) ∧
    (∀ E : Set (Fin r × Fin d), Module.finrank K (intertwinerSubmodule A B) ≤
      Module.finrank K (relationKernel (intertwinerRelation A B (parentWordMatrix A p ℓ hp)
        (parentWordMatrix B p ℓ hp) v) E)) ∧
    (∃ e : intertwinerSubmodule A B ≃ₗ[K] relationKernel (intertwinerRelation A B
        (parentWordMatrix A p ℓ hp) (parentWordMatrix B p ℓ hp) v) Set.univ,
      (∀ F, (e F : Fin d → K) = (F : Matrix (Fin d) (Fin d) K) *ᵥ v) ∧
      ∀ y, (e.symm y : Matrix (Fin d) (Fin d) K) =
        cyclicMatrix (parentWordMatrix B p ℓ hp) y *
          (cyclicMatrix (parentWordMatrix A p ℓ hp) v)⁻¹) ∧
    ((∀ i, B i = A i) → ∀ E : Set (Fin r × Fin d),
      Module.finrank K (relationKernel (intertwinerRelation A B (parentWordMatrix A p ℓ hp)
        (parentWordMatrix B p ℓ hp) v) E) = 1 →
      (intertwinerSubmodule A B : Set (Matrix (Fin d) (Fin d) K)) =
        Set.range fun c : K => c • (1 : Matrix (Fin d) (Fin d) K)) := by
  have hP := parentWordMatrix_isParentWordFamily A p ℓ hp
  have hQ := parentWordMatrix_isParentWordFamily B p ℓ hp
  refine ⟨fun E => ⟨intertwinerEval hP hQ hC E, intertwinerEval_injective hP hQ hC E,
      fun _ => rfl⟩,
    fun E => LinearMap.finrank_le_finrank_of_injective (intertwinerEval_injective hP hQ hC E),
    ⟨intertwinerEvalEquiv hP hQ hC, fun _ => rfl, intertwinerEvalEquiv_symm_apply hP hQ hC⟩,
    fun hBA E hE => ?_⟩
  obtain rfl : B = A := funext hBA
  exact intertwinerSubmodule_eq_scalars hP hC E hE

end CFSG.Certificates
