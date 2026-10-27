module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import Mathlib.LinearAlgebra.Matrix.Permutation

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix

variable (n : ℕ) (K : Type*) [Field K]

@[expose] def flagSpace (i : ℕ) : Submodule K (Fin n → K) :=
  Submodule.span K ((fun j : Fin n => (Pi.single j (1 : K) : Fin n → K)) '' {j | (j : ℕ) < i})

variable {n K}

theorem mem_flagSpace {i : ℕ} {v : Fin n → K} :
    v ∈ flagSpace n K i ↔ ∀ j : Fin n, i ≤ (j : ℕ) → v j = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      intro j hj
      have hkj : k ≠ j := fun h => by
        subst h
        exact absurd hk (not_lt.mpr hj)
      simp [hkj.symm]
    | zero => intro j _; rfl
    | add x y _ _ hx hy => intro j hj; simp [hx j hj, hy j hj]
    | smul c x _ hx => intro j hj; simp [hx j hj]
  · intro hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < i
    · have : (Pi.single j (v j) : Fin n → K) = v j • Pi.single j 1 := by
        ext k
        rcases eq_or_ne k j with rfl | h <;> simp [*]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [hv j (not_lt.mp hj), Pi.single_zero]
      exact Submodule.zero_mem _

variable (n K)

@[simp]
theorem flagSpace_zero : flagSpace n K 0 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  funext j
  exact mem_flagSpace.mp hv j (Nat.zero_le _)

variable {n K}

theorem mul_apply_self_of_isUpperTriangular {M N : Matrix (Fin n) (Fin n) K}
    (hM : M.IsUpperTriangular) (hN : N.IsUpperTriangular) (i : Fin n) :
    (M * N) i i = M i i * N i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coe_inv_isUpperTriangular {A : SpecialLinearGroup (Fin n) K}
    (hA : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular) :
    ((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).IsUpperTriangular := by
  have h : (A : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  have := Matrix.invertibleOfIsUnitDet (A : Matrix (Fin n) (Fin n) K)
    (by rw [A.prop]; exact isUnit_one)
  rw [← Matrix.inv_eq_right_inv h]
  exact blockTriangular_inv_of_blockTriangular hA

theorem coe_inv_mul_coe (A : SpecialLinearGroup (Fin n) K) :
    ((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (A : Matrix (Fin n) (Fin n) K) = 1 := by
  have h : (A : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  exact mul_eq_one_comm.mp h

theorem coe_inv_apply_self_of_isUpperTriangular {A : SpecialLinearGroup (Fin n) K}
    (hA : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular) (i : Fin n) :
    (A : Matrix (Fin n) (Fin n) K) i i *
      ((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i i = 1 := by
  have h : (A : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  rw [← mul_apply_self_of_isUpperTriangular hA (coe_inv_isUpperTriangular hA), h, one_apply_eq]

variable (n K)

@[expose] def upperTriangular : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {A | ∀ i j : Fin n, j < i → (A : Matrix (Fin n) (Fin n) K) i j = 0}
  one_mem' := fun i j hij => by
    rw [SpecialLinearGroup.coe_one, one_apply_ne (ne_of_gt hij)]
  mul_mem' := fun {A B} hA hB i j hij => by
    have hA' : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun _ _ h => hA _ _ h
    have hB' : (B : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun _ _ h => hB _ _ h
    rw [SpecialLinearGroup.coe_mul]
    exact BlockTriangular.mul hA' hB' hij
  inv_mem' := fun {A} hA i j hij => by
    have hA' : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun _ _ h => hA _ _ h
    exact coe_inv_isUpperTriangular hA' hij

variable {n K}

theorem mem_upperTriangular {A : SpecialLinearGroup (Fin n) K} :
    A ∈ upperTriangular n K ↔ ∀ i j : Fin n, j < i → (A : Matrix (Fin n) (Fin n) K) i j = 0 :=
  Iff.rfl

theorem mem_upperTriangular_iff_isUpperTriangular {A : SpecialLinearGroup (Fin n) K} :
    A ∈ upperTriangular n K ↔ (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
  ⟨fun h _ _ hij => h _ _ hij, fun h _ _ hij => h hij⟩

variable (n K)

@[expose] def unitriangular : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {A | (∀ i j : Fin n, j < i → (A : Matrix (Fin n) (Fin n) K) i j = 0) ∧
    ∀ i : Fin n, (A : Matrix (Fin n) (Fin n) K) i i = 1}
  one_mem' := ⟨(upperTriangular n K).one_mem, fun i => by simp⟩
  mul_mem' := fun {A B} hA hB => ⟨(upperTriangular n K).mul_mem hA.1 hB.1, fun i => by
    have hA' : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun _ _ h => hA.1 _ _ h
    have hB' : (B : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun _ _ h => hB.1 _ _ h
    rw [SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular hA' hB', hA.2, hB.2,
      one_mul]⟩
  inv_mem' := fun {A} hA => ⟨(upperTriangular n K).inv_mem hA.1, fun i => by
    have hA' : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun _ _ h => hA.1 _ _ h
    have h := coe_inv_apply_self_of_isUpperTriangular hA' i
    rwa [hA.2, one_mul] at h⟩

variable {n K}

theorem mem_unitriangular {A : SpecialLinearGroup (Fin n) K} :
    A ∈ unitriangular n K ↔ (∀ i j : Fin n, j < i → (A : Matrix (Fin n) (Fin n) K) i j = 0) ∧
      ∀ i : Fin n, (A : Matrix (Fin n) (Fin n) K) i i = 1 :=
  Iff.rfl

variable (n K)

theorem unitriangular_le_upperTriangular : unitriangular n K ≤ upperTriangular n K :=
  fun _ hA => hA.1

theorem scalars_le_upperTriangular : scalars n K ≤ upperTriangular n K := by
  rintro A ⟨c, -, hA⟩ i j hij
  rw [hA, scalar_apply, diagonal_apply_ne _ (ne_of_gt hij)]

@[expose] def projUnitriangular : Subgroup (projectiveSL n K) :=
  (unitriangular n K).map (proj n K)

@[expose] def projUpperTriangular : Subgroup (projectiveSL n K) :=
  (upperTriangular n K).map (proj n K)

variable {n K}

@[expose] def stabilizer (W : Submodule K (Fin n → K)) : Subgroup (SpecialLinearGroup (Fin n) K)
    where
  carrier := {g | W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = W}
  one_mem' := by
    change W.map (mulVecLin (1 : Matrix (Fin n) (Fin n) K)) = W
    rw [mulVecLin_one, Submodule.map_id]
  mul_mem' := fun {g h} hg hh => by
    have hg' : W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = W := hg
    have hh' : W.map (mulVecLin (h : Matrix (Fin n) (Fin n) K)) = W := hh
    change W.map (mulVecLin ((g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K))) =
      W
    rw [mulVecLin_mul, Submodule.map_comp, hh', hg']
  inv_mem' := fun {g} hg => by
    have hg' : W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = W := hg
    change W.map (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) = W
    calc W.map (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K))
        = (W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K))).map
            (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [hg']
      _ = W := by
          rw [← Submodule.map_comp, ← mulVecLin_mul, coe_inv_mul_coe, mulVecLin_one,
            Submodule.map_id]

theorem mem_stabilizer {W : Submodule K (Fin n → K)} {g : SpecialLinearGroup (Fin n) K} :
    g ∈ stabilizer W ↔ W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = W :=
  Iff.rfl

@[expose] def projStabilizer (W : Submodule K (Fin n → K)) : Subgroup (projectiveSL n K) :=
  (stabilizer W).map (proj n K)

theorem scalars_le_stabilizer (W : Submodule K (Fin n → K)) : scalars n K ≤ stabilizer W := by
  rintro g ⟨c, -, hg⟩
  change W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = W
  have hs : ∀ v : Fin n → K, scalar (Fin n) (c : K) *ᵥ v = (c : K) • v := fun v => by
    rw [scalar_apply, ← smul_one_eq_diagonal, smul_mulVec, one_mulVec]
  rw [hg]
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨v, hv, rfl⟩
    rw [mulVecLin_apply, hs]
    exact W.smul_mem (c : K) hv
  · refine ⟨((c⁻¹ : Kˣ) : K) • v, W.smul_mem _ hv, ?_⟩
    rw [mulVecLin_apply, hs, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_smul]

variable (n K)

@[expose] def flagStabilizer (I : Set ℕ) : Subgroup (SpecialLinearGroup (Fin n) K) :=
  ⨅ i ∈ I, stabilizer (flagSpace n K i)

variable {n K}

theorem mem_flagStabilizer {I : Set ℕ} {g : SpecialLinearGroup (Fin n) K} :
    g ∈ flagStabilizer n K I ↔ ∀ i ∈ I, g ∈ stabilizer (flagSpace n K i) := by
  simp only [flagStabilizer, Subgroup.mem_iInf]

variable (n K)

@[simp]
theorem flagStabilizer_empty : flagStabilizer n K ∅ = ⊤ := by
  simp [flagStabilizer]

theorem scalars_le_flagStabilizer (I : Set ℕ) : scalars n K ≤ flagStabilizer n K I :=
  fun _ hg => mem_flagStabilizer.mpr fun _ _ => scalars_le_stabilizer _ hg

@[expose] def reflectionMatrix (i : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b =>
    if ((a : ℕ) + 1 = i ∨ (a : ℕ) + 1 = i + 1) ∧ ((b : ℕ) + 1 = i ∨ (b : ℕ) + 1 = i + 1) then
      (if (a : ℕ) + 1 = i ∧ (b : ℕ) + 1 = i + 1 then -1
        else if (a : ℕ) + 1 = i + 1 ∧ (b : ℕ) + 1 = i then 1 else 0)
    else if a = b then 1 else 0

@[expose] def permMatrix (w : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b => if a = w b then 1 else 0

variable {n K}

theorem permMatrix_apply (w : Equiv.Perm (Fin n)) (a b : Fin n) :
    permMatrix n K w a b = if a = w b then 1 else 0 :=
  rfl

theorem permMatrix_mulVec_single (w : Equiv.Perm (Fin n)) (j : Fin n) :
    permMatrix n K w *ᵥ Pi.single j 1 = Pi.single (w j) 1 := by
  ext a
  rw [mulVec_single, MulOpposite.op_one, one_smul]
  simp only [col_apply, permMatrix_apply, Pi.single_apply]

theorem permMatrix_eq (w : Equiv.Perm (Fin n)) : permMatrix n K w = (w⁻¹).permMatrix K := by
  ext a b
  simp only [permMatrix_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  congr 1
  apply propext
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, eq_comm]

theorem det_permMatrix (w : Equiv.Perm (Fin n)) :
    (permMatrix n K w).det = ((Equiv.Perm.sign w : ℤ) : K) := by
  rw [permMatrix_eq, det_permutation, Equiv.Perm.sign_inv]

theorem reflectionMatrix_eq (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    reflectionMatrix n K i =
      permMatrix n K (Equiv.swap ⟨i - 1, by omega⟩ ⟨i, hin⟩) *
        diagonal (fun b : Fin n => if (b : ℕ) = i then -1 else 1) := by
  ext a b
  rw [mul_diagonal, permMatrix_apply, reflectionMatrix, of_apply, Equiv.swap_apply_def]
  split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (exfalso; omega) | norm_num

theorem det_reflectionMatrix (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    (reflectionMatrix n K i).det = 1 := by
  have ha : (⟨i - 1, by omega⟩ : Fin n) ≠ ⟨i, hin⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  rw [reflectionMatrix_eq i hi hin, det_mul, det_permMatrix, Equiv.Perm.sign_swap ha, det_diagonal,
    Finset.prod_eq_single (⟨i, hin⟩ : Fin n)]
  · simp
  · intro b _ hb
    rw [ite_eq_right fun h => hb (Fin.ext h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable (n K)

@[expose] def reflection (i : ℕ) (hi : 1 ≤ i) (hin : i < n) : SpecialLinearGroup (Fin n) K :=
  ⟨reflectionMatrix n K i, det_reflectionMatrix i hi hin⟩

@[simp]
theorem coe_reflection (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    (reflection n K i hi hin : Matrix (Fin n) (Fin n) K) = reflectionMatrix n K i :=
  rfl

@[expose] def signedPermMatrix (w : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) K :=
  diagonal (fun a : Fin n => if (a : ℕ) = 0 then ((Equiv.Perm.sign w : ℤ) : K) else 1) *
    permMatrix n K w

variable {n K}

theorem det_signedPermMatrix (w : Equiv.Perm (Fin n)) : (signedPermMatrix n K w).det = 1 := by
  rw [signedPermMatrix, det_mul, det_permMatrix, det_diagonal]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim w 1, map_one]
    simp
  · rw [Finset.prod_eq_single (⟨0, hn⟩ : Fin n)]
    · rw [ite_eq_left rfl, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
        Int.cast_one]
    · intro b _ hb
      rw [ite_eq_right fun h => hb (Fin.ext h)]
    · intro h
      exact absurd (Finset.mem_univ _) h

variable (n K)

@[expose] def signedPermutation (w : Equiv.Perm (Fin n)) : SpecialLinearGroup (Fin n) K :=
  ⟨signedPermMatrix n K w, det_signedPermMatrix w⟩

@[simp]
theorem coe_signedPermutation (w : Equiv.Perm (Fin n)) :
    (signedPermutation n K w : Matrix (Fin n) (Fin n) K) = signedPermMatrix n K w :=
  rfl

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
