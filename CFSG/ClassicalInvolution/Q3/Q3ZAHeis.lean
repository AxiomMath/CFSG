module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped commutatorElement

abbrev F3 : Type := GaloisField 3 1

abbrev V4 : Type := Fin 2 ⊕ Fin 2 → F3

@[ext] structure Heis where
  c : F3
  v : V4

namespace Heis

noncomputable instance : Mul Heis :=
  ⟨fun x y => ⟨x.c + y.c + 2 * form x.v y.v, x.v + y.v⟩⟩

noncomputable instance : One Heis := ⟨⟨0, 0⟩⟩

noncomputable instance : Inv Heis := ⟨fun x => ⟨-x.c, -x.v⟩⟩

theorem mul_def (x y : Heis) : x * y = ⟨x.c + y.c + 2 * form x.v y.v, x.v + y.v⟩ := rfl

theorem one_def : (1 : Heis) = ⟨0, 0⟩ := rfl

theorem inv_def (x : Heis) : x⁻¹ = ⟨-x.c, -x.v⟩ := rfl

theorem form_neg_right' (v w : V4) : form v (-w) = -form v w := by
  have h := form_smul_right (K := F3) (n := 2) v w (-1)
  simpa using h

theorem form_neg_left' (v w : V4) : form (-v) w = -form v w := by
  have h := form_smul_left (K := F3) (n := 2) v w (-1)
  simpa using h

noncomputable instance : Group Heis where
  mul_assoc x y z := by
    ext
    · simp only [mul_def, form_add_left, form_add_right]
      ring
    · simp only [mul_def, add_assoc]
  one_mul x := by
    ext
    · simp [mul_def, one_def, form_zero_left]
    · simp [mul_def, one_def]
  mul_one x := by
    ext
    · simp [mul_def, one_def, form_zero_right]
    · simp [mul_def, one_def]
  inv_mul_cancel x := by
    ext
    · simp [mul_def, one_def, inv_def, form_neg_left', form_self]
    · simp [mul_def, one_def, inv_def]

@[expose] noncomputable def center : Heis := ⟨1, 0⟩

@[expose] noncomputable def vec (v : V4) : Heis := ⟨0, v⟩

theorem vec_mul_vec (v w : V4) : vec v * vec w = ⟨2 * form v w, v + w⟩ := by
  ext <;> simp [mul_def, vec]

theorem center_mul (x : Heis) : center * x = ⟨x.c + 1, x.v⟩ := by
  ext
  · simp [mul_def, center, form_zero_left]; ring
  · simp [mul_def, center]

theorem mul_center (x : Heis) : x * center = ⟨x.c + 1, x.v⟩ := by
  ext
  · simp [mul_def, center, form_zero_right]
  · simp [mul_def, center]

theorem center_mul_comm (x : Heis) : center * x = x * center := by
  rw [center_mul, mul_center]

end Heis

@[expose] noncomputable def heisAutOf (s : StatedSp 2 F3) : Heis ≃* Heis where
  toFun x := ⟨x.c, (mat 2 F3 s).mulVec x.v⟩
  invFun x := ⟨x.c, (mat 2 F3 s⁻¹).mulVec x.v⟩
  left_inv x := by
    refine Heis.ext rfl ?_
    show (mat 2 F3 s⁻¹).mulVec ((mat 2 F3 s).mulVec x.v) = x.v
    rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
  right_inv x := by
    refine Heis.ext rfl ?_
    show (mat 2 F3 s).mulVec ((mat 2 F3 s⁻¹).mulVec x.v) = x.v
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  map_mul' x y := by
    refine Heis.ext ?_ ?_
    · show x.c + y.c + 2 * form x.v y.v =
        x.c + y.c + 2 * form ((mat 2 F3 s).mulVec x.v) ((mat 2 F3 s).mulVec y.v)
      rw [form_mulVec]
    · show (mat 2 F3 s).mulVec (x.v + y.v) =
        (mat 2 F3 s).mulVec x.v + (mat 2 F3 s).mulVec y.v
      rw [Matrix.mulVec_add]

@[expose] noncomputable def heisAct : StatedSp 2 F3 →* MulAut Heis where
  toFun := heisAutOf
  map_one' := by
    refine MulEquiv.ext fun x => Heis.ext rfl ?_
    show (mat 2 F3 1).mulVec x.v = x.v
    rw [map_one, Matrix.one_mulVec]
  map_mul' s t := by
    refine MulEquiv.ext fun x => Heis.ext rfl ?_
    show (mat 2 F3 (s * t)).mulVec x.v = (mat 2 F3 s).mulVec ((mat 2 F3 t).mulVec x.v)
    rw [map_mul, Matrix.mulVec_mulVec]

theorem heisAct_apply (s : StatedSp 2 F3) (x : Heis) :
    heisAct s x = ⟨x.c, (mat 2 F3 s).mulVec x.v⟩ :=
  rfl

end CFSG.ClassicalInvolution.Q3.Q3ZA
