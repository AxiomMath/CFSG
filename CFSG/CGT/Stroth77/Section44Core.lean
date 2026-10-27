module

public import CFSG.CGT.Stroth77.Section43CoreE

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Type201

theorem uvM_mulVec (m : ℕ) (x : Fin 3 → ℤ) :
    uvM m *ᵥ x = ![-3 * x 0 + x 1 + x 2,
      -4 * x 0 + x 1 + (2 + 3 * 2 ^ (m + 1) + 2 ^ (m + 1) * 2 ^ (m + 1)) * x 2,
      -4 * x 0 + (2 + 2 ^ (m + 1)) * x 1 + x 2] := by
  funext i
  fin_cases i <;> simp [uvM, uvA, tM, ρM] <;> ring

theorem tM_mulVec (m : ℕ) (x : Fin 3 → ℤ) :
    tM m *ᵥ x = ![x 0 - (1 + 2 ^ (m + 1)) * x 2,
      4 * x 0 + (2 ^ (m + 1) - 1) * x 1 - (2 + 2 ^ (m + 1)) * x 2, -(1 + 2 ^ (m + 1)) * x 2] := by
  funext i
  fin_cases i <;> simp [uvA, tM, ρM] <;> ring

theorem uM_mulVec (m : ℕ) (x : Fin 3 → ℤ) : uM m *ᵥ x = ![x 0, x 2, x 1] := by
  funext i
  fin_cases i <;> simp [uM, uMat]

theorem ρM_mulVec (m : ℕ) (x : Fin 3 → ℤ) : ρM m *ᵥ x = ![x 0 - x 2, -x 2, x 1 - x 2] := by
  funext i
  fin_cases i <;> simp [ρM] <;> ring

end Type201

namespace Stroth44Core

variable {m : ℕ}

theorem t201_φuv (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t201 m).action.φuv (Torus.ofInt _ x) = Torus.ofInt _ ![-3 * x 0 + x 1 + x 2,
      -4 * x 0 + x 1 + (2 + 3 * 2 ^ (m + 1) + 2 ^ (m + 1) * 2 ^ (m + 1)) * x 2,
      -4 * x 0 + (2 + 2 ^ (m + 1)) * x 1 + x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t201 m).k) (Type201.uvM m)
    (StrothTypeIndex.t201 m).action.compat_uv x
  rw [Type201.uvM_mulVec] at h
  exact h

theorem t201_φt (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t201 m).action.φt (Torus.ofInt _ x) = Torus.ofInt _
      ![x 0 - (1 + 2 ^ (m + 1)) * x 2,
        4 * x 0 + (2 ^ (m + 1) - 1) * x 1 - (2 + 2 ^ (m + 1)) * x 2, -(1 + 2 ^ (m + 1)) * x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t201 m).k) (Type201.tM m)
    (StrothTypeIndex.t201 m).action.compat_t x
  rw [Type201.tM_mulVec] at h
  exact h

theorem t201_φu (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t201 m).action.φu (Torus.ofInt _ x) = Torus.ofInt _ ![x 0, x 2, x 1] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t201 m).k) (Type201.uM m)
    (StrothTypeIndex.t201 m).action.compat_u x
  rw [Type201.uM_mulVec] at h
  exact h

theorem t201_φρ (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t201 m).action.φρ (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0 - x 2, -x 2, x 1 - x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t201 m).k) (Type201.ρM m)
    (StrothTypeIndex.t201 m).action.compat_ρ x
  rw [Type201.ρM_mulVec] at h
  exact h

theorem t201_ofInt_eq_iff (x y : Fin 3 → ℤ) :
    Torus.ofInt (StrothTypeIndex.t201 m).k x = Torus.ofInt _ y ↔
      (2 : ℤ) ^ m ∣ y 0 - x 0 ∧ (2 : ℤ) ^ (m + 2) ∣ y 1 - x 1 ∧
        (2 : ℤ) ^ (m + 2) ∣ y 2 - x 2 := by
  rw [Torus.ofInt_eq_ofInt_iff]
  constructor
  · intro h
    exact ⟨Int.modEq_iff_dvd.mp (h 0), Int.modEq_iff_dvd.mp (h 1), Int.modEq_iff_dvd.mp (h 2)⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact Int.modEq_iff_dvd.mpr h0
    · exact Int.modEq_iff_dvd.mpr h1
    · exact Int.modEq_iff_dvd.mpr h2


section Elements

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t201 m))

open StrothWeakTypeData

include dD in
theorem mem_comm {x y : G} (hx : x ∈ D) (hy : y ∈ D) : x * y = y * x :=
  congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem ofTorus_ofInt_mul (v w : Fin 3 → ℤ) :
    dD.ofTorus (Torus.ofInt _ v) * dD.ofTorus (Torus.ofInt _ w) =
      dD.ofTorus (Torus.ofInt _ (v + w)) := by
  rw [Torus.ofInt_add, dD.ofTorus_add]

theorem ofTorus_ofInt_inv (v : Fin 3 → ℤ) :
    (dD.ofTorus (Torus.ofInt _ v))⁻¹ = dD.ofTorus (Torus.ofInt _ (-v)) := by
  rw [Torus.ofInt_neg, dD.ofTorus_neg]

theorem c_pow_eq (n : ℕ) : (dD.c : G) ^ n = dD.ofTorus (Torus.ofInt _ ![(n : ℤ), 0, 0]) := by
  rw [dD.ofTorus_ofInt]
  simp

theorem a_pow_eq (n : ℕ) : (dD.a : G) ^ n = dD.ofTorus (Torus.ofInt _ ![0, (n : ℤ), 0]) := by
  rw [dD.ofTorus_ofInt]
  simp

theorem b_pow_eq (n : ℕ) : (dD.b : G) ^ n = dD.ofTorus (Torus.ofInt _ ![0, 0, (n : ℤ)]) := by
  rw [dD.ofTorus_ofInt]
  simp

theorem cab_eq : dD.cab = dD.ofTorus (Torus.ofInt _ ![1, 1, 1]) := by
  rw [dD.ofTorus_ofInt]
  simp [StrothWeakTypeData.cab]

theorem ab_inv_pow_eq (n : ℕ) :
    ((dD.a : G) * (dD.b : G)⁻¹) ^ n = dD.ofTorus (Torus.ofInt _ ![0, (n : ℤ), -(n : ℤ)]) := by
  have hab0 : Commute (dD.a : G) (dD.b : G) :=
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm dD.a dD.b)
  have hab : Commute (dD.a : G) (dD.b : G)⁻¹ := hab0.inv_right
  rw [hab.mul_pow, a_pow_eq, inv_pow, b_pow_eq, ofTorus_ofInt_inv, ofTorus_ofInt_mul]
  congr 2
  funext i
  fin_cases i <;> simp

theorem a_inv_mul_b_pow_eq (n : ℕ) :
    (dD.a : G)⁻¹ * (dD.b : G) ^ n = dD.ofTorus (Torus.ofInt _ ![0, -1, (n : ℤ)]) := by
  rw [dD.ofTorus_ofInt]
  simp

end Elements

section Facts

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t201 m))

open StrothWeakTypeData

theorem ofTorus_ofInt_eq_one_iff (v : Fin 3 → ℤ) :
    dD.ofTorus (Torus.ofInt _ v) = 1 ↔
      (2 : ℤ) ^ m ∣ v 0 ∧ (2 : ℤ) ^ (m + 2) ∣ v 1 ∧ (2 : ℤ) ^ (m + 2) ∣ v 2 := by
  rw [dD.ofTorus_eq_one_iff, ← Torus.ofInt_zero, t201_ofInt_eq_iff]
  simp

theorem nf_eq_iff (v w : Fin 3 → ℤ) (i j l : Bool) :
    dD.ofTorus (Torus.ofInt _ v) * dD.d8 i j l = dD.ofTorus (Torus.ofInt _ w) * dD.d8 i j l ↔
      (2 : ℤ) ^ m ∣ w 0 - v 0 ∧ (2 : ℤ) ^ (m + 2) ∣ w 1 - v 1 ∧
        (2 : ℤ) ^ (m + 2) ∣ w 2 - v 2 := by
  rw [mul_left_inj, dD.ofTorus_inj.eq_iff, t201_ofInt_eq_iff]

theorem x_eq : (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv =
    dD.ofTorus (Torus.ofInt _ ![2 ^ (m - 1) + 1, 1, 1]) * dD.d8 true false false := by
  rw [c_pow_eq, cab_eq, ofTorus_ofInt_mul, dD.d8_tff]
  congr 3
  funext i
  fin_cases i <;> simp

theorem t201_hx2 (hm : 1 ≤ m) :
    (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
      ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv) = 1 := by
  rw [x_eq, dD.nf_mul_self]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, dD.d8_fff, mul_one]
  rw [t201_φuv, ← Torus.ofInt_add, ofTorus_ofInt_eq_one_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨-1, by ring⟩, ⟨1 + 2 * 2 ^ k, by ring⟩, ⟨0, by ring⟩⟩

theorem l_eq : (dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u =
    dD.ofTorus (Torus.ofInt _ ![2 ^ (m - 1), 2 ^ m, -2 ^ m]) * dD.d8 false false true := by
  rw [c_pow_eq, ab_inv_pow_eq, ofTorus_ofInt_mul, dD.d8_fft]
  congr 3
  funext i
  fin_cases i <;> simp

theorem t201_hxl (hm : 1 ≤ m) :
    (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
        ((dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u) =
      (dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u *
        ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv) := by
  rw [x_eq, l_eq, dD.nf_mul_nf, dD.nf_mul_nf]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
    Bool.and_false, Bool.xor_false, Bool.false_xor, Bool.xor_true, Bool.true_xor, Bool.not_false,
    Bool.not_true, AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  rw [t201_φuv, t201_φu, ← Torus.ofInt_add, ← Torus.ofInt_add, nf_eq_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨2, by ring⟩, ⟨1 + 3 * 2 ^ k + 4 * (2 ^ k) ^ 2, by ring⟩, ⟨-(2 ^ k), by ring⟩⟩

theorem t201_hl :
    (dD.a : G) ^ 2 ^ m * ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) * ((dD.a : G) ^ 2 ^ m)⁻¹ =
      (dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u := by
  rw [l_eq, a_pow_eq, c_pow_eq, ofTorus_ofInt_inv, ← dD.d8_fft, ← mul_assoc, ofTorus_ofInt_mul,
    mul_assoc, dD.d8_mul_ofTorus, ← mul_assoc]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply]
  rw [t201_φu, ofTorus_ofInt_mul]
  congr 3
  funext i
  fin_cases i <;> simp

theorem t201_hxlu (hm : 1 ≤ m) :
    (dD.t * dD.ofTorus (Torus.ofInt _ ![0, 0, 3 * 2 ^ m - 1]))⁻¹ *
        ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
          ((dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u)) *
        (dD.t * dD.ofTorus (Torus.ofInt _ ![0, 0, 3 * 2 ^ m - 1])) = dD.u := by
  set q := dD.t * dD.ofTorus (Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 0, 3 * 2 ^ m - 1])
  suffices key : (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
      ((dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u) * q = q * dD.u by
    rw [mul_assoc, key, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [x_eq, l_eq, dD.nf_mul_nf]
  simp only [q, ← dD.d8_ftf, ← dD.d8_fft]
  rw [show ∀ a b c d : G, a * b * (c * d) = a * (b * c) * d from fun _ _ _ _ => by group,
    dD.d8_mul_d8, mul_assoc, dD.d8_mul_ofTorus, ← mul_assoc, ← dD.ofTorus_add, dD.d8_mul_ofTorus,
    mul_assoc, dD.d8_mul_d8]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
    Bool.and_false, Bool.true_and, Bool.and_true, Bool.xor_false, Bool.false_xor, Bool.xor_true,
    Bool.true_xor, Bool.not_false, Bool.not_true, AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  rw [t201_φuv, t201_φu, t201_φt, ← Torus.ofInt_add, ← Torus.ofInt_add, t201_φt, nf_eq_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨-12 * 2 ^ k, by ring⟩, ⟨1 - 3 * 2 ^ k + 4 * (2 ^ k) ^ 2, by ring⟩,
    ⟨-4 * 2 ^ k, by ring⟩⟩

theorem f_eq : (dD.a : G)⁻¹ * (dD.b : G) ^ 2 ^ m * dD.t =
    dD.ofTorus (Torus.ofInt _ ![0, -1, 2 ^ m]) * dD.d8 false true false := by
  rw [a_inv_mul_b_pow_eq, dD.d8_ftf]
  congr 3

theorem t201_hf2 (hm : 1 ≤ m) :
    (dD.a : G)⁻¹ * (dD.b : G) ^ 2 ^ m * dD.t * ((dD.a : G)⁻¹ * (dD.b : G) ^ 2 ^ m * dD.t) = 1 := by
  rw [f_eq, dD.nf_mul_self]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, dD.d8_fff, mul_one]
  rw [t201_φt, ← Torus.ofInt_add, ofTorus_ofInt_eq_one_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨-(1 + 4 * 2 ^ k), by ring⟩, ⟨-(1 + 2 ^ k), by ring⟩, ⟨-(2 ^ k), by ring⟩⟩

theorem t201_hxf (hm : 1 ≤ m) :
    (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv * ((dD.a : G)⁻¹ * (dD.b : G) ^ 2 ^ m * dD.t) =
      (dD.a : G)⁻¹ * (dD.b : G) ^ 2 ^ m * dD.t * ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv) := by
  rw [x_eq, f_eq, dD.nf_mul_nf, dD.nf_mul_nf]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
    Bool.and_false, Bool.xor_false, Bool.false_xor, Bool.xor_true, Bool.true_xor, Bool.not_false,
    Bool.not_true, AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  rw [t201_φuv, t201_φt, ← Torus.ofInt_add, ← Torus.ofInt_add, nf_eq_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨-3, by ring⟩, ⟨-3 * 2 ^ k - 4 * (2 ^ k) ^ 2, by ring⟩, ⟨0, by ring⟩⟩

theorem za_eq : (dD.a : G) ^ 2 ^ (m + 1) =
    dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (m + 1), 0]) := by
  rw [a_pow_eq]
  congr 2

theorem zb_eq : (dD.b : G) ^ 2 ^ (m + 1) =
    dD.ofTorus (Torus.ofInt _ ![0, 0, 2 ^ (m + 1)]) := by
  rw [b_pow_eq]
  congr 2

theorem t201_za_comm (hm : 1 ≤ m) :
    (StrothTypeIndex.t201 m).action.φuv (Torus.ofInt _ ![0, 2 ^ (m + 1), 0]) =
        Torus.ofInt _ ![0, 2 ^ (m + 1), 0] ∧
      (StrothTypeIndex.t201 m).action.φt (Torus.ofInt _ ![0, 2 ^ (m + 1), 0]) =
        Torus.ofInt _ ![0, 2 ^ (m + 1), 0] := by
  rw [t201_φuv, t201_φt, t201_ofInt_eq_iff, t201_ofInt_eq_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine ⟨⟨⟨-2, by ring⟩, ⟨0, by ring⟩, ⟨-1 - 2 * 2 ^ k, by ring⟩⟩,
    ⟨⟨0, by ring⟩, ⟨1 - 2 * 2 ^ k, by ring⟩, ⟨0, by ring⟩⟩⟩

theorem t201_zb_comm (hm : 1 ≤ m) :
    (StrothTypeIndex.t201 m).action.φuv (Torus.ofInt _ ![0, 0, 2 ^ (m + 1)]) =
        Torus.ofInt _ ![0, 0, 2 ^ (m + 1)] ∧
      (StrothTypeIndex.t201 m).action.φt (Torus.ofInt _ ![0, 0, 2 ^ (m + 1)]) =
        Torus.ofInt _ ![0, 0, 2 ^ (m + 1)] := by
  rw [t201_φuv, t201_φt, t201_ofInt_eq_iff, t201_ofInt_eq_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine ⟨⟨⟨-2, by ring⟩, ⟨-1 - 6 * 2 ^ k - 8 * (2 ^ k) ^ 2, by ring⟩, ⟨0, by ring⟩⟩,
    ⟨⟨2 + 8 * 2 ^ k, by ring⟩, ⟨1 + 2 * 2 ^ k, by ring⟩, ⟨1 + 2 * 2 ^ k, by ring⟩⟩⟩

theorem not_two_pow_dvd_four (hm : 1 ≤ m) : ¬ (2 : ℤ) ^ (m + 2) ∣ 4 := by
  intro h
  have h1 := Int.le_of_dvd (by norm_num) h
  have h2 : (2 : ℤ) ^ 3 ≤ 2 ^ (m + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at h2
  omega

theorem uv_not_mem (hm : 1 ≤ m) : dD.uv ∉ D := by
  intro huv
  have h := dD.uv_mul_ofTorus (Torus.ofInt _ ![1, 0, 0])
  rw [mem_comm dD huv (dD.ofTorus_mem _), mul_left_inj, dD.ofTorus_inj.eq_iff, t201_φuv,
    t201_ofInt_eq_iff] at h
  obtain ⟨-, h1, -⟩ := h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h1
  exact not_two_pow_dvd_four hm (by simpa using h1)

theorem t_not_mem (hm : 1 ≤ m) : dD.t ∉ D := by
  intro ht
  have h := dD.t_mul_ofTorus (Torus.ofInt _ ![0, 1, 0])
  rw [mem_comm dD ht (dD.ofTorus_mem _), mul_left_inj, dD.ofTorus_inj.eq_iff, t201_φt,
    t201_ofInt_eq_iff] at h
  obtain ⟨-, h1, -⟩ := h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have h4 : (4 : ℤ) ∣ _ := dvd_trans ⟨2 * 2 ^ k, by ring⟩ h1
  have e : ∀ X : ℤ, X = 4 * 2 ^ k - 2 → (4 : ℤ) ∣ X → False := by
    intro X hX hd
    rw [hX] at hd
    generalize (2 : ℤ) ^ k = P at hd
    omega
  exact e _ (by ring) h4

theorem uv_mul_t_not_mem (hm : 1 ≤ m) : dD.uv * dD.t ∉ D := by
  intro hut
  have h := dD.d8_mul_ofTorus true true false (Torus.ofInt _ ![0, 1, 0])
  rw [dD.d8_ttf, mem_comm dD hut (dD.ofTorus_mem _), mul_left_inj, dD.ofTorus_inj.eq_iff] at h
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] at h
  rw [t201_φt, t201_φuv, t201_ofInt_eq_iff] at h
  obtain ⟨h0, -, -⟩ := h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h0
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have h2 : (2 : ℤ) ∣ _ := dvd_trans ⟨2 ^ k, by ring⟩ h0
  have e : ∀ X : ℤ, X = 4 * 2 ^ k - 1 → (2 : ℤ) ∣ X → False := by
    intro X hX hd
    rw [hX] at hd
    generalize (2 : ℤ) ^ k = P at hd
    omega
  exact e _ (by ring) h2

theorem d8_mem_of_nf_mem {v : Torus (StrothTypeIndex.t201 m).k} {i j l : Bool}
    (h : dD.ofTorus v * dD.d8 i j l ∈ D) : dD.d8 i j l ∈ D := by
  have := D.mul_mem (D.inv_mem (dD.ofTorus_mem v)) h
  rwa [inv_mul_cancel_left] at this

theorem za_mul_x (hm : 1 ≤ m) :
    (dD.a : G) ^ 2 ^ (m + 1) * ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv) =
      (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv * (dD.a : G) ^ 2 ^ (m + 1) := by
  rw [x_eq, za_eq]
  refine ((dD.nf_commute_iff _ _ _ _ _).2 ?_).symm
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply]
  exact (t201_za_comm hm).1

theorem zb_mul_x (hm : 1 ≤ m) :
    (dD.b : G) ^ 2 ^ (m + 1) * ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv) =
      (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv * (dD.b : G) ^ 2 ^ (m + 1) := by
  rw [x_eq, zb_eq]
  refine ((dD.nf_commute_iff _ _ _ _ _).2 ?_).symm
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply]
  exact (t201_zb_comm hm).1

theorem za_mul_f (hm : 1 ≤ m) :
    (dD.a : G) ^ 2 ^ (m + 1) * ((dD.a : G)⁻¹ * (dD.b : G) ^ 2 ^ m * dD.t) =
      (dD.a : G)⁻¹ * (dD.b : G) ^ 2 ^ m * dD.t * (dD.a : G) ^ 2 ^ (m + 1) := by
  rw [f_eq, za_eq]
  refine ((dD.nf_commute_iff _ _ _ _ _).2 ?_).symm
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply]
  exact (t201_za_comm hm).2

theorem zb_mul_f (hm : 1 ≤ m) :
    (dD.b : G) ^ 2 ^ (m + 1) * ((dD.a : G)⁻¹ * (dD.b : G) ^ 2 ^ m * dD.t) =
      (dD.a : G)⁻¹ * (dD.b : G) ^ 2 ^ m * dD.t * (dD.b : G) ^ 2 ^ (m + 1) := by
  rw [f_eq, zb_eq]
  refine ((dD.nf_commute_iff _ _ _ _ _).2 ?_).symm
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply]
  exact (t201_zb_comm hm).2

theorem za_zb (hm : 1 ≤ m) :
    (dD.a : G) ^ 2 ^ (m + 1) * (dD.a : G) ^ 2 ^ (m + 1) = 1 ∧
      (dD.b : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) = 1 ∧
      (dD.a : G) ^ 2 ^ (m + 1) ≠ 1 ∧ (dD.b : G) ^ 2 ^ (m + 1) ≠ 1 ∧
      (dD.a : G) ^ 2 ^ (m + 1) ≠ (dD.b : G) ^ 2 ^ (m + 1) := by
  rw [za_eq, zb_eq, ofTorus_ofInt_mul, ofTorus_ofInt_mul, ofTorus_ofInt_eq_one_iff,
    ofTorus_ofInt_eq_one_iff, Ne, ofTorus_ofInt_eq_one_iff, Ne, ofTorus_ofInt_eq_one_iff, Ne,
    dD.ofTorus_inj.eq_iff, t201_ofInt_eq_iff]
  have hne : ¬ (2 : ℤ) ^ (m + 2) ∣ 2 ^ (m + 1) := by
    intro h
    have h1 := Int.le_of_dvd (by positivity) h
    have h2 : (2 : ℤ) ^ (m + 1) < 2 ^ (m + 2) := pow_lt_pow_right₀ (by norm_num) (by omega)
    omega
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, add_zero, dvd_zero, true_and, and_true, zero_sub, sub_zero,
    dvd_neg]
  refine ⟨⟨1, by ring⟩, ⟨1, by ring⟩, hne, hne, fun h => hne h.1⟩

theorem t201_hx16 (hm : 1 ≤ m) :
    ∃ E : Subgroup G,
      E ≤ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv} ∧
        (∀ y ∈ E, y * y = 1) ∧ Nat.card E = 16 := by
  obtain ⟨hza2, hzb2, hza1, hzb1, hzazb⟩ := za_zb dD hm
  have hcab : (dD.c : G) ^ 2 ^ (m - 1) * dD.cab ∈ D :=
    D.mul_mem (D.pow_mem dD.c.2 _) (D.mul_mem (D.mul_mem dD.c.2 dD.a.2) dD.b.2)
  have hg : (dD.a : G)⁻¹ * (dD.b : G) ^ 2 ^ m ∈ D :=
    D.mul_mem (D.inv_mem dD.a.2) (D.pow_mem dD.b.2 _)
  have hxD : (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv ∉ D := fun h' =>
    uv_not_mem dD hm (by
      have := D.mul_mem (D.inv_mem hcab) h'
      rwa [inv_mul_cancel_left] at this)
  have hfD : (dD.a : G)⁻¹ * (dD.b : G) ^ 2 ^ m * dD.t ∉ D := fun h' =>
    t_not_mem dD hm (by
      have := D.mul_mem (D.inv_mem hg) h'
      rwa [inv_mul_cancel_left] at this)
  have hxfD : (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
      ((dD.a : G)⁻¹ * (dD.b : G) ^ 2 ^ m * dD.t) ∉ D := by
    rw [x_eq, f_eq, dD.nf_mul_nf]
    intro h'
    apply uv_mul_t_not_mem dD hm
    have := d8_mem_of_nf_mem dD h'
    simpa [dD.d8_ttf] using this
  exact Stroth42Core.exists_E16 (D.pow_mem dD.a.2 _) (D.pow_mem dD.b.2 _) hza2 hzb2
    (t201_hx2 dD hm) (t201_hf2 dD hm) (mem_comm dD (D.pow_mem dD.a.2 _) (D.pow_mem dD.b.2 _))
    (za_mul_x dD hm) (za_mul_f dD hm) (zb_mul_x dD hm) (zb_mul_f dD hm) (t201_hxf dD hm) hza1
    hzb1 hzazb hxD hfD hxfD (za_mul_x dD hm) (zb_mul_x dD hm) rfl (t201_hxf dD hm).symm

theorem t201_hl' {S : Subgroup G} (hDS : D ≤ S) :
    ∃ q ∈ S, q⁻¹ * ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) * q =
      (dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u :=
  ⟨((dD.a : G) ^ 2 ^ m)⁻¹, S.inv_mem (hDS (D.pow_mem dD.a.2 _)), by rw [inv_inv]; exact t201_hl dD⟩

theorem t201_hxlu' (hm : 1 ≤ m) {S : Subgroup G} (hDS : D ≤ S) (htS : dD.t ∈ S) :
    ∃ q ∈ S, q⁻¹ * ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
      ((dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u)) * q = dD.u :=
  ⟨_, S.mul_mem htS (hDS (dD.ofTorus_mem _)), t201_hxlu dD hm⟩

theorem t201_h3 (hm : 1 ≤ m) : ∀ y ∈ D, y * y = 1 → y ≠ 1 →
    (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ (m - 1)) ∨
      ∃ g ∈ dD.L, g⁻¹ * y * g = (dD.a : G) ^ 2 ^ (m + 1) := by
  intro y hy hy2 hy1
  obtain ⟨v, rfl⟩ := dD.exists_ofTorus hy
  rw [dD.ofTorus_mul_self, dD.ofTorus_eq_one_iff] at hy2
  have hk : ∀ i, 1 ≤ (StrothTypeIndex.t201 m).k i := by
    intro i
    fin_cases i <;> simp [StrothTypeIndex.k, Type201.k] <;> omega
  obtain ⟨ε, hε, rfl⟩ := (Torus.two_zsmul_eq_zero_iff hk v).mp (by rw [two_zsmul]; exact hy2)
  have hv : (fun i => ε i * 2 ^ ((StrothTypeIndex.t201 m).k i - 1) : Fin 3 → ℤ) =
      ![ε 0 * 2 ^ (m - 1), ε 1 * 2 ^ (m + 1), ε 2 * 2 ^ (m + 1)] := by
    funext i
    fin_cases i <;> rfl
  have huvP : dD.uv ∈ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) :=
    Subgroup.subset_closure (by simp)
  have htP : dD.t ∈ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) :=
    Subgroup.subset_closure (by simp)
  rw [hv] at hy1 ⊢
  rw [c_pow_eq, za_eq]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel] at hy1 ⊢
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2 | h2 <;>
    rw [h0, h1, h2] at hy1 ⊢ <;> simp only [zero_mul, one_mul] at hy1 ⊢
  · exact absurd (by rw [show (![0, 0, 0] : Fin 3 → ℤ) = 0 by funext i; fin_cases i <;> rfl,
      Torus.ofInt_zero, dD.ofTorus_zero]) hy1
  ·
    refine Or.inr ⟨dD.u, dD.u_mem_L, ?_⟩
    rw [dD.conj_ofTorus dD.u_mem dD.u_conj, t201_φu]
    congr 2
  · exact Or.inr ⟨1, one_mem _, by simp⟩
  ·
    refine Or.inr ⟨dD.ρ, dD.ρ_mem_L, ?_⟩
    rw [dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, t201_φρ, dD.ofTorus_inj.eq_iff, t201_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨⟨2, by ring⟩, ⟨1, by ring⟩, ⟨0, by ring⟩⟩
  · exact Or.inl ⟨1, one_mem _, by simp⟩
  ·
    refine Or.inl ⟨dD.uv * dD.t, mul_mem huvP htP, ?_⟩
    rw [show (dD.uv * dD.t)⁻¹ * dD.ofTorus (Torus.ofInt _ ![2 ^ k, 0, 2 ^ (k + 1 + 1)]) *
        (dD.uv * dD.t) = dD.t⁻¹ * (dD.uv⁻¹ * dD.ofTorus (Torus.ofInt _ ![2 ^ k, 0, 2 ^ (k + 1 + 1)])
          * dD.uv) * dD.t by group,
      dD.conj_ofTorus dD.uv_mem dD.uv_conj, t201_φuv, dD.conj_ofTorus dD.t_mem dD.t_conj, t201_φt,
      dD.ofTorus_inj.eq_iff, t201_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ⟨4 * 2 ^ k - 16 * (2 ^ k) ^ 2 - 32 * (2 ^ k) ^ 3, by ring⟩,
      ⟨0, by ring⟩⟩
  ·
    refine Or.inl ⟨dD.t, htP, ?_⟩
    rw [dD.conj_ofTorus dD.t_mem dD.t_conj, t201_φt, dD.ofTorus_inj.eq_iff, t201_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ⟨-2 * 2 ^ k, by ring⟩, ⟨0, by ring⟩⟩
  ·
    refine Or.inl ⟨dD.uv, huvP, ?_⟩
    rw [dD.conj_ofTorus dD.uv_mem dD.uv_conj, t201_φuv, dD.ofTorus_inj.eq_iff, t201_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨⟨-2, by ring⟩, ⟨-1 - 6 * 2 ^ k - 8 * (2 ^ k) ^ 2, by ring⟩, ⟨-1 - 2 * 2 ^ k, by ring⟩⟩

end Facts

end Stroth44Core

end CFSG.CGT.Stroth77
