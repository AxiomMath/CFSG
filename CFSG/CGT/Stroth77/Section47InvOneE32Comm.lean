module

public import CFSG.CGT.Stroth77.Section47InvOneCard
public import CFSG.CGT.Stroth77.Section47InvOneS1

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core Stroth34T200

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))
  {e : G}

open StrothWeakTypeData

theorem t200inv1_twist_tff {j p : ℕ} (hrel : Rel34inv dD e j 1 p) :
    (dD.t200inv1EAction hrel).twist true false =
      Torus.ofInt _ ![(p : ℤ), (p : ℤ), (p : ℤ)] := by
  rw [EAction.twist]
  simp only [Bool.false_eq_true, ↓reduceIte, map_zero, add_zero]
  rfl

theorem t200inv1_twist_ftf {j p : ℕ} (hrel : Rel34inv dD e j 1 p) :
    (dD.t200inv1EAction hrel).twist false true =
      Torus.ofInt _ ![0, -(p : ℤ), 0] := by
  rw [EAction.twist]
  simp only [Bool.false_eq_true, ↓reduceIte, SigmaFourAction.d8Act, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, zero_add]
  rfl

theorem t200inv1_e_mul_nf {j p : ℕ} (hrel : Rel34inv dD e j 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) (i j' l : Bool) :
    e * (dD.ofTorus v * dD.d8 i j' l) =
      dD.ofTorus ((dD.t200inv1EAction hrel).φe v + (dD.t200inv1EAction hrel).twist i j') *
        dD.d8 i j' l * e := by
  calc e * (dD.ofTorus v * dD.d8 i j' l)
      = (e * dD.ofTorus v) * dD.d8 i j' l := by group
    _ = (dD.ofTorus ((dD.t200inv1EAction hrel).φe v) * e) * dD.d8 i j' l := by
        rw [(dD.t200inv1EAction hrel).e_mul_ofTorus]
    _ = dD.ofTorus ((dD.t200inv1EAction hrel).φe v) *
          (e * dD.d8 i j' l) := by group
    _ = dD.ofTorus ((dD.t200inv1EAction hrel).φe v) *
          (dD.ofTorus ((dD.t200inv1EAction hrel).twist i j') * dD.d8 i j' l * e) := by
        rw [(dD.t200inv1EAction hrel).e_mul_d8 i j' l]
        simp only [show (dD.t200inv1EAction hrel).ve = 0 from rfl, sub_zero, map_zero,
          zero_add]
    _ = (dD.ofTorus ((dD.t200inv1EAction hrel).φe v) *
          dD.ofTorus ((dD.t200inv1EAction hrel).twist i j')) * dD.d8 i j' l * e := by
        group
    _ = dD.ofTorus ((dD.t200inv1EAction hrel).φe v +
          (dD.t200inv1EAction hrel).twist i j') * dD.d8 i j' l * e := by
        rw [← dD.ofTorus_add]

theorem t200inv1_e_comm_nf_iff {j p : ℕ} (hrel : Rel34inv dD e j 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) (i j' l : Bool) :
    e * (dD.ofTorus v * dD.d8 i j' l) = dD.ofTorus v * dD.d8 i j' l * e ↔
      (dD.t200inv1EAction hrel).φe v + (dD.t200inv1EAction hrel).twist i j' = v := by
  rw [t200inv1_e_mul_nf dD hrel]
  rw [mul_right_cancel_iff, mul_right_cancel_iff, dD.ofTorus_inj.eq_iff]

theorem t200inv1_c₁e_mul_nf_left {j p : ℕ} (hrel : Rel34inv dD e j 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) (i j' l : Bool) :
    (dD.ofTorus (om200 m ![1, 0, 0]) * e) * (dD.ofTorus v * dD.d8 i j' l) =
      dD.ofTorus ((om200 m ![1, 0, 0] + (dD.t200inv1EAction hrel).φe v) +
        (dD.t200inv1EAction hrel).twist i j') * dD.d8 i j' l * e := by
  calc (dD.ofTorus (om200 m ![1, 0, 0]) * e) * (dD.ofTorus v * dD.d8 i j' l)
      = dD.ofTorus (om200 m ![1, 0, 0]) * (e * (dD.ofTorus v * dD.d8 i j' l)) := by group
    _ = dD.ofTorus (om200 m ![1, 0, 0]) *
          (dD.ofTorus ((dD.t200inv1EAction hrel).φe v +
            (dD.t200inv1EAction hrel).twist i j') * dD.d8 i j' l * e) := by
        rw [t200inv1_e_mul_nf dD hrel]
    _ = (dD.ofTorus (om200 m ![1, 0, 0]) *
          dD.ofTorus ((dD.t200inv1EAction hrel).φe v +
            (dD.t200inv1EAction hrel).twist i j')) * dD.d8 i j' l * e := by group
    _ = dD.ofTorus (om200 m ![1, 0, 0] +
          ((dD.t200inv1EAction hrel).φe v + (dD.t200inv1EAction hrel).twist i j')) *
          dD.d8 i j' l * e := by rw [← dD.ofTorus_add]
    _ = dD.ofTorus ((om200 m ![1, 0, 0] + (dD.t200inv1EAction hrel).φe v) +
          (dD.t200inv1EAction hrel).twist i j') * dD.d8 i j' l * e := by
        rw [show om200 m ![1, 0, 0] + ((dD.t200inv1EAction hrel).φe v +
            (dD.t200inv1EAction hrel).twist i j') =
          (om200 m ![1, 0, 0] + (dD.t200inv1EAction hrel).φe v) +
            (dD.t200inv1EAction hrel).twist i j' by abel]

theorem t200inv1_c₁e_mul_nf_right
    (v : Torus (StrothTypeIndex.t200 m).k) (i j' l : Bool) :
    (dD.ofTorus v * dD.d8 i j' l) * (dD.ofTorus (om200 m ![1, 0, 0]) * e) =
      dD.ofTorus (v + (StrothTypeIndex.t200 m).action.d8Act i j' l (om200 m ![1, 0, 0])) *
        dD.d8 i j' l * e := by
  calc (dD.ofTorus v * dD.d8 i j' l) * (dD.ofTorus (om200 m ![1, 0, 0]) * e)
      = dD.ofTorus v * (dD.d8 i j' l * dD.ofTorus (om200 m ![1, 0, 0])) * e := by group
    _ = dD.ofTorus v *
          (dD.ofTorus ((StrothTypeIndex.t200 m).action.d8Act i j' l (om200 m ![1, 0, 0])) *
            dD.d8 i j' l) * e := by rw [dD.d8_mul_ofTorus]
    _ = (dD.ofTorus v *
          dD.ofTorus ((StrothTypeIndex.t200 m).action.d8Act i j' l (om200 m ![1, 0, 0]))) *
          dD.d8 i j' l * e := by group
    _ = dD.ofTorus (v +
          (StrothTypeIndex.t200 m).action.d8Act i j' l (om200 m ![1, 0, 0])) *
          dD.d8 i j' l * e := by rw [← dD.ofTorus_add]

theorem t200inv1_c₁e_comm_nf_iff {j p : ℕ} (hrel : Rel34inv dD e j 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) (i j' l : Bool) :
    ((dD.c : G) ^ 2 ^ (m - 1) * e) * (dD.ofTorus v * dD.d8 i j' l) =
        dD.ofTorus v * dD.d8 i j' l * ((dD.c : G) ^ 2 ^ (m - 1) * e) ↔
      om200 m ![1, 0, 0] + (dD.t200inv1EAction hrel).φe v +
          (dD.t200inv1EAction hrel).twist i j' =
        v + (StrothTypeIndex.t200 m).action.d8Act i j' l (om200 m ![1, 0, 0]) := by
  rw [dD.t200_c_pow]
  rw [t200inv1_c₁e_mul_nf_left dD hrel, t200inv1_c₁e_mul_nf_right dD]
  rw [mul_right_cancel_iff, mul_right_cancel_iff, dD.ofTorus_inj.eq_iff]

theorem t200inv1_coord_cab (hrel : Rel34inv dD e 0 1 2) :
    (dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![1, 1, 1]) +
      (dD.t200inv1EAction hrel).twist true false = Torus.ofInt _ ![1, 1, 1] := by
  rw [t200inv1_φe dD hrel, t200inv1_twist_tff]
  rw [t200_add_vec]
  congr 1

theorem t200inv1_coord_a_inv_t (hrel : Rel34inv dD e 0 1 2) :
    (dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![0, -1, 0]) +
      (dD.t200inv1EAction hrel).twist false true = Torus.ofInt _ ![0, -1, 0] := by
  rw [t200inv1_φe dD hrel, t200inv1_twist_ftf]
  rw [t200_add_vec]
  congr 1

theorem t200inv1_coord_cab_c₁ (hm : 1 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) 1 2) :
    om200 m ![1, 0, 0] + (dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![1, 1, 1]) +
        (dD.t200inv1EAction hrel).twist true false =
      Torus.ofInt _ ![1, 1, 1] +
        (StrothTypeIndex.t200 m).action.d8Act true false false (om200 m ![1, 0, 0]) := by
  rw [t200inv1_φe dD hrel, t200inv1_twist_tff]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply]
  rw [t200_φuv_om hm]
  rw [om200_apply, om200_apply]
  rw [t200_add_vec, t200_add_vec, t200_add_vec]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [t200_ofInt_eq_iff]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [pow_succ, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨(-2 : ℤ), by ring⟩
  · exact ⟨(-1 : ℤ), by ring⟩
  · exact ⟨(-1 : ℤ), by ring⟩

theorem t200inv1_coord_a_inv_t_c₁ (hm : 1 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) 1 2) :
    om200 m ![1, 0, 0] + (dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![0, -1, 0]) +
        (dD.t200inv1EAction hrel).twist false true =
      Torus.ofInt _ ![0, -1, 0] +
        (StrothTypeIndex.t200 m).action.d8Act false true false (om200 m ![1, 0, 0]) := by
  rw [t200inv1_φe dD hrel, t200inv1_twist_ftf]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply]
  rw [t200_φt_om hm]
  rw [om200_apply, om200_apply]
  rw [t200_add_vec, t200_add_vec, t200_add_vec]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [t200_ofInt_eq_iff]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [pow_succ, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · simp
  · exact ⟨(1 : ℤ), by ring⟩
  · simp

theorem t200inv1_coord_F_c₁e_uv (hm : 1 ≤ m) (hrel : Rel34inv dD e 0 1 2) :
    om200 m ![1, 0, 0] +
        (dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) +
        (dD.t200inv1EAction hrel).twist true false =
      Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m] +
        (StrothTypeIndex.t200 m).action.d8Act true false false (om200 m ![1, 0, 0]) := by
  rw [t200inv1_φe dD hrel, t200inv1_twist_tff]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply]
  rw [t200_φuv_om hm]
  rw [om200_apply, om200_apply]
  rw [t200_add_vec, t200_add_vec, t200_add_vec]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [t200_ofInt_eq_iff]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [pow_succ, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨(-2 : ℤ), by ring⟩
  · exact ⟨(-1 : ℤ), by ring⟩
  · exact ⟨(-1 : ℤ), by ring⟩

theorem t200inv1_coord_F_c₁e_t (hm : 1 ≤ m) (hrel : Rel34inv dD e 0 1 2) :
    om200 m ![1, 0, 0] +
        (dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) +
        (dD.t200inv1EAction hrel).twist false true =
      Torus.ofInt _ ![0, 2 ^ m - 1, 0] +
        (StrothTypeIndex.t200 m).action.d8Act false true false (om200 m ![1, 0, 0]) := by
  rw [t200inv1_φe dD hrel, t200inv1_twist_ftf]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply]
  rw [t200_φt_om hm]
  rw [om200_apply, om200_apply]
  rw [t200_add_vec, t200_add_vec, t200_add_vec]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [t200_ofInt_eq_iff]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [pow_succ, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · simp
  · exact ⟨(1 : ℤ), by ring⟩
  · simp

theorem t200inv1_coord_F_e_uv (hm : 1 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) 1 2) :
    (dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) +
      (dD.t200inv1EAction hrel).twist true false =
        Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m] := by
  rw [t200inv1_φe dD hrel, t200inv1_twist_tff]
  rw [t200_add_vec]
  rw [t200_ofInt_eq_iff]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [pow_succ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · exact dvd_zero _
  · exact ⟨(2 : ℤ) ^ m' - 1, by push_cast; ring⟩
  · exact ⟨(2 : ℤ) ^ m' - 1, by push_cast; ring⟩

theorem t200inv1_coord_F_e_t (hm : 1 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) 1 2) :
    (dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) +
      (dD.t200inv1EAction hrel).twist false true =
        Torus.ofInt _ ![0, 2 ^ m - 1, 0] := by
  rw [t200inv1_φe dD hrel, t200inv1_twist_ftf]
  rw [t200_add_vec]
  rw [t200_ofInt_eq_iff]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [pow_succ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · exact dvd_zero _
  · refine ⟨1 - (2 : ℤ) ^ m', ?_⟩
    push_cast
    set K : ℤ := (2 : ℤ) ^ m'
    ring
  · simp

theorem t200inv1_comm_a₁_b₁ {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) (w : Torus (StrothTypeIndex.t200 m).k) :
    dD.ofTorus w * e * (dD.a : G) ^ 2 ^ (m + 1) =
        (dD.a : G) ^ 2 ^ (m + 1) * (dD.ofTorus w * e) ∧
      dD.ofTorus w * e * (dD.b : G) ^ 2 ^ (m + 1) =
        (dD.b : G) ^ 2 ^ (m + 1) * (dD.ofTorus w * e) := by
  have hf : Even j := t200inv1_even_j hj
  have hEa : e * (dD.a : G) ^ 2 ^ (m + 1) = (dD.a : G) ^ 2 ^ (m + 1) * e := by
    rw [dD.t200_a_pow]
    have h := (dD.t200inv1EAction hrel).e_mul_ofTorus (om200 m ![0, 1, 0])
    rwa [t200inv1_φe_om dD hrel hm hf] at h
  have hEb : e * (dD.b : G) ^ 2 ^ (m + 1) = (dD.b : G) ^ 2 ^ (m + 1) * e := by
    rw [dD.t200_b_pow]
    have h := (dD.t200inv1EAction hrel).e_mul_ofTorus (om200 m ![0, 0, 1])
    rwa [t200inv1_φe_om dD hrel hm hf] at h
  constructor
  · calc dD.ofTorus w * e * (dD.a : G) ^ 2 ^ (m + 1)
        = dD.ofTorus w * (e * (dD.a : G) ^ 2 ^ (m + 1)) := by group
      _ = dD.ofTorus w * ((dD.a : G) ^ 2 ^ (m + 1) * e) := by rw [hEa]
      _ = (dD.ofTorus w * (dD.a : G) ^ 2 ^ (m + 1)) * e := by group
      _ = ((dD.a : G) ^ 2 ^ (m + 1) * dD.ofTorus w) * e := by
          rw [dD.t200_a_pow, dD.ofTorus_comm]
      _ = (dD.a : G) ^ 2 ^ (m + 1) * (dD.ofTorus w * e) := by group
  · calc dD.ofTorus w * e * (dD.b : G) ^ 2 ^ (m + 1)
        = dD.ofTorus w * (e * (dD.b : G) ^ 2 ^ (m + 1)) := by group
      _ = dD.ofTorus w * ((dD.b : G) ^ 2 ^ (m + 1) * e) := by rw [hEb]
      _ = (dD.ofTorus w * (dD.b : G) ^ 2 ^ (m + 1)) * e := by group
      _ = ((dD.b : G) ^ 2 ^ (m + 1) * dD.ofTorus w) * e := by
          rw [dD.t200_b_pow, dD.ofTorus_comm]
      _ = (dD.b : G) ^ 2 ^ (m + 1) * (dD.ofTorus w * e) := by group

theorem t200inv1_comm_E'_e (hrel : Rel34inv dD e 0 1 2) :
    e * (dD.cab * dD.uv) = dD.cab * dD.uv * e ∧
      e * ((dD.a : G)⁻¹ * dD.t) = (dD.a : G)⁻¹ * dD.t * e := by
  constructor
  · rw [t200_cab_eq, ← dD.d8_tff]
    exact (t200inv1_e_comm_nf_iff dD hrel _ true false false).mpr (t200inv1_coord_cab dD hrel)
  · rw [dD.a_eq, a_eq_ofInt, ← dD.ofTorus_neg, t200_neg_vec, ← dD.d8_ftf]
    exact (t200inv1_e_comm_nf_iff dD hrel _ false true false).mpr
      (t200inv1_coord_a_inv_t dD hrel)

theorem t200inv1_comm_E'_c₁e (hm : 1 ≤ m) (hrel : Rel34inv dD e (2 ^ (m + 1)) 1 2) :
    (dD.c : G) ^ 2 ^ (m - 1) * e * (dD.cab * dD.uv) =
        dD.cab * dD.uv * ((dD.c : G) ^ 2 ^ (m - 1) * e) ∧
      (dD.c : G) ^ 2 ^ (m - 1) * e * ((dD.a : G)⁻¹ * dD.t) =
        (dD.a : G)⁻¹ * dD.t * ((dD.c : G) ^ 2 ^ (m - 1) * e) := by
  constructor
  · rw [t200_cab_eq, ← dD.d8_tff]
    exact (t200inv1_c₁e_comm_nf_iff dD hrel _ true false false).mpr
      (t200inv1_coord_cab_c₁ dD hm hrel)
  · rw [dD.a_eq, a_eq_ofInt, ← dD.ofTorus_neg, t200_neg_vec, ← dD.d8_ftf]
    exact (t200inv1_c₁e_comm_nf_iff dD hrel _ false true false).mpr
      (t200inv1_coord_a_inv_t_c₁ dD hm hrel)

theorem t200inv1_comm_F_c₁e (hm : 1 ≤ m) (hrel : Rel34inv dD e 0 1 2) :
    (dD.c : G) ^ 2 ^ (m - 1) * e *
        (dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv) =
      dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv *
        ((dD.c : G) ^ 2 ^ (m - 1) * e) ∧
    (dD.c : G) ^ 2 ^ (m - 1) * e * (dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t) =
      dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t *
        ((dD.c : G) ^ 2 ^ (m - 1) * e) := by
  constructor
  · rw [← dD.d8_tff]
    exact (t200inv1_c₁e_comm_nf_iff dD hrel _ true false false).mpr
      (t200inv1_coord_F_c₁e_uv dD hm hrel)
  · rw [← dD.d8_ftf]
    exact (t200inv1_c₁e_comm_nf_iff dD hrel _ false true false).mpr
      (t200inv1_coord_F_c₁e_t dD hm hrel)

theorem t200inv1_comm_F_e (hm : 1 ≤ m) (hrel : Rel34inv dD e (2 ^ (m + 1)) 1 2) :
    e * (dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv) =
        dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv * e ∧
      e * (dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t) =
        dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t * e := by
  constructor
  · rw [← dD.d8_tff]
    exact (t200inv1_e_comm_nf_iff dD hrel _ true false false).mpr
      (t200inv1_coord_F_e_uv dD hm hrel)
  · rw [← dD.d8_ftf]
    exact (t200inv1_e_comm_nf_iff dD hrel _ false true false).mpr
      (t200inv1_coord_F_e_t dD hm hrel)

theorem t200inv1_ofTorus_mul_e_not_mem {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) (w : Torus (StrothTypeIndex.t200 m).k) :
    dD.ofTorus w * e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
  intro hmem
  apply (dD.t200inv1EAction hrel).e_not_mem
    (fun i j l h => t200inv1_not_word dD hm hj hrel i j l h)
  have h : e = (dD.ofTorus w)⁻¹ * (dD.ofTorus w * e) := by group
  rw [h]
  exact mul_mem (inv_mem (Subgroup.mem_sup_left (dD.ofTorus_mem w))) hmem

theorem t200inv1_c₁e_mul_self {j p : ℕ} (hm : 1 ≤ m) (hrel : Rel34inv dD e j 1 p) :
    (dD.c : G) ^ 2 ^ (m - 1) * e * ((dD.c : G) ^ 2 ^ (m - 1) * e) = 1 := by
  have hc : (dD.c : G) ^ 2 ^ (m - 1) * (dD.c : G) ^ 2 ^ (m - 1) = 1 := by
    rw [dD.t200_c_pow, dD.ofTorus_mul_self, om200_add_self hm, dD.ofTorus_zero]
  have hcomm := t200inv1_e_comm_c₁ dD hm hrel
  calc (dD.c : G) ^ 2 ^ (m - 1) * e * ((dD.c : G) ^ 2 ^ (m - 1) * e)
      = (dD.c : G) ^ 2 ^ (m - 1) * (e * (dD.c : G) ^ 2 ^ (m - 1)) * e := by group
    _ = (dD.c : G) ^ 2 ^ (m - 1) * ((dD.c : G) ^ 2 ^ (m - 1) * e) * e := by rw [hcomm]
    _ = ((dD.c : G) ^ 2 ^ (m - 1) * (dD.c : G) ^ 2 ^ (m - 1)) * (e * e) := by group
    _ = 1 := by rw [hc, hrel.e_sq, mul_one]

end Stroth47Core

end CFSG.CGT.Stroth77
