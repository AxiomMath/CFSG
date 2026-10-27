module

public import CFSG.CGT.Stroth77.Section43CoreE
public import CFSG.CGT.Stroth77.Extension22
public import Mathlib.Tactic.Linarith

public section

namespace CFSG.CGT.Stroth77

open Matrix

open Stroth42Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m))

theorem iii_ofInt_mul (x y : Fin 3 → ℤ) (z : G) :
    dD.ofTorus (Torus.ofInt _ x) * (dD.ofTorus (Torus.ofInt _ y) * z) =
      dD.ofTorus (Torus.ofInt _ (x + y)) * z := by
  rw [← mul_assoc, ← dD.ofTorus_add, Torus.ofInt_add]

theorem iii_ofInt_mul' (x y : Fin 3 → ℤ) :
    dD.ofTorus (Torus.ofInt _ x) * dD.ofTorus (Torus.ofInt _ y) =
      dD.ofTorus (Torus.ofInt _ (x + y)) := by
  rw [← dD.ofTorus_add, Torus.ofInt_add]

theorem iii_uv_mul_ofInt (x : Fin 3 → ℤ) (z : G) :
    dD.uv * (dD.ofTorus (Torus.ofInt _ x) * z) = dD.ofTorus (Torus.ofInt _ 
      ![-3 * x 0 + 2 * x 1 + 2 * x 2, -2 * x 0 + x 1 + 2 * x 2, -2 * x 0 + 2 * x 1 + x 2]) *
        (dD.uv * z) := by
  rw [dD.uv_mul_ofTorus_mul, t100_φuv]

theorem iii_t_mul_ofInt (x : Fin 3 → ℤ) (z : G) :
    dD.t * (dD.ofTorus (Torus.ofInt _ x) * z) =
      dD.ofTorus (Torus.ofInt _ ![x 0 - 2 * x 2, 2 * x 0 - x 1 - 2 * x 2, -x 2]) * (dD.t * z) := by
  rw [dD.t_mul_ofTorus_mul, t100_φt]

theorem iii_u_mul_ofInt (x : Fin 3 → ℤ) (z : G) :
    dD.u * (dD.ofTorus (Torus.ofInt _ x) * z) =
      dD.ofTorus (Torus.ofInt _ ![x 0, x 2, x 1]) * (dD.u * z) := by
  rw [dD.u_mul_ofTorus_mul, t100_φu]

theorem iii_uv_mul_ofInt' (x : Fin 3 → ℤ) :
    dD.uv * dD.ofTorus (Torus.ofInt _ x) = dD.ofTorus (Torus.ofInt _ 
      ![-3 * x 0 + 2 * x 1 + 2 * x 2, -2 * x 0 + x 1 + 2 * x 2, -2 * x 0 + 2 * x 1 + x 2]) *
        dD.uv := by
  rw [dD.uv_mul_ofTorus, t100_φuv]

theorem iii_t_mul_ofInt' (x : Fin 3 → ℤ) :
    dD.t * dD.ofTorus (Torus.ofInt _ x) =
      dD.ofTorus (Torus.ofInt _ ![x 0 - 2 * x 2, 2 * x 0 - x 1 - 2 * x 2, -x 2]) * dD.t := by
  rw [dD.t_mul_ofTorus, t100_φt]

theorem iii_u_mul_ofInt' (x : Fin 3 → ℤ) :
    dD.u * dD.ofTorus (Torus.ofInt _ x) = dD.ofTorus (Torus.ofInt _ ![x 0, x 2, x 1]) * dD.u := by
  rw [dD.u_mul_ofTorus, t100_φu]


theorem iii_u_mul_t' : dD.u * dD.t = dD.uv * (dD.t * dD.u) := by rw [dD.u_mul_t_eq, mul_assoc]

theorem iii_c_npow (n : ℕ) : (dD.c : G) ^ n = dD.ofTorus (Torus.ofInt _ ![(n : ℤ), 0, 0]) := by
  rw [c_eq, ← ofTorus_nsmul]
  congr 1
  funext i
  fin_cases i <;> simp [gen, Pi.single_apply]

theorem iii_a_npow (n : ℕ) : (dD.a : G) ^ n = dD.ofTorus (Torus.ofInt _ ![0, (n : ℤ), 0]) := by
  rw [a_eq, ← ofTorus_nsmul]
  congr 1
  funext i
  fin_cases i <;> simp [gen, Pi.single_apply]

theorem iii_b_npow (n : ℕ) : (dD.b : G) ^ n = dD.ofTorus (Torus.ofInt _ ![0, 0, (n : ℤ)]) := by
  rw [b_eq, ← ofTorus_nsmul]
  congr 1
  funext i
  fin_cases i <;> simp [gen, Pi.single_apply]

theorem iii_c_ofInt : (dD.c : G) = dD.ofTorus (Torus.ofInt _ ![1, 0, 0]) := by
  simpa using dD.iii_c_npow 1

theorem iii_a_ofInt : (dD.a : G) = dD.ofTorus (Torus.ofInt _ ![0, 1, 0]) := by
  simpa using dD.iii_a_npow 1

theorem iii_b_ofInt : (dD.b : G) = dD.ofTorus (Torus.ofInt _ ![0, 0, 1]) := by
  simpa using dD.iii_b_npow 1

theorem iii_ofInt_inv (x : Fin 3 → ℤ) :
    (dD.ofTorus (Torus.ofInt _ x))⁻¹ = dD.ofTorus (Torus.ofInt _ (-x)) := by
  rw [← dD.ofTorus_neg, Torus.ofInt_neg]

theorem iii_ofInt_npow (x : Fin 3 → ℤ) (n : ℕ) :
    (dD.ofTorus (Torus.ofInt _ x)) ^ n = dD.ofTorus (Torus.ofInt _ ((n : ℤ) • x)) := by
  rw [← dD.ofTorus_nsmul, Torus.ofInt_zsmul, natCast_zsmul]

theorem iii_ofInt_mul_eq {x y : Fin 3 → ℤ} (z : G)
    (h0 : (2 : ℤ) ^ m ∣ y 0 - x 0) (h1 : (2 : ℤ) ^ (m + 1) ∣ y 1 - x 1)
    (h2 : (2 : ℤ) ^ (m + 1) ∣ y 2 - x 2) :
    dD.ofTorus (Torus.ofInt _ x) * z = dD.ofTorus (Torus.ofInt _ y) * z := by
  rw [(t100_ofInt_eq_iff x y).mpr ⟨h0, h1, h2⟩]

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_e_conj_ofTorus (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹)
    (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹) (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹)
    (x : Fin 3 → ℤ) :
    e⁻¹ * dD.ofTorus (Torus.ofInt _ x) * e = dD.ofTorus (Torus.ofInt _ (-x)) := by
  have hconj : ∀ g : G, e⁻¹ * g * e = MulAut.conj e⁻¹ g := fun g => by
    rw [MulAut.conj_apply, inv_inv]
  rw [hconj, dD.ofTorus_ofInt, dD.ofTorus_ofInt, map_mul, map_mul, map_zpow,
    map_zpow, map_zpow, ← hconj, ← hconj, ← hconj, hce, hae, hbe]
  simp only [Pi.neg_apply, zpow_neg, inv_zpow]

theorem iii_e_inv (he : e * e = 1) : e⁻¹ = e := inv_eq_of_mul_eq_one_right he

theorem iii_e_mul_ofInt (he : e * e = 1) (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹)
    (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹) (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹)
    (x : Fin 3 → ℤ) (z : G) :
    e * (dD.ofTorus (Torus.ofInt _ x) * z) = dD.ofTorus (Torus.ofInt _ (-x)) * (e * z) := by
  have h := dD.iii_e_conj_ofTorus hce hae hbe x
  rw [iii_e_inv he] at h
  rw [← h, mul_assoc, mul_assoc, ← mul_assoc e e z, he, one_mul, ← mul_assoc]

theorem iii_e_mul_uv (he : e * e = 1)
    (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv) (z : G) :
    e * (dD.uv * z) = dD.ofTorus (Torus.ofInt _ ![2, 1, 1]) * (dD.uv * (e * z)) := by
  have h : (dD.c : G) ^ 2 * dD.a * dD.b = dD.ofTorus (Torus.ofInt _ ![2, 1, 1]) := by
    rw [dD.iii_c_npow, dD.iii_a_ofInt, dD.iii_b_ofInt, dD.iii_ofInt_mul',
      dD.iii_ofInt_mul']
    congr 2
    funext i
    fin_cases i <;> simp
  rw [iii_e_inv he, h] at heuv
  calc e * (dD.uv * z) = e * dD.uv * e * (e * z) := by
        rw [mul_assoc (e * dD.uv) e, ← mul_assoc e e z, he, one_mul, mul_assoc]
    _ = _ := by rw [heuv, mul_assoc]

theorem iii_e_mul_t (he : e * e = 1) (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (z : G) :
    e * (dD.t * z) = dD.ofTorus (Torus.ofInt _ ![0, -1, 0]) * (dD.t * (e * z)) := by
  have h : (dD.a : G)⁻¹ = dD.ofTorus (Torus.ofInt _ ![0, -1, 0]) := by
    rw [dD.iii_a_ofInt, dD.iii_ofInt_inv]
    congr 2
    funext i
    fin_cases i <;> simp
  rw [iii_e_inv he, h] at het
  calc e * (dD.t * z) = e * dD.t * e * (e * z) := by
        rw [mul_assoc (e * dD.t) e, ← mul_assoc e e z, he, one_mul, mul_assoc]
    _ = _ := by rw [het, mul_assoc]

theorem iii_e_mul_u (he : e * e = 1) (hue : e⁻¹ * dD.u * e = dD.u) (z : G) :
    e * (dD.u * z) = dD.u * (e * z) := by
  rw [iii_e_inv he] at hue
  calc e * (dD.u * z) = e * dD.u * e * (e * z) := by
        rw [mul_assoc (e * dD.u) e, ← mul_assoc e e z, he, one_mul, mul_assoc]
    _ = _ := by rw [hue]

theorem iii_e_mul_e (he : e * e = 1) (z : G) : e * (e * z) = z := by
  rw [← mul_assoc, he, one_mul]

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_eq_of_nf {A B : G}
    (h : dD.ofTorus (Torus.ofInt _ 0) * (A * 1) = dD.ofTorus (Torus.ofInt _ 0) * (B * 1)) :
    A = B := by
  simpa [Torus.ofInt_zero, dD.ofTorus_zero] using h

theorem t100_iii_hr2 : (dD.c : G) * dD.a * dD.uv * ((dD.c : G) * dD.a * dD.uv) = 1 := by
  apply dD.iii_eq_of_nf
  rw [dD.iii_c_ofInt, dD.iii_a_ofInt]
  simp only [mul_assoc, iii_ofInt_mul, iii_uv_mul_ofInt, iii_t_mul_ofInt, iii_u_mul_ofInt,
    uv_mul_uv, t_mul_t, u_mul_u, t_mul_uv, u_mul_uv, u_mul_t, one_mul]
  refine dD.iii_ofInt_mul_eq _ ?_ ?_ ?_ <;> simp

theorem t100_iii_hrue (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (hue : e⁻¹ * dD.u * e = dD.u) (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹)
    (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹) (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹)
    (he : e * e = 1) :
    (dD.c : G) * dD.a * dD.uv * (dD.u * e) = dD.u * e * ((dD.c : G) * dD.a * dD.uv) := by
  have r1 := dD.iii_e_mul_ofInt he hce hae hbe
  have r2 := dD.iii_e_mul_uv he heuv
  have r4 := dD.iii_e_mul_u he hue
  apply dD.iii_eq_of_nf
  rw [dD.iii_c_ofInt, dD.iii_a_ofInt]
  simp only [mul_assoc, iii_ofInt_mul, iii_uv_mul_ofInt, iii_t_mul_ofInt, iii_u_mul_ofInt,
    uv_mul_uv, t_mul_t, u_mul_u, t_mul_uv, u_mul_uv, u_mul_t, one_mul, r1, r2, r4]
  refine dD.iii_ofInt_mul_eq _ ?_ ?_ ?_ <;> simp

theorem t100_iii_hrta (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1) :
    (dD.t * dD.a)⁻¹ * ((dD.c : G) * dD.a * dD.uv * (dD.u * e)) * (dD.t * dD.a) =
      (dD.c : G) * dD.u * e := by
  have r1 := dD.iii_e_mul_ofInt he hce hae hbe
  have r2 := dD.iii_e_mul_uv he heuv
  have r3 := dD.iii_e_mul_t he het
  have r4 := dD.iii_e_mul_u he hue
  apply dD.iii_eq_of_nf
  rw [mul_inv_rev, dD.t_inv, dD.iii_c_ofInt, dD.iii_a_ofInt, dD.iii_ofInt_inv]
  simp only [mul_assoc, iii_ofInt_mul, iii_uv_mul_ofInt, iii_t_mul_ofInt, iii_u_mul_ofInt,
    uv_mul_uv, t_mul_t, u_mul_u, t_mul_uv, u_mul_uv, u_mul_t, one_mul, r1, r2, r3, r4]
  refine dD.iii_ofInt_mul_eq _ ?_ ?_ ?_ <;> simp

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_zpowers_u_le_normalizer : Subgroup.zpowers dD.u ≤ Subgroup.normalizer (D : Set G) := by
  rw [Subgroup.zpowers_le]
  exact dD.u_mem

theorem iii_mem_Du_iff {y : G} :
    y ∈ D ⊔ Subgroup.zpowers dD.u ↔
      ∃ (v : Torus (StrothTypeIndex.t100 m).k) (l : Bool),
        y = dD.ofTorus v * dD.d8 false false l := by
  rw [← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left D _ dD.iii_zpowers_u_le_normalizer,
    Set.mem_mul]
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    obtain ⟨v, rfl⟩ := dD.exists_ofTorus hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · refine ⟨v, false, ?_⟩
      rw [← two_mul, zpow_mul, zpow_two, dD.u_sq, one_zpow, d8_fff]
    · refine ⟨v, true, ?_⟩
      rw [zpow_add, zpow_mul, zpow_two, dD.u_sq, one_zpow, one_mul, zpow_one, d8_fft]
  · rintro ⟨v, l, rfl⟩
    refine ⟨_, dD.ofTorus_mem v, _, ?_, rfl⟩
    cases l
    · rw [d8_fff]; exact one_mem _
    · rw [d8_fft]; exact Subgroup.mem_zpowers _

theorem t100_iii_hC11 (hm : 2 ≤ m) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * e ∈ D ⊔ Subgroup.zpowers dD.u → y * y = 1 →
        ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
          q⁻¹ * y * q = (dD.c : G) ^ 2 ^ (m - 1) * y := by
  intro y _ hye _
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have r1 := dD.iii_e_mul_ofInt he hce hae hbe
  have r4 := dD.iii_e_mul_u he hue
  obtain ⟨v, l, hv⟩ := dD.iii_mem_Du_iff.mp hye
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hy : y = dD.ofTorus (Torus.ofInt _ x) * dD.d8 false false l * e := by
    rw [← hv, mul_assoc, he, mul_one]
  refine ⟨(dD.c : G) ^ 2 ^ n, Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (Subgroup.pow_mem _ (dD.c : D).2 _)), ?_⟩
  subst hy
  apply dD.iii_eq_of_nf
  cases l <;>
  · simp only [d8_fff, d8_fft, dD.iii_c_npow, dD.iii_ofInt_inv]
    simp only [mul_assoc, iii_ofInt_mul, iii_uv_mul_ofInt, iii_t_mul_ofInt, iii_u_mul_ofInt,
      uv_mul_uv, t_mul_t, u_mul_u, t_mul_uv, u_mul_uv, u_mul_t, one_mul, r1, r4]
    refine dD.iii_ofInt_mul_eq _ ?_ ?_ ?_ <;> simp <;> exact ⟨1, by ring⟩

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_ofTorus_mem (v : Torus (StrothTypeIndex.t100 m).k) :
    dD.ofTorus v ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (dD.ofTorus_mem v))

theorem iii_uv_mem : dD.uv ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))

theorem iii_t_mem : dD.t ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))

theorem iii_e_mem : e ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers e)

theorem iii_e_mul_ofInt' (he : e * e = 1) (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹)
    (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹) (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹)
    (x : Fin 3 → ℤ) : e * dD.ofTorus (Torus.ofInt _ x) = dD.ofTorus (Torus.ofInt _ (-x)) * e := by
  simpa using dD.iii_e_mul_ofInt he hce hae hbe x 1

theorem iii_e_mul_uv' (he : e * e = 1)
    (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv) :
    e * dD.uv = dD.ofTorus (Torus.ofInt _ ![2, 1, 1]) * (dD.uv * e) := by
  simpa using dD.iii_e_mul_uv he heuv 1

theorem iii_e_mul_t' (he : e * e = 1) (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) :
    e * dD.t = dD.ofTorus (Torus.ofInt _ ![0, -1, 0]) * (dD.t * e) := by
  simpa using dD.iii_e_mul_t he het 1

theorem iii_e_mul_u' (he : e * e = 1) (hue : e⁻¹ * dD.u * e = dD.u) : e * dD.u = dD.u * e := by
  simpa using dD.iii_e_mul_u he hue 1

theorem iii_ofInt_eq {x y : Fin 3 → ℤ}
    (h0 : (2 : ℤ) ^ m ∣ y 0 - x 0) (h1 : (2 : ℤ) ^ (m + 1) ∣ y 1 - x 1)
    (h2 : (2 : ℤ) ^ (m + 1) ∣ y 2 - x 2) :
    dD.ofTorus (Torus.ofInt _ x) = dD.ofTorus (Torus.ofInt _ y) := by
  rw [(t100_ofInt_eq_iff x y).mpr ⟨h0, h1, h2⟩]

end StrothWeakTypeData

namespace Stroth43Core

private theorem isConj_of_conj {G : Type*} [Group G] {y z : G} (q : G) (h : q⁻¹ * y * q = z) :
    IsConj y z :=
  isConj_iff.mpr ⟨q⁻¹, by rw [inv_inv]; exact h⟩

end Stroth43Core

open Stroth43Core

set_option hygiene false in
local macro "iii_rels" : tactic => `(tactic| (
  have r1 := dD.iii_e_mul_ofInt he hce hae hbe
  have r1' := dD.iii_e_mul_ofInt' he hce hae hbe
  have r2 := dD.iii_e_mul_uv he heuv
  have r2' := dD.iii_e_mul_uv' he heuv
  have r3 := dD.iii_e_mul_t he het
  have r3' := dD.iii_e_mul_t' he het
  have r4 := dD.iii_e_mul_u he hue
  have r4' := dD.iii_e_mul_u' he hue
  have r5 := StrothWeakTypeData.iii_e_mul_e he
  have r6 := StrothWeakTypeData.iii_e_inv he))

set_option hygiene false in
local macro "iii_nf" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [mul_inv_rev, r6, dD.uv_inv, dD.t_inv,
  dD.u_inv, dD.iii_ofInt_inv, dD.iii_ofInt_npow, mul_assoc, dD.iii_ofInt_mul,
  dD.iii_ofInt_mul',
  dD.iii_uv_mul_ofInt, dD.iii_t_mul_ofInt, dD.iii_u_mul_ofInt, dD.iii_uv_mul_ofInt',
  dD.iii_t_mul_ofInt',
  dD.iii_u_mul_ofInt', dD.uv_mul_uv, dD.t_mul_t, dD.u_mul_u, dD.t_mul_uv, dD.u_mul_uv, dD.u_mul_t,
  dD.uv_sq, dD.t_sq, dD.u_sq, dD.uv_comm_t.symm, dD.uv_comm_u.symm, dD.iii_u_mul_t', one_mul,
  mul_one, r1, r1', r2, r2', r3, r3', r4, r4', r5, he] $[$loc]?)

set_option hygiene false in
local macro "s_nf" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [mul_inv_rev, dD.uv_inv, dD.t_inv,
  dD.u_inv, dD.iii_ofInt_inv, dD.iii_ofInt_npow, mul_assoc, dD.iii_ofInt_mul,
  dD.iii_ofInt_mul',
  dD.iii_uv_mul_ofInt, dD.iii_t_mul_ofInt, dD.iii_u_mul_ofInt, dD.iii_uv_mul_ofInt',
  dD.iii_t_mul_ofInt',
  dD.iii_u_mul_ofInt', dD.uv_mul_uv, dD.t_mul_t, dD.u_mul_u, dD.t_mul_uv, dD.u_mul_uv, dD.u_mul_t,
  dD.uv_sq, dD.t_sq, dD.u_sq, dD.uv_comm_t.symm, dD.uv_comm_u.symm, dD.iii_u_mul_t', one_mul,
  mul_one] $[$loc]?)

local macro "nf_coord" : tactic => `(tactic| first
  | (refine StrothWeakTypeData.iii_ofInt_mul_eq _ _ ?_ ?_ ?_ <;>
      simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.zero_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_succ, Nat.cast_pow, Nat.cast_ofNat, Pi.smul_apply, smul_eq_mul])
  | (refine StrothWeakTypeData.iii_ofInt_eq _ ?_ ?_ ?_ <;>
      simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.zero_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_succ, Nat.cast_pow, Nat.cast_ofNat, Pi.smul_apply, smul_eq_mul]))

local macro "dvd_const" : tactic => `(tactic| first
  | exact dvd_zero _
  | (refine ⟨0, ?_⟩; ring1) | (refine ⟨1, ?_⟩; ring1) | (refine ⟨-1, ?_⟩; ring1)
  | (refine ⟨2, ?_⟩; ring1) | (refine ⟨-2, ?_⟩; ring1) | (refine ⟨3, ?_⟩; ring1)
  | (refine ⟨-3, ?_⟩; ring1) | (refine ⟨4, ?_⟩; ring1) | (refine ⟨-4, ?_⟩; ring1)
  | (refine ⟨5, ?_⟩; ring1) | (refine ⟨-5, ?_⟩; ring1) | (refine ⟨6, ?_⟩; ring1)
  | (refine ⟨-6, ?_⟩; ring1) | (refine ⟨8, ?_⟩; ring1) | (refine ⟨-8, ?_⟩; ring1))

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_uv_cond {x0 x1 x2 : ℤ}
    (h : dD.ofTorus (Torus.ofInt _ ![x0, x1, x2]) * dD.uv *
      (dD.ofTorus (Torus.ofInt _ ![x0, x1, x2]) * dD.uv) = 1) :
    (2 : ℤ) ^ m ∣ x1 + x2 - x0 := by
  s_nf at h
  rw [ofTorus_eq_one_iff, t100_ofInt_eq_zero_iff] at h
  obtain ⟨-, h1, -⟩ := h
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h1
  rw [pow_succ', show x1 + (-2 * x0 + x1 + 2 * x2) = 2 * (x1 + x2 - x0) by ring] at h1
  exact (mul_dvd_mul_iff_left two_ne_zero).mp h1

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_uv_param {x : Fin 3 → ℤ}
    (h : dD.ofTorus (Torus.ofInt _ x) * dD.uv * (dD.ofTorus (Torus.ofInt _ x) * dD.uv) = 1) :
    dD.ofTorus (Torus.ofInt _ x) = dD.ofTorus (Torus.ofInt _ ![x 1 + x 2, x 1, x 2]) := by
  have hx : x = ![x 0, x 1, x 2] := by funext i; fin_cases i <;> rfl
  rw [hx] at h ⊢
  have hc := dD.iii_uv_cond h
  refine dD.iii_ofInt_eq ?_ ?_ ?_ <;> simp
  exact hc

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_uv_parity {x : Fin 3 → ℤ} (hm : 1 ≤ m)
    (h : dD.ofTorus (Torus.ofInt _ x) * dD.uv * (dD.ofTorus (Torus.ofInt _ x) * dD.uv) = 1) :
    Even (x 0) ↔ Even (x 1 + x 2) := by
  have hx : x = ![x 0, x 1, x 2] := by funext i; fin_cases i <;> rfl
  rw [hx] at h
  have hc := dD.iii_uv_cond h
  have h2 : (2 : ℤ) ∣ x 1 + x 2 - x 0 := (dvd_pow_self 2 (by omega)).trans hc
  constructor
  · intro h0
    have := h0.two_dvd
    exact even_iff_two_dvd.mpr (by simpa using dvd_add h2 this)
  · intro h0
    have := h0.two_dvd
    exact even_iff_two_dvd.mpr (by simpa using dvd_sub this h2)

theorem iii_cls_uv (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1)
    (hm : 1 ≤ m) {x : Fin 3 → ℤ}
    (h : dD.ofTorus (Torus.ofInt _ x) * dD.uv * (dD.ofTorus (Torus.ofInt _ x) * dD.uv) = 1) :
    (Even (x 0) → ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        q⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * dD.uv) * q = dD.uv) ∧
      (¬ Even (x 0) → ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        q⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * dD.uv) * q = (dD.c : G) * dD.a * dD.uv) := by
  iii_rels
  have hpar := dD.iii_uv_parity hm h
  rw [hpar, dD.iii_uv_param h]
  obtain ⟨p, hp | hp⟩ := Int.even_or_odd' (x 1) <;>
  obtain ⟨r, hr | hr⟩ := Int.even_or_odd' (x 2) <;>
  rw [hp, hr]
  ·
    refine ⟨fun _ => ⟨dD.ofTorus (Torus.ofInt _ ![0, -r, -p]), dD.iii_ofTorus_mem (e := e) _, ?_⟩,
      fun hod => absurd ⟨p + r, by ring⟩ hod⟩
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> ring_nf <;> exact dvd_zero _
  ·
    refine ⟨fun hev => absurd hev (Int.not_even_iff_odd.mpr ⟨p + r, by ring⟩), fun _ =>
      ⟨dD.ofTorus (Torus.ofInt _ ![0, -r, -p]) * e,
        mul_mem (dD.iii_ofTorus_mem (e := e) _) (dD.iii_e_mem (e := e)), ?_⟩⟩
    rw [dD.iii_c_ofInt, dD.iii_a_ofInt]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> ring_nf <;> exact dvd_zero _
  ·
    refine ⟨fun hev => absurd hev (Int.not_even_iff_odd.mpr ⟨p + r, by ring⟩), fun _ =>
      ⟨dD.ofTorus (Torus.ofInt _ ![0, -r, -p]), dD.iii_ofTorus_mem (e := e) _, ?_⟩⟩
    rw [dD.iii_c_ofInt, dD.iii_a_ofInt]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> ring_nf <;> exact dvd_zero _
  ·
    refine ⟨fun _ => ⟨e * dD.ofTorus (Torus.ofInt _ ![0, r, p]),
        mul_mem (dD.iii_e_mem (e := e)) (dD.iii_ofTorus_mem (e := e) _), ?_⟩,
      fun hod => absurd ⟨p + r + 1, by ring⟩ hod⟩
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> ring_nf <;> exact dvd_zero _

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_dvd_of_eq_one {X : Fin 3 → ℤ} (h : dD.ofTorus (Torus.ofInt _ X) = 1) :
    (2 : ℤ) ^ m ∣ X 0 ∧ (2 : ℤ) ^ (m + 1) ∣ X 1 ∧ (2 : ℤ) ^ (m + 1) ∣ X 2 := by
  rwa [ofTorus_eq_one_iff, t100_ofInt_eq_zero_iff] at h

theorem iii_cls_u (hm : 2 ≤ m) {x : Fin 3 → ℤ}
    (h : dD.ofTorus (Torus.ofInt _ x) * dD.u * (dD.ofTorus (Torus.ofInt _ x) * dD.u) = 1) :
    ∃ q ∈ D, q⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * dD.u) * q = dD.u ∨
      q⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * dD.u) * q = (dD.c : G) ^ 2 ^ (m - 1) * dD.u := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  s_nf at h
  obtain ⟨h0, h1, -⟩ := dD.iii_dvd_of_eq_one h
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1
  obtain ⟨s, hs⟩ : (2 : ℤ) ^ (n + 1) ∣ x 0 := by
    have : x 0 + x 0 = 2 * x 0 := by ring
    rw [this, show (2 : ℤ) ^ (n + 2) = 2 * 2 ^ (n + 1) by ring] at h0
    exact (mul_dvd_mul_iff_left two_ne_zero).mp h0
  obtain ⟨w, hw⟩ := h1
  have hx : dD.ofTorus (Torus.ofInt _ x) =
      dD.ofTorus (Torus.ofInt _ ![s * 2 ^ (n + 1), x 1, -x 1]) := by
    refine dD.iii_ofInt_eq ?_ ?_ ?_ <;> simp
    · exact ⟨0, by rw [hs]; ring⟩
    · exact ⟨-w, by linear_combination -hw⟩
  refine ⟨dD.ofTorus (Torus.ofInt _ ![0, x 1, 0]), dD.ofTorus_mem _, ?_⟩
  rw [hx]
  obtain ⟨s', hs' | hs'⟩ := Int.even_or_odd' s
  · left
    apply dD.iii_eq_of_nf; s_nf; nf_coord <;> (try rw [hs']) <;> ring_nf <;>
      first | exact dvd_zero _ | exact ⟨-s', by ring⟩
  · right
    rw [dD.iii_c_npow]
    apply dD.iii_eq_of_nf; s_nf; nf_coord <;> (try rw [hs']) <;> push_cast <;> ring_nf <;>
      first | exact dvd_zero _ | exact ⟨-s', by ring⟩

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_conj_uv_ofTorus (v : Torus (StrothTypeIndex.t100 m).k) :
    dD.uv⁻¹ * dD.ofTorus v * dD.uv = dD.ofTorus ((StrothTypeIndex.t100 m).action.φuv v) :=
  dD.conj_ofTorus dD.uv_mem dD.uv_conj v

theorem iii_conj_t_ofTorus (v : Torus (StrothTypeIndex.t100 m).k) :
    dD.t⁻¹ * dD.ofTorus v * dD.t = dD.ofTorus ((StrothTypeIndex.t100 m).action.φt v) :=
  dD.conj_ofTorus dD.t_mem dD.t_conj v

theorem iii_conj_u_ofTorus (v : Torus (StrothTypeIndex.t100 m).k) :
    dD.u⁻¹ * dD.ofTorus v * dD.u = dD.ofTorus ((StrothTypeIndex.t100 m).action.φu v) :=
  dD.conj_ofTorus dD.u_mem dD.u_conj v

theorem iii_conj_mul (y p q : G) : (p * q)⁻¹ * y * (p * q) = q⁻¹ * (p⁻¹ * y * p) * q := by group

theorem iii_cls_D (hm : 2 ≤ m) {y : G} (hy : y ∈ D) (h2 : y * y = 1) (h1 : y ≠ 1) :
    IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨ IsConj y ((dD.a : G) ^ 2 ^ m) := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨ε, hε, rfl⟩ := dD.t100_eq_om_of_mul_self hm1 hy h2
  have hεv : ε = ![ε 0, ε 1, ε 2] := by funext i; fin_cases i <;> rfl
  rw [dD.t100_c_pow, dD.t100_a_pow]
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1' | h1' <;> rcases hε 2 with h2' | h2' <;>
    rw [hεv, h0, h1', h2']
  · exact absurd (by rw [hεv, h0, h1', h2', show (![0, 0, 0] : Fin 3 → ℤ) = 0 by decide,
      om100_zero, dD.ofTorus_zero]) h1
  ·
    right
    exact isConj_of_conj dD.u (by
      rw [dD.iii_conj_u_ofTorus, t100_φu_om]
      exact congrArg dD.ofTorus ((om100_eq_iff hm1 _ _).mpr (by decide)))
  · right; exact IsConj.refl _
  ·
    right
    have h1 : IsConj (dD.ofTorus (om100 m ![0, 1, 1])) (dD.ofTorus (om100 m ![0, 0, 1])) :=
      isConj_of_conj dD.ρ⁻¹ (by
        rw [inv_inv, dD.rho_mul_ofTorus_mul_rho_inv, t100_φρ_om hm1, t100_φρ_om hm1]
        exact congrArg dD.ofTorus ((om100_eq_iff hm1 _ _).mpr (by decide)))
    have h2 : IsConj (dD.ofTorus (om100 m ![0, 0, 1])) (dD.ofTorus (om100 m ![0, 1, 0])) :=
      isConj_of_conj dD.u (by
        rw [dD.iii_conj_u_ofTorus, t100_φu_om]
        exact congrArg dD.ofTorus ((om100_eq_iff hm1 _ _).mpr (by decide)))
    exact h1.trans h2
  · left; exact IsConj.refl _
  ·
    left
    exact isConj_of_conj (dD.uv * dD.t) (by
      rw [iii_conj_mul, dD.iii_conj_uv_ofTorus, t100_φuv_om hm1, dD.iii_conj_t_ofTorus,
        t100_φt_om hm1]
      exact congrArg dD.ofTorus ((om100_eq_iff hm1 _ _).mpr (by decide)))
  ·
    left
    exact isConj_of_conj dD.t (by
      rw [dD.iii_conj_t_ofTorus, t100_φt_om hm1]
      exact congrArg dD.ofTorus ((om100_eq_iff hm1 _ _).mpr (by decide)))
  ·
    left
    exact isConj_of_conj dD.uv (by
      rw [dD.iii_conj_uv_ofTorus, t100_φuv_om hm1]
      exact congrArg dD.ofTorus ((om100_eq_iff hm1 _ _).mpr (by decide)))

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_cls_e (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1)
    (x : Fin 3 → ℤ) :
    (Even (x 0) → ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        q⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * e) * q = e) ∧
      (¬ Even (x 0) → ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        q⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * e) * q = (dD.c : G) * e) := by
  iii_rels
  have hx : x = ![x 0, x 1, x 2] := by funext i; fin_cases i <;> rfl
  rw [hx]
  have hD := fun v => dD.iii_ofTorus_mem (e := e) v
  have hUV := dD.iii_uv_mem (e := e)
  have hT := dD.iii_t_mem (e := e)
  obtain ⟨p0, h0 | h0⟩ := Int.even_or_odd' (x 0) <;>
  obtain ⟨p1, h1 | h1⟩ := Int.even_or_odd' (x 1) <;>
  obtain ⟨p2, h2 | h2⟩ := Int.even_or_odd' (x 2) <;>
  simp only [h0, h1, h2, Matrix.cons_val_zero]
  · refine ⟨fun _ => ⟨dD.ofTorus (Torus.ofInt _ ![p0, p1, p2]), hD _, ?_⟩,
      fun hod => absurd ⟨p0, by ring⟩ hod⟩
    (try rw [dD.iii_c_ofInt]); apply dD.iii_eq_of_nf; iii_nf
    nf_coord <;> ring_nf <;> exact dvd_zero _
  · refine ⟨fun _ => ⟨dD.ofTorus (Torus.ofInt _ ![p0, p1, p2]) * (dD.uv * dD.t),
      mul_mem (hD _) (mul_mem hUV hT), ?_⟩, fun hod => absurd ⟨p0, by ring⟩ hod⟩
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> ring_nf <;> exact dvd_zero _
  · refine ⟨fun _ => ⟨dD.ofTorus (Torus.ofInt _ ![p0, p1, p2]) * dD.t,
      mul_mem (hD _) hT, ?_⟩, fun hod => absurd ⟨p0, by ring⟩ hod⟩
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> ring_nf <;> exact dvd_zero _
  · refine ⟨fun _ => ⟨dD.ofTorus (Torus.ofInt _ ![p0, p1, p2]) *
      (dD.uv * dD.ofTorus (Torus.ofInt _ ![1, 1, 1])), mul_mem (hD _) (mul_mem hUV (hD _)), ?_⟩,
      fun hod => absurd ⟨p0, by ring⟩ hod⟩
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> ring_nf <;> exact dvd_zero _
  · refine ⟨fun hev => absurd hev (Int.not_even_iff_odd.mpr ⟨p0, by ring⟩), fun _ =>
      ⟨dD.ofTorus (Torus.ofInt _ ![p0, p1, p2]), hD _, ?_⟩⟩
    (try rw [dD.iii_c_ofInt]); apply dD.iii_eq_of_nf; iii_nf
    nf_coord <;> ring_nf <;> exact dvd_zero _
  · refine ⟨fun hev => absurd hev (Int.not_even_iff_odd.mpr ⟨p0, by ring⟩), fun _ =>
      ⟨dD.ofTorus (Torus.ofInt _ ![p0, p1, p2]) * (dD.uv * dD.t *
        dD.ofTorus (Torus.ofInt _ ![0, 0, 1])), mul_mem (hD _) (mul_mem (mul_mem hUV hT) (hD _)),
        ?_⟩⟩
    (try rw [dD.iii_c_ofInt]); apply dD.iii_eq_of_nf; iii_nf
    nf_coord <;> ring_nf <;> exact dvd_zero _
  · refine ⟨fun hev => absurd hev (Int.not_even_iff_odd.mpr ⟨p0, by ring⟩), fun _ =>
      ⟨dD.ofTorus (Torus.ofInt _ ![p0, p1, p2]) * (dD.t * dD.ofTorus (Torus.ofInt _ ![0, 1, 0])),
        mul_mem (hD _) (mul_mem hT (hD _)), ?_⟩⟩
    (try rw [dD.iii_c_ofInt]); apply dD.iii_eq_of_nf; iii_nf
    nf_coord <;> ring_nf <;> exact dvd_zero _
  · refine ⟨fun hev => absurd hev (Int.not_even_iff_odd.mpr ⟨p0, by ring⟩), fun _ =>
      ⟨dD.ofTorus (Torus.ofInt _ ![p0, p1, p2]) * (dD.uv * dD.ofTorus (Torus.ofInt _ ![-1, 0, 0])),
        mul_mem (hD _) (mul_mem hUV (hD _)), ?_⟩⟩
    (try rw [dD.iii_c_ofInt]); apply dD.iii_eq_of_nf; iii_nf
    nf_coord <;> ring_nf <;> exact dvd_zero _

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_conj_sq_eq_one {y g : G} (h : y * y = 1) : g⁻¹ * y * g * (g⁻¹ * y * g) = 1 := by
  calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
    _ = 1 := by rw [h]; group

theorem iii_cls_ue (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1)
    {x : Fin 3 → ℤ}
    (h : dD.ofTorus (Torus.ofInt _ x) * (dD.u * e) *
      (dD.ofTorus (Torus.ofInt _ x) * (dD.u * e)) = 1) :
    (Even (x 0) → IsConj (dD.ofTorus (Torus.ofInt _ x) * (dD.u * e)) (dD.u * e)) ∧
      (¬ Even (x 0) →
        IsConj (dD.ofTorus (Torus.ofInt _ x) * (dD.u * e)) ((dD.c : G) * dD.u * e)) := by
  iii_rels
  have hx : x = ![x 0, x 1, x 2] := by funext i; fin_cases i <;> rfl
  rw [hx] at h ⊢
  iii_nf at h
  obtain ⟨-, h1, -⟩ := dD.iii_dvd_of_eq_one h
  simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h1
  obtain ⟨w, hw⟩ := h1
  obtain ⟨p0, h0 | h0⟩ := Int.even_or_odd' (x 0) <;> simp only [h0, Matrix.cons_val_zero]
  · refine ⟨fun _ => isConj_of_conj (dD.ofTorus (Torus.ofInt _ ![p0, x 1, 0])) ?_,
      fun hod => absurd ⟨p0, by ring⟩ hod⟩
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> ring_nf <;>
      first | exact dvd_zero _ | exact ⟨w, by linear_combination hw⟩ |
        exact ⟨-w, by linear_combination -hw⟩
  · refine ⟨fun hev => absurd hev (Int.not_even_iff_odd.mpr ⟨p0, by ring⟩), fun _ =>
      isConj_of_conj (dD.ofTorus (Torus.ofInt _ ![p0, x 1, 0])) ?_⟩
    rw [dD.iii_c_ofInt]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> ring_nf <;>
      first | exact dvd_zero _ | exact ⟨w, by linear_combination hw⟩ |
        exact ⟨-w, by linear_combination -hw⟩

theorem iii_t_conj_uvue (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1)
    (x : Fin 3 → ℤ) :
    dD.t⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * (dD.u * e))) * dD.t =
      dD.ofTorus (Torus.ofInt _ ![x 0 - 2 * x 2, 2 * x 0 - x 1 - 2 * x 2, 1 - x 2]) *
        (dD.u * e) := by
  iii_rels
  have hx : x = ![x 0, x 1, x 2] := by funext i; fin_cases i <;> rfl
  rw [hx]
  apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> ring_nf <;> exact dvd_zero _

theorem iii_cls_uvue (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1)
    {x : Fin 3 → ℤ}
    (h : dD.ofTorus (Torus.ofInt _ x) * (dD.uv * (dD.u * e)) *
      (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * (dD.u * e))) = 1) :
    (Even (x 0) →
        IsConj (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * (dD.u * e))) (dD.u * e)) ∧
      (¬ Even (x 0) → IsConj (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * (dD.u * e)))
        ((dD.c : G) * dD.u * e)) := by
  have hc := dD.iii_t_conj_uvue heuv het hue hce hae hbe he x
  have h' := iii_conj_sq_eq_one (g := dD.t) h
  rw [hc] at h'
  obtain ⟨hA, hB⟩ := dD.iii_cls_ue heuv het hue hce hae hbe he h'
  have hpar : Even (x 0 - 2 * x 2) ↔ Even (x 0) := by
    rw [Int.even_sub]; simp [parity_simps]
  simp only [Matrix.cons_val_zero] at hA hB
  refine ⟨fun hev => (isConj_of_conj dD.t hc).trans (hA (hpar.mpr hev)),
    fun hod => (isConj_of_conj dD.t hc).trans (hB (mt hpar.mp hod))⟩

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_rho_conj_t (x : Fin 3 → ℤ) :
    dD.ρ * (dD.ofTorus (Torus.ofInt _ x) * dD.t) * dD.ρ⁻¹ =
      dD.ofTorus (Torus.ofInt _
          ![x 0 - 2 * x 2 - 2 * (x 1 - x 2), -(x 1 - x 2), -x 2 - (x 1 - x 2)]) *
        dD.uv := by
  have ht : dD.ρ * dD.t * dD.ρ⁻¹ = dD.uv := by rw [← dD.conj_rho_uv]; group
  calc dD.ρ * (dD.ofTorus (Torus.ofInt _ x) * dD.t) * dD.ρ⁻¹ =
      (dD.ρ * dD.ofTorus (Torus.ofInt _ x) * dD.ρ⁻¹) * (dD.ρ * dD.t * dD.ρ⁻¹) := by group
    _ = _ := by
      rw [dD.rho_mul_ofTorus_mul_rho_inv, t100_φρ, t100_φρ, ht]
      congr 3

theorem iii_cls_t (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1)
    (hm : 1 ≤ m) {x : Fin 3 → ℤ}
    (h : dD.ofTorus (Torus.ofInt _ x) * dD.t * (dD.ofTorus (Torus.ofInt _ x) * dD.t) = 1) :
    (Even (x 0) → IsConj (dD.ofTorus (Torus.ofInt _ x) * dD.t) dD.uv) ∧
      (¬ Even (x 0) →
        IsConj (dD.ofTorus (Torus.ofInt _ x) * dD.t) ((dD.c : G) * dD.a * dD.uv)) := by
  have hc := dD.iii_rho_conj_t x
  have hconj : IsConj (dD.ofTorus (Torus.ofInt _ x) * dD.t) (dD.ofTorus (Torus.ofInt _
      ![x 0 - 2 * x 2 - 2 * (x 1 - x 2), -(x 1 - x 2), -x 2 - (x 1 - x 2)]) * dD.uv) :=
    isConj_of_conj dD.ρ⁻¹ (by rw [inv_inv]; exact hc)
  have h' := iii_conj_sq_eq_one (g := dD.ρ⁻¹) h
  rw [inv_inv, hc] at h'
  obtain ⟨hA, hB⟩ := dD.iii_cls_uv heuv het hue hce hae hbe he hm h'
  have hpar : Even (x 0 - 2 * x 2 - 2 * (x 1 - x 2)) ↔ Even (x 0) := by
    simp [Int.even_sub, parity_simps]
  simp only [Matrix.cons_val_zero] at hA hB
  refine ⟨fun hev => ?_, fun hod => ?_⟩
  · obtain ⟨q, -, hq⟩ := hA (hpar.mpr hev)
    exact hconj.trans (isConj_of_conj q hq)
  · obtain ⟨q, -, hq⟩ := hB (mt hpar.mp hod)
    exact hconj.trans (isConj_of_conj q hq)

theorem iii_u_conj_uvt (x : Fin 3 → ℤ) :
    dD.u⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * dD.t)) * dD.u =
      dD.ofTorus (Torus.ofInt _ ![x 0, x 2, x 1]) * dD.t := by
  have hx : x = ![x 0, x 1, x 2] := by funext i; fin_cases i <;> rfl
  rw [hx]
  apply dD.iii_eq_of_nf; s_nf

theorem iii_cls_uvt (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1)
    (hm : 1 ≤ m) {x : Fin 3 → ℤ}
    (h : dD.ofTorus (Torus.ofInt _ x) * (dD.uv * dD.t) *
      (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * dD.t)) = 1) :
    (Even (x 0) → IsConj (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * dD.t)) dD.uv) ∧
      (¬ Even (x 0) →
        IsConj (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * dD.t)) ((dD.c : G) * dD.a * dD.uv)) := by
  have hc := dD.iii_u_conj_uvt x
  have h' := iii_conj_sq_eq_one (g := dD.u) h
  rw [hc] at h'
  obtain ⟨hA, hB⟩ := dD.iii_cls_t heuv het hue hce hae hbe he hm h'
  simp only [Matrix.cons_val_zero] at hA hB
  exact ⟨fun hev => (isConj_of_conj dD.u hc).trans (hA hev),
    fun hod => (isConj_of_conj dD.u hc).trans (hB hod)⟩

theorem iii_t_conj_uvu (x : Fin 3 → ℤ) :
    dD.t⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * dD.u)) * dD.t =
      dD.ofTorus (Torus.ofInt _ ![x 0 - 2 * x 2, 2 * x 0 - x 1 - 2 * x 2, -x 2]) * dD.u := by
  have hx : x = ![x 0, x 1, x 2] := by funext i; fin_cases i <;> rfl
  rw [hx]
  apply dD.iii_eq_of_nf; s_nf

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_u_even (hm : 2 ≤ m) {x : Fin 3 → ℤ}
    (h : dD.ofTorus (Torus.ofInt _ x) * dD.u * (dD.ofTorus (Torus.ofInt _ x) * dD.u) = 1) :
    Even (x 0) := by
  s_nf at h
  obtain ⟨h0, -, -⟩ := dD.iii_dvd_of_eq_one h
  simp only [Pi.add_apply, Matrix.cons_val_zero] at h0
  have h4 : (4 : ℤ) ∣ x 0 + x 0 := (pow_dvd_pow 2 hm).trans h0
  exact even_iff_two_dvd.mpr (by omega)

theorem iii_D_even (hm : 2 ≤ m) {x : Fin 3 → ℤ}
    (h : dD.ofTorus (Torus.ofInt _ x) * dD.ofTorus (Torus.ofInt _ x) = 1) : Even (x 0) := by
  rw [dD.iii_ofInt_mul'] at h
  obtain ⟨h0, -, -⟩ := dD.iii_dvd_of_eq_one h
  simp only [Pi.add_apply] at h0
  have h4 : (4 : ℤ) ∣ x 0 + x 0 := (pow_dvd_pow 2 hm).trans h0
  exact even_iff_two_dvd.mpr (by omega)

theorem iii_cls_uvu (hm : 2 ≤ m) {x : Fin 3 → ℤ}
    (h : dD.ofTorus (Torus.ofInt _ x) * (dD.uv * dD.u) *
      (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * dD.u)) = 1) :
    Even (x 0) ∧ (IsConj (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * dD.u)) dD.u ∨
      IsConj (dD.ofTorus (Torus.ofInt _ x) * (dD.uv * dD.u))
        ((dD.c : G) ^ 2 ^ (m - 1) * dD.u)) := by
  have hc := dD.iii_t_conj_uvu x
  have h' := iii_conj_sq_eq_one (g := dD.t) h
  rw [hc] at h'
  have hev := dD.iii_u_even hm h'
  simp only [Matrix.cons_val_zero] at hev
  refine ⟨by simpa [Int.even_sub, parity_simps] using hev, ?_⟩
  obtain ⟨q, -, hq | hq⟩ := dD.iii_cls_u hm h'
  · exact Or.inl ((isConj_of_conj dD.t hc).trans (isConj_of_conj q hq))
  · exact Or.inr ((isConj_of_conj dD.t hc).trans (isConj_of_conj q hq))

theorem iii_uv_not (hm : 1 ≤ m) {X : Fin 3 → ℤ}
    (h : dD.ofTorus (Torus.ofInt _ X) * dD.uv = 1) : False := by
  have hnot := dD.d8_not_mem (t100_faithful hm) (i := true) (j := false) (l := false)
    (by decide) (Torus.ofInt _ X)
  rw [d8_tff, h] at hnot
  exact hnot (one_mem _)

theorem iii_classify (hm : 2 ≤ m) (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1)
    (x : Fin 3 → ℤ) (i j l k : Bool) {y : G}
    (hy : y = dD.ofTorus (Torus.ofInt _ x) * dD.d8 i j l * Stroth42Core.bpow e k)
    (h2 : y * y = 1) (h1 : y ≠ 1) :
    (k = false → Even (x 0) → IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨
        IsConj y ((dD.a : G) ^ 2 ^ m) ∨ IsConj y dD.uv ∨ IsConj y dD.u ∨
        IsConj y ((dD.c : G) ^ 2 ^ (m - 1) * dD.u)) ∧
      (k = false → ¬ Even (x 0) → IsConj y ((dD.c : G) * dD.a * dD.uv)) ∧
      (k = true → Even (x 0) → IsConj y e ∨ IsConj y (dD.u * e)) ∧
      (k = true → ¬ Even (x 0) → IsConj y ((dD.c : G) * e) ∨ IsConj y ((dD.c : G) * dD.u * e)) := by
  have hm1 : 1 ≤ m := by omega
  iii_rels
  subst hy
  cases i <;> cases j <;> cases l <;> cases k <;>
    simp only [d8_fff, d8_tff, d8_ftf, d8_fft, d8_ttf, d8_tft, d8_ftt, d8_ttt, Stroth42Core.bpow,
      if_true, if_false, Bool.false_eq_true, ↓reduceIte, mul_one, forall_const, true_implies,
      false_implies, true_and, and_true, reduceCtorEq, IsEmpty.forall_iff, Bool.true_eq_false]
      at h2 h1 ⊢
  · have hev := dD.iii_D_even hm h2
    exact ⟨fun _ => by
      rcases dD.iii_cls_D hm (dD.ofTorus_mem _) h2 h1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h), fun hod => absurd hev hod⟩
  · obtain ⟨hA, hB⟩ := dD.iii_cls_e heuv het hue hce hae hbe he x
    exact ⟨fun hev => by obtain ⟨q, -, hq⟩ := hA hev; exact Or.inl (isConj_of_conj q hq),
      fun hod => by obtain ⟨q, -, hq⟩ := hB hod; exact Or.inl (isConj_of_conj q hq)⟩
  · have hev := dD.iii_u_even hm h2
    refine ⟨fun _ => ?_, fun hod => absurd hev hod⟩
    obtain ⟨q, -, hq | hq⟩ := dD.iii_cls_u hm h2
    · exact Or.inr (Or.inr (Or.inr (Or.inl (isConj_of_conj q hq))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (isConj_of_conj q hq))))
  · have hw : dD.ofTorus (Torus.ofInt _ x) * dD.u * e =
        dD.ofTorus (Torus.ofInt _ x) * (dD.u * e) := mul_assoc _ _ _
    rw [hw] at h2 ⊢
    obtain ⟨hA, hB⟩ := dD.iii_cls_ue heuv het hue hce hae hbe he h2
    exact ⟨fun hev => Or.inr (hA hev), fun hod => Or.inr (hB hod)⟩
  · obtain ⟨hA, hB⟩ := dD.iii_cls_t heuv het hue hce hae hbe he hm1 h2
    exact ⟨fun hev => Or.inr (Or.inr (Or.inl (hA hev))), hB⟩
  · exfalso
    iii_nf at h2
    obtain ⟨-, h1', -⟩ := dD.iii_dvd_of_eq_one h2
    have h2' := (dvd_pow_self (2 : ℤ) (by omega : m + 1 ≠ 0)).trans h1'
    simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h2'
    omega
  · exfalso
    s_nf at h2
    exact dD.iii_uv_not hm1 h2
  · exfalso
    iii_nf at h2
    exact dD.iii_uv_not hm1 h2
  · obtain ⟨hA, hB⟩ := dD.iii_cls_uv heuv het hue hce hae hbe he hm1 h2
    refine ⟨fun hev => ?_, fun hod => ?_⟩
    · obtain ⟨q, -, hq⟩ := hA hev
      exact Or.inr (Or.inr (Or.inl (isConj_of_conj q hq)))
    · obtain ⟨q, -, hq⟩ := hB hod
      exact isConj_of_conj q hq
  · exfalso
    iii_nf at h2
    obtain ⟨-, h1', -⟩ := dD.iii_dvd_of_eq_one h2
    have h2' := (dvd_pow_self (2 : ℤ) (by omega : m + 1 ≠ 0)).trans h1'
    simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h2'
    omega
  · obtain ⟨hev, hc⟩ := dD.iii_cls_uvu hm h2
    refine ⟨fun _ => ?_, fun hod => absurd hev hod⟩
    rcases hc with hc | hc
    · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hc)))
  · have hw : dD.ofTorus (Torus.ofInt _ x) * (dD.uv * dD.u) * e =
        dD.ofTorus (Torus.ofInt _ x) * (dD.uv * (dD.u * e)) := by simp only [mul_assoc]
    rw [hw] at h2 ⊢
    obtain ⟨hA, hB⟩ := dD.iii_cls_uvue heuv het hue hce hae hbe he h2
    exact ⟨fun hev => Or.inr (hA hev), fun hod => Or.inr (hB hod)⟩
  · obtain ⟨hA, hB⟩ := dD.iii_cls_uvt heuv het hue hce hae hbe he hm1 h2
    exact ⟨fun hev => Or.inr (Or.inr (Or.inl (hA hev))), hB⟩
  · exfalso
    iii_nf at h2
    obtain ⟨-, -, h1'⟩ := dD.iii_dvd_of_eq_one h2
    have h2' := (dvd_pow_self (2 : ℤ) (by omega : m + 1 ≠ 0)).trans h1'
    simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h2'
    omega
  · exfalso
    s_nf at h2
    exact dD.iii_uv_not hm1 h2
  · exfalso
    iii_nf at h2
    exact dD.iii_uv_not hm1 h2

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_even_ofInt_iff (hm : 1 ≤ m) (x : Fin 3 → ℤ) :
    Even ((Torus.ofInt (StrothTypeIndex.t100 m).k x) 0) ↔ Even (x 0) := by
  have hk : 1 ≤ (StrothTypeIndex.t100 m).k 0 := hm
  rw [Torus.ofInt_apply, even_intCast_iff hk]

theorem iii_even_ofInt_add_one_iff (hm : 1 ≤ m) (x : Fin 3 → ℤ) :
    Even ((Torus.ofInt (StrothTypeIndex.t100 m).k x) 0 + 1) ↔ ¬ Even (x 0) := by
  have hk : 1 ≤ (StrothTypeIndex.t100 m).k 0 := hm
  have h : (Torus.ofInt (StrothTypeIndex.t100 m).k x) 0 + 1 =
      (((x 0 + 1 : ℤ)) : ZMod (2 ^ (StrothTypeIndex.t100 m).k 0)) := by
    rw [Torus.ofInt_apply]; push_cast; rfl
  rw [h, even_intCast_iff hk, Int.even_add_one]

theorem t100_iii_hC7 (hm : 2 ≤ m) (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1) :
    ∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e},
      y * y = 1 → y ≠ 1 → IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨
        IsConj y ((dD.a : G) ^ 2 ^ m) ∨ IsConj y dD.uv ∨ IsConj y dD.u ∨
        IsConj y ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ∨ IsConj y e ∨ IsConj y (dD.u * e) := by
  intro y hy h2 h1
  obtain ⟨v, i, j, l, k, hv, rfl⟩ :=
    (dD.iii_mem_S₁e_iff (by omega) heuv het hue hce hae hbe he).mp hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hev : Even (x 0) := (iii_even_ofInt_iff (m := m) (by omega) x).mp hv
  obtain ⟨hA, -, hC, -⟩ := dD.iii_classify hm heuv het hue hce hae hbe he x i j l k rfl h2 h1
  cases k
  · rcases hA rfl hev with h | h | h | h | h <;> simp only [h, true_or, or_true]
  · rcases hC rfl hev with h | h <;> simp only [h, true_or, or_true]

theorem t100_iii_hC10 (hm : 2 ≤ m) (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1) :
    ∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
      (dD.c : G) * e}, y * y = 1 → y ≠ 1 → IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨
        IsConj y ((dD.a : G) ^ 2 ^ m) ∨ IsConj y dD.uv ∨ IsConj y dD.u ∨
        IsConj y ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ∨ IsConj y ((dD.c : G) * e) ∨
        IsConj y ((dD.c : G) * dD.u * e) := by
  intro y hy h2 h1
  obtain ⟨v, i, j, l, k, hv, rfl⟩ :=
    (dD.iii_mem_S₂_iff (by omega) heuv het hue hce hae hbe he).mp hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  obtain ⟨hA, -, -, hD⟩ := dD.iii_classify hm heuv het hue hce hae hbe he x i j l k rfl h2 h1
  cases k
  · have hev : Even (x 0) := (iii_even_ofInt_iff (m := m) (by omega) x).mp (by simpa using hv)
    rcases hA rfl hev with h | h | h | h | h <;> simp only [h, true_or, or_true]
  · have hod : ¬ Even (x 0) :=
      (iii_even_ofInt_add_one_iff (m := m) (by omega) x).mp (by simpa using hv)
    rcases hD rfl hod with h | h <;> simp only [h, true_or, or_true]

theorem t100_iii_hC6 (hm : 2 ≤ m) (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} →
      y * y = 1 → IsConj y ((dD.c : G) * dD.a * dD.uv) ∨ IsConj y ((dD.c : G) * e) ∨
        IsConj y ((dD.c : G) * dD.u * e) := by
  intro y hy hy1 h2
  have h1 : y ≠ 1 := fun h => hy1 (h ▸ one_mem _)
  obtain ⟨v, i, j, l, k, rfl⟩ :=
    (dD.iiiAction heuv het hue hce hae hbe he).mem_sup_zpowers_iff.mp hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hod : ¬ Even (x 0) := fun hev =>
    hy1 ((dD.iii_mem_S₁e_iff (by omega) heuv het hue hce hae hbe he).mpr
      ⟨_, i, j, l, k, (iii_even_ofInt_iff (m := m) (by omega) x).mpr hev, rfl⟩)
  obtain ⟨-, hB, -, hD⟩ := dD.iii_classify hm heuv het hue hce hae hbe he x i j l k rfl h2 h1
  cases k
  · exact Or.inl (hB rfl hod)
  · rcases hD rfl hod with h | h <;> simp only [h, true_or, or_true]

theorem t100_iii_hC4 (hm : 2 ≤ m) (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1) :
    ∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
      e}, y * dD.uv ∈ D → y * y = 1 →
        ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
          q⁻¹ * y * q = dD.uv := by
  intro y hy hyD h2
  obtain ⟨v, hv⟩ := dD.exists_ofTorus hyD
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hyv : y = dD.ofTorus (Torus.ofInt _ x) * dD.uv := by
    rw [← hv, mul_assoc, dD.uv_sq, mul_one]
  have hS₁ := fun {g : G} (hg : g ∈ ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
    e} : Set G)) => Subgroup.subset_closure hg
  have hev : Even (x 0) := by
    by_contra hod
    obtain ⟨p, hp⟩ := Int.not_even_iff_odd.mp hod
    have hd : dD.ofTorus (Torus.ofInt _ x) ∈
        Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} := by
      rw [← hv]; exact mul_mem hy (hS₁ (by simp))
    have hd' : dD.ofTorus (Torus.ofInt _ ![2 * p, x 1, x 2]) ∈
        Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} :=
      (dD.iii_mem_S₁e_iff (by omega) heuv het hue hce hae hbe he).mpr
        ⟨_, false, false, false, false,
          (iii_even_ofInt_iff (m := m) (by omega) ![2 * p, x 1, x 2]).mpr
            (by show Even (2 * p); exact even_two_mul p),
          by simp only [d8_fff, Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one]⟩
    have hc : (dD.c : G) = dD.ofTorus (Torus.ofInt _ x) *
        (dD.ofTorus (Torus.ofInt _ ![2 * p, x 1, x 2]))⁻¹ := by
      rw [dD.iii_c_ofInt, dD.iii_ofInt_inv, dD.iii_ofInt_mul']
      refine dD.iii_ofInt_eq ?_ ?_ ?_ <;> simp [hp]
    have h3 := mul_mem hd (inv_mem hd')
    rw [← hc] at h3
    exact dD.iii_h2 hm heuv het hue hce hae hbe he h3
  rw [hyv] at h2 ⊢
  exact (dD.iii_cls_uv heuv het hue hce hae hbe he (by omega) h2).1 hev

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_zab : (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m = dD.ofTorus (om100 m ![0, 1, 1]) := by
  rw [dD.t100_a_pow, dD.t100_b_pow, ← dD.ofTorus_add, om100, om100, om100, ← Torus.ofInt_add]
  congr 2
  funext i
  fin_cases i <;> simp

theorem iii_comm_of_conj {g x : G} (h : g⁻¹ * x * g = x) : g * x = x * g := by
  calc g * x = g * (g⁻¹ * x * g) := by rw [h]
    _ = x * g := by group

theorem t100_iii_hC2c (hm : 1 ≤ m) (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) =
        (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m * y := by
  intro y hy
  rw [dD.iii_zab]
  have hle : D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e ≤
      Subgroup.centralizer {dD.ofTorus (om100 m ![0, 1, 1])} := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro d hd
      obtain ⟨v, rfl⟩ := dD.exists_ofTorus hd
      rw [Subgroup.mem_centralizer_singleton_iff, dD.ofTorus_comm]
    · rw [Subgroup.closure_le]
      rintro g (rfl | rfl | rfl) <;>
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] <;> refine iii_comm_of_conj ?_
      · rw [dD.iii_conj_uv_ofTorus, t100_φuv_om hm]
        exact congrArg dD.ofTorus ((om100_eq_iff hm _ _).mpr (by decide))
      · rw [dD.iii_conj_t_ofTorus, t100_φt_om hm]
        exact congrArg dD.ofTorus ((om100_eq_iff hm _ _).mpr (by decide))
      · rw [dD.iii_conj_u_ofTorus, t100_φu_om]
        exact congrArg dD.ofTorus ((om100_eq_iff hm _ _).mpr (by decide))
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      refine iii_comm_of_conj ?_
      rw [(dD.iiiAction heuv het hue hce hae hbe he).conj_ofTorus, iiiAction_φe_apply]
      congr 1
      rw [neg_eq_iff_add_eq_zero, om100_add_self hm]
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_om100_add (ε ε' : Fin 3 → ℤ) : om100 m ε + om100 m ε' = om100 m (ε + ε') := by
  rw [om100, om100, om100, ← Torus.ofInt_add]
  congr 1
  funext i
  simp only [Pi.add_apply]
  ring

theorem iii_hC2_D (hm : 1 ≤ m) {y : G} (hy : y ∈ D) (h2 : y * y = 1) (h1 : y ≠ 1)
    (hz : y ≠ (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) :
    ∃ q ∈ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G),
      q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) := by
  obtain ⟨ε, hε, rfl⟩ := dD.t100_eq_om_of_mul_self hm hy h2
  have hεv : ε = ![ε 0, ε 1, ε 2] := by funext i; fin_cases i <;> rfl
  have huv : dD.uv ∈ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hu : dD.u ∈ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) :=
    Subgroup.subset_closure (by simp)
  rw [dD.iii_zab] at hz ⊢
  rw [← dD.ofTorus_add, iii_om100_add]
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1' | h1' <;> rcases hε 2 with h2' | h2' <;>
    rw [hεv, h0, h1', h2'] at hz h1 ⊢
  · exact absurd (by rw [show (![0, 0, 0] : Fin 3 → ℤ) = 0 by decide, om100_zero,
      dD.ofTorus_zero]) h1
  · refine ⟨dD.u, hu, ?_⟩
    rw [dD.iii_conj_u_ofTorus, t100_φu_om]
    exact congrArg dD.ofTorus ((om100_eq_iff hm _ _).mpr (by decide))
  · refine ⟨dD.u, hu, ?_⟩
    rw [dD.iii_conj_u_ofTorus, t100_φu_om]
    exact congrArg dD.ofTorus ((om100_eq_iff hm _ _).mpr (by decide))
  · exact absurd (congrArg dD.ofTorus ((om100_eq_iff hm _ _).mpr (by decide))) hz
  all_goals
    refine ⟨dD.uv, huv, ?_⟩
    rw [dD.iii_conj_uv_ofTorus, t100_φuv_om hm]
    exact congrArg dD.ofTorus ((om100_eq_iff hm _ _).mpr (by decide))

theorem t100_iii_hC2 (hm : 2 ≤ m) (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * y = 1 → y ≠ 1 → y ≠ (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m →
        ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
          q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) := by
  intro y hy h2 h1 hz
  have hm1 : 1 ≤ m := by omega
  iii_rels
  obtain ⟨v, i, j, l, k, rfl⟩ :=
    (dD.iiiAction heuv het hue hce hae hbe he).mem_sup_zpowers_iff.mp hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hx : x = ![x 0, x 1, x 2] := by funext i; fin_cases i <;> rfl
  have hD := fun w => dD.iii_ofTorus_mem (e := e) w
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hcl := dD.iii_classify hm heuv het hue hce hae hbe he x i j l k rfl h2 h1
  rw [hx] at h2 h1 hz ⊢
  cases i <;> cases j <;> cases l <;> cases k <;>
    simp only [d8_fff, d8_tff, d8_ftf, d8_fft, d8_ttf, d8_tft, d8_ftt, d8_ttt, Stroth42Core.bpow,
      if_true, if_false, Bool.false_eq_true, ↓reduceIte, mul_one] at h2 h1 hz ⊢
  · obtain ⟨q, hq, hq'⟩ := dD.iii_hC2_D hm1 (dD.ofTorus_mem _) h2 h1 hz
    exact ⟨q, Subgroup.mem_sup_left (Subgroup.mem_sup_right hq), hq'⟩
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (n + 1), 2 ^ (n + 1)]), hD _, ?_⟩
    rw [dD.iii_a_npow, dD.iii_b_npow]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> push_cast <;> ring_nf <;> dvd_const
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 0, 2 ^ (n + 2)]), hD _, ?_⟩
    rw [dD.iii_a_npow, dD.iii_b_npow]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> push_cast <;> ring_nf <;> dvd_const
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (n + 2), 0]), hD _, ?_⟩
    rw [dD.iii_a_npow, dD.iii_b_npow]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> push_cast <;> ring_nf <;> dvd_const
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 0, 2 ^ (n + 1)]), hD _, ?_⟩
    rw [dD.iii_a_npow, dD.iii_b_npow]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> push_cast <;> ring_nf <;> dvd_const
  · exfalso
    iii_nf at h2
    obtain ⟨-, h1', -⟩ := dD.iii_dvd_of_eq_one h2
    have h2' := (dvd_pow_self (2 : ℤ) (by omega : n + 2 + 1 ≠ 0)).trans h1'
    simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h2'
    omega
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 0, 2 ^ (n + 2)]), hD _, ?_⟩
    rw [dD.iii_a_npow, dD.iii_b_npow]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> push_cast <;> ring_nf <;> dvd_const
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (n + 2), 0]), hD _, ?_⟩
    rw [dD.iii_a_npow, dD.iii_b_npow]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> push_cast <;> ring_nf <;> dvd_const
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (n + 1), 2 ^ (n + 1)]), hD _, ?_⟩
    rw [dD.iii_a_npow, dD.iii_b_npow]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> push_cast <;> ring_nf <;> dvd_const
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (n + 1), 0]), hD _, ?_⟩
    rw [dD.iii_a_npow, dD.iii_b_npow]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> push_cast <;> ring_nf <;> dvd_const
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (n + 2), 0]), hD _, ?_⟩
    rw [dD.iii_a_npow, dD.iii_b_npow]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> push_cast <;> ring_nf <;> dvd_const
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (n + 2), 0]), hD _, ?_⟩
    rw [dD.iii_a_npow, dD.iii_b_npow]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> push_cast <;> ring_nf <;> dvd_const
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (n + 1), 0]), hD _, ?_⟩
    rw [dD.iii_a_npow, dD.iii_b_npow]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> push_cast <;> ring_nf <;> dvd_const
  · exfalso
    iii_nf at h2
    obtain ⟨-, -, h1'⟩ := dD.iii_dvd_of_eq_one h2
    have h2' := (dvd_pow_self (2 : ℤ) (by omega : n + 2 + 1 ≠ 0)).trans h1'
    simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h2'
    omega
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (n + 2), 0]), hD _, ?_⟩
    rw [dD.iii_a_npow, dD.iii_b_npow]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> push_cast <;> ring_nf <;> dvd_const
  · refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (n + 2), 0]), hD _, ?_⟩
    rw [dD.iii_a_npow, dD.iii_b_npow]
    apply dD.iii_eq_of_nf; iii_nf; nf_coord <;> push_cast <;> ring_nf <;> dvd_const

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

include dD in
theorem iii_pow_exp {y : G} (hy : y ∈ D) : y ^ 2 ^ (m + 1) = 1 := by
  obtain ⟨v, rfl⟩ := dD.exists_ofTorus hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [dD.iii_ofInt_npow, ← dD.ofTorus_zero, ← Torus.ofInt_zero]
  refine dD.iii_ofInt_eq ?_ ?_ ?_ <;> simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul,
    zero_sub, dvd_neg] <;> push_cast
  · exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
  · exact Dvd.dvd.mul_right dvd_rfl _
  · exact Dvd.dvd.mul_right dvd_rfl _

include dD in
theorem iii_pow_four_of_conj {y₁ y₂ : G} (h₁ : y₁ ∈ D) (h₂ : y₂ ∈ Subgroup.normalizer (D : Set G))
    (hy₁ : y₁ * y₁ = 1) (hy₂ : y₂ * y₂ = 1) : (y₁ * y₂) ^ 4 = 1 ∧ (y₂ * y₁) ^ 4 = 1 := by
  have hy₂i : y₂⁻¹ = y₂ := inv_eq_of_mul_eq_one_right hy₂
  have hw : y₂ * y₁ * y₂ ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp h₂ y₁).mp h₁
    rwa [hy₂i] at this
  have hw2 : y₂ * y₁ * y₂ * (y₂ * y₁ * y₂) = 1 := by
    calc y₂ * y₁ * y₂ * (y₂ * y₁ * y₂) = y₂ * (y₁ * (y₂ * y₂) * y₁) * y₂ := by group
      _ = 1 := by rw [hy₂, mul_one, hy₁, mul_one, hy₂]
  have hc : y₁ * (y₂ * y₁ * y₂) = (y₂ * y₁ * y₂) * y₁ := by
    obtain ⟨v, hv⟩ := dD.exists_ofTorus h₁
    obtain ⟨w, hw'⟩ := dD.exists_ofTorus hw
    rw [hw', hv, dD.ofTorus_comm]
  constructor
  · calc (y₁ * y₂) ^ 4 = (y₁ * (y₂ * y₁ * y₂)) * (y₁ * (y₂ * y₁ * y₂)) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = (y₁ * y₁) * ((y₂ * y₁ * y₂) * (y₂ * y₁ * y₂)) := by
          rw [mul_assoc, ← mul_assoc (y₂ * y₁ * y₂) y₁, ← hc]; simp only [mul_assoc]
      _ = 1 := by rw [hy₁, hw2, mul_one]
  · calc (y₂ * y₁) ^ 4 = ((y₂ * y₁ * y₂) * y₁) * ((y₂ * y₁ * y₂) * y₁) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = ((y₂ * y₁ * y₂) * (y₂ * y₁ * y₂)) * (y₁ * y₁) := by
          rw [mul_assoc, ← mul_assoc y₁ (y₂ * y₁ * y₂), hc]; simp only [mul_assoc]
      _ = 1 := by rw [hy₁, hw2, one_mul]

theorem t100_iii_hC14 (hm : 1 ≤ m) :
    ∀ y₁ ∈ D ⊔ Subgroup.zpowers dD.u, ∀ y₂ ∈ D ⊔ Subgroup.zpowers dD.u,
      y₁ * y₁ = 1 → y₂ * y₂ = 1 → (y₁ * y₂) ^ 2 ^ (m + 1) = 1 := by
  intro y₁ hy₁ y₂ hy₂ h₁ h₂
  have hpow : ∀ z : G, z ^ 4 = 1 → z ^ 2 ^ (m + 1) = 1 := fun z hz => by
    obtain ⟨k, hk⟩ : (4 : ℕ) ∣ 2 ^ (m + 1) :=
      ⟨2 ^ (m - 1), by rw [show m + 1 = 2 + (m - 1) by omega, pow_add]; norm_num⟩
    rw [hk, pow_mul, hz, one_pow]
  obtain ⟨v₁, l₁, rfl⟩ := dD.iii_mem_Du_iff.mp hy₁
  obtain ⟨v₂, l₂, rfl⟩ := dD.iii_mem_Du_iff.mp hy₂
  have hnu : ∀ v, dD.ofTorus v * dD.u ∈ Subgroup.normalizer (D : Set G) := fun v =>
    mul_mem (Subgroup.le_normalizer (dD.ofTorus_mem v)) dD.u_mem
  cases l₁ <;> cases l₂ <;> simp only [d8_fff, d8_fft, mul_one] at h₁ h₂ ⊢
  · exact dD.iii_pow_exp (mul_mem (dD.ofTorus_mem v₁) (dD.ofTorus_mem v₂))
  · exact hpow _ (dD.iii_pow_four_of_conj (dD.ofTorus_mem v₁) (hnu v₂) h₁ h₂).1
  · exact hpow _ (dD.iii_pow_four_of_conj (dD.ofTorus_mem v₂) (hnu v₁) h₂ h₁).2
  · refine dD.iii_pow_exp ?_
    rw [mul_assoc, ← mul_assoc dD.u, dD.u_mul_ofTorus, mul_assoc, dD.u_sq, mul_one]
    exact mul_mem (dD.ofTorus_mem _) (dD.ofTorus_mem _)

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_om_cases (hm : 1 ≤ m) {y : G} (hy : y ∈ D) (h2 : y * y = 1)
    (hc : y ≠ dD.ofTorus (om100 m ![1, 0, 0])) :
    ∃ i : Fin 7, ![dD.ofTorus (om100 m ![0, 0, 0]), dD.ofTorus (om100 m ![0, 1, 0]),
      dD.ofTorus (om100 m ![0, 0, 1]), dD.ofTorus (om100 m ![0, 1, 1]),
      dD.ofTorus (om100 m ![1, 1, 0]), dD.ofTorus (om100 m ![1, 0, 1]),
      dD.ofTorus (om100 m ![1, 1, 1])] i = y := by
  obtain ⟨ε, hε, rfl⟩ := dD.t100_eq_om_of_mul_self hm hy h2
  have hεv : ε = ![ε 0, ε 1, ε 2] := by funext i; fin_cases i <;> rfl
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2' | h2' <;>
    rw [hεv, h0, h1, h2'] at hc ⊢
  exacts [⟨0, rfl⟩, ⟨2, rfl⟩, ⟨1, rfl⟩, ⟨3, rfl⟩, absurd rfl hc, ⟨5, rfl⟩, ⟨4, rfl⟩, ⟨6, rfl⟩]

theorem iii_om_cases_u (hm : 1 ≤ m) {y : G} (hy : y ∈ D) (h2 : y * y = 1)
    (hc : y ≠ dD.ofTorus (om100 m ![1, 0, 0])) (hu : y * dD.u = dD.u * y) :
    y = dD.ofTorus (om100 m ![0, 0, 0]) ∨ y = dD.ofTorus (om100 m ![0, 1, 1]) ∨
      y = dD.ofTorus (om100 m ![1, 1, 1]) := by
  obtain ⟨ε, hε, rfl⟩ := dD.t100_eq_om_of_mul_self hm hy h2
  have hεv : ε = ![ε 0, ε 1, ε 2] := by funext i; fin_cases i <;> rfl
  have hfix : dD.ofTorus ((StrothTypeIndex.t100 m).action.φu (om100 m ε)) =
      dD.ofTorus (om100 m ε) := by
    rw [← dD.iii_conj_u_ofTorus, dD.u_inv, ← hu, mul_assoc, dD.u_sq, mul_one]
  rw [t100_φu_om] at hfix
  have hfix' := (om100_eq_iff hm _ _).mp (dD.ofTorus_inj hfix)
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2' | h2' <;>
    rw [hεv, h0, h1, h2'] at hc hfix' ⊢
  · exact Or.inl rfl
  · exact absurd (hfix' 1) (by decide)
  · exact absurd (hfix' 1) (by decide)
  · exact Or.inr (Or.inl rfl)
  · exact absurd rfl hc
  · exact absurd (hfix' 1) (by decide)
  · exact absurd (hfix' 1) (by decide)
  · exact Or.inr (Or.inr rfl)

theorem t100_iii_hC13 (hm : 1 ≤ m) :
    ∀ E : Subgroup G, E ≤ D ⊔ Subgroup.zpowers dD.u → (∀ y ∈ E, y * y = 1) →
      Nat.card E = 8 → (dD.c : G) ^ 2 ^ (m - 1) ∈ E := by
  intro E hE hinv hcard
  by_contra hc1
  rw [dD.t100_c_pow] at hc1
  have hne : ∀ y ∈ E, y ≠ dD.ofTorus (om100 m ![1, 0, 0]) := fun y hy h => hc1 (h ▸ hy)
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h1 := inv_eq_of_mul_eq_one_right (hinv a ha)
    have h2 := inv_eq_of_mul_eq_one_right (hinv b hb)
    have h3 := inv_eq_of_mul_eq_one_right (hinv _ (mul_mem ha hb))
    calc a * b = (a * b)⁻¹ := h3.symm
      _ = b * a := by rw [mul_inv_rev, h1, h2]
  by_cases hED : ∀ y ∈ E, y ∈ D
  · have h7 := Stroth42Core.natCard_le_of_subset_range (E := E) _ fun y hy =>
      dD.iii_om_cases hm (hED y hy) (hinv y hy) (hne y hy)
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h7
    omega
  · push Not at hED
    obtain ⟨y₀, hy₀E, hy₀D⟩ := hED
    obtain ⟨v₀, l₀, rfl⟩ := dD.iii_mem_Du_iff.mp (hE hy₀E)
    cases l₀
    · exact hy₀D (by rw [d8_fff, mul_one]; exact dD.ofTorus_mem v₀)
    rw [d8_fft] at hy₀E hy₀D
    have hDu : ∀ y ∈ E, y ∈ D → y = dD.ofTorus (om100 m ![0, 0, 0]) ∨
        y = dD.ofTorus (om100 m ![0, 1, 1]) ∨ y = dD.ofTorus (om100 m ![1, 1, 1]) := by
      intro y hyE hyD
      refine dD.iii_om_cases_u hm hyD (hinv y hyE) (hne y hyE) ?_
      have h := hcomm y hyE _ hy₀E
      obtain ⟨w, rfl⟩ := dD.exists_ofTorus hyD
      rw [← mul_assoc, dD.ofTorus_comm, mul_assoc, mul_assoc] at h
      exact mul_left_cancel h
    have h6 := Stroth42Core.natCard_le_of_subset_range (E := E)
      ![dD.ofTorus (om100 m ![0, 0, 0]), dD.ofTorus (om100 m ![0, 1, 1]),
        dD.ofTorus (om100 m ![1, 1, 1]), dD.ofTorus v₀ * dD.u,
        dD.ofTorus (om100 m ![0, 1, 1]) * (dD.ofTorus v₀ * dD.u),
        dD.ofTorus (om100 m ![1, 1, 1]) * (dD.ofTorus v₀ * dD.u)] fun y hy => by
      obtain ⟨v, l, rfl⟩ := dD.iii_mem_Du_iff.mp (hE hy)
      cases l
      · rw [d8_fff, mul_one] at hy ⊢
        rcases hDu _ hy (dD.ofTorus_mem v) with h | h | h
        exacts [⟨0, h.symm⟩, ⟨1, h.symm⟩, ⟨2, h.symm⟩]
      · rw [d8_fft] at hy ⊢
        have hq : dD.ofTorus v * dD.u * (dD.ofTorus v₀ * dD.u)⁻¹ ∈ D := by
          rw [mul_inv_rev, dD.u_inv, mul_assoc, ← mul_assoc dD.u, dD.u_sq, one_mul]
          exact mul_mem (dD.ofTorus_mem v) (inv_mem (dD.ofTorus_mem v₀))
        have hqE := mul_mem hy (inv_mem hy₀E)
        rcases hDu _ hqE hq with h | h | h
        · refine ⟨3, ?_⟩
          show dD.ofTorus v₀ * dD.u = dD.ofTorus v * dD.u
          rw [show dD.ofTorus (om100 m ![0, 0, 0]) = 1 by
            rw [show (![0, 0, 0] : Fin 3 → ℤ) = 0 by decide, om100_zero, dD.ofTorus_zero]] at h
          exact (mul_inv_eq_one.mp h).symm
        · refine ⟨4, ?_⟩
          show dD.ofTorus (om100 m ![0, 1, 1]) * (dD.ofTorus v₀ * dD.u) = dD.ofTorus v * dD.u
          rw [← h]; group
        · refine ⟨5, ?_⟩
          show dD.ofTorus (om100 m ![1, 1, 1]) * (dD.ofTorus v₀ * dD.u) = dD.ofTorus v * dD.u
          rw [← h]; group
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h6
    omega

end StrothWeakTypeData

namespace Stroth43Core

open Stroth42Core

variable {G : Type*} [Group G]

theorem closure_three_inv {x y z : G} (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1)
    (hxy : x * y = y * x) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (hind : ∀ a b c : Bool, bpow x a * bpow y b * bpow z c = 1 →
      a = false ∧ b = false ∧ c = false) :
    (∀ g ∈ Subgroup.closure ({x, y, z} : Set G), g * g = 1) ∧
      Nat.card (Subgroup.closure ({x, y, z} : Set G)) = 8 := by
  have h1 : (1 : G) * 1 = 1 := mul_one 1
  have hmul := prod4_mul_prod4 hx hy hz h1 hxy hxz (by simp) hyz (by simp) (by simp)
  let f : Bool × Bool × Bool → G := fun w => prod4 x y z 1 ((w.1, w.2.1), (w.2.2, false))
  have hf : ∀ w w', f w * f w' = f (xor w.1 w'.1, xor w.2.1 w'.2.1, xor w.2.2 w'.2.2) := by
    intro w w'
    simp only [f, hmul, xor4, Bool.xor_false]
  have hsq : ∀ w, f w * f w = 1 := fun w => by
    rw [hf]; simp only [Bool.xor_self]; exact prod4_zero x y z 1
  let E : Subgroup G :=
    { carrier := Set.range f
      mul_mem' := by
        rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
        exact ⟨_, (hf w w').symm⟩
      one_mem' := ⟨(false, false, false), prod4_zero x y z 1⟩
      inv_mem' := by
        rintro _ ⟨w, rfl⟩
        exact ⟨w, (inv_eq_of_mul_eq_one_right (hsq w)).symm⟩ }
  have hfE : ∀ w, f w ∈ Subgroup.closure ({x, y, z} : Set G) := by
    rintro ⟨a, b, c⟩
    have hxS : x ∈ Subgroup.closure ({x, y, z} : Set G) := Subgroup.subset_closure (by simp)
    have hyS : y ∈ Subgroup.closure ({x, y, z} : Set G) := Subgroup.subset_closure (by simp)
    have hzS : z ∈ Subgroup.closure ({x, y, z} : Set G) := Subgroup.subset_closure (by simp)
    cases a <;> cases b <;> cases c <;> simp [f, prod4, bpow, mul_mem, hxS, hyS, hzS]
  have hEq : Subgroup.closure ({x, y, z} : Set G) = E := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro g (rfl | rfl | rfl)
      · exact ⟨(true, false, false), by simp [f, prod4, bpow]⟩
      · exact ⟨(false, true, false), by simp [f, prod4, bpow]⟩
      · exact ⟨(false, false, true), by simp [f, prod4, bpow]⟩
    · rintro _ ⟨w, rfl⟩
      exact hfE w
  have hf0 : ∀ w, f w = bpow x w.1 * bpow y w.2.1 * bpow z w.2.2 := by
    rintro ⟨a, b, c⟩
    simp [f, prod4, bpow, mul_assoc]
  have hinj : Function.Injective f := by
    intro w w' h
    have h0 : f (xor w.1 w'.1, xor w.2.1 w'.2.1, xor w.2.2 w'.2.2) = 1 := by
      rw [← hf, h, hsq]
    rw [hf0] at h0
    obtain ⟨ha, hb, hc⟩ := hind _ _ _ h0
    obtain ⟨a, b, c⟩ := w
    obtain ⟨a', b', c'⟩ := w'
    revert ha hb hc
    cases a <;> cases a' <;> cases b <;> cases b' <;> cases c <;> cases c' <;> decide
  refine ⟨fun g hg => ?_, ?_⟩
  · rw [hEq] at hg
    obtain ⟨w, rfl⟩ := hg
    exact hsq w
  · rw [hEq]
    change Nat.card (Set.range f) = 8
    rw [Nat.card_range_of_injective hinj]
    simp

end Stroth43Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_t_not_mem (hm : 1 ≤ m) : dD.t ∉ D := by
  have h := dD.d8_not_mem (t100_faithful hm) (i := false) (j := true) (l := false) (by decide) 0
  rwa [d8_ftf, dD.ofTorus_zero, one_mul] at h

theorem t100_iii_hF (hm : 2 ≤ m) :
    Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.t} ≤
        Subgroup.centralizer {(dD.c : G) * dD.a * dD.uv} ∧
      (∀ y ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.t}, y * y = 1) ∧
      Nat.card (Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.t}) = 8 := by
  have hm1 : 1 ≤ m := by omega
  have hza : (dD.a : G) ^ 2 ^ m * (dD.a : G) ^ 2 ^ m = 1 := by
    rw [dD.t100_a_pow, ← dD.ofTorus_add, om100_add_self hm1, dD.ofTorus_zero]
  have hzb : (dD.b : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m = 1 := by
    rw [dD.t100_b_pow, ← dD.ofTorus_add, om100_add_self hm1, dD.ofTorus_zero]
  have hab : (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m = (dD.b : G) ^ 2 ^ m * (dD.a : G) ^ 2 ^ m := by
    rw [dD.t100_a_pow, dD.t100_b_pow, dD.ofTorus_comm]
  have hat : (dD.a : G) ^ 2 ^ m * dD.t = dD.t * (dD.a : G) ^ 2 ^ m := by
    refine (iii_comm_of_conj ?_).symm
    rw [dD.t100_a_pow, dD.iii_conj_t_ofTorus, t100_φt_om hm1]
    exact congrArg dD.ofTorus ((om100_eq_iff hm1 _ _).mpr (by decide))
  have hbt : (dD.b : G) ^ 2 ^ m * dD.t = dD.t * (dD.b : G) ^ 2 ^ m := by
    refine (iii_comm_of_conj ?_).symm
    rw [dD.t100_b_pow, dD.iii_conj_t_ofTorus, t100_φt_om hm1]
    exact congrArg dD.ofTorus ((om100_eq_iff hm1 _ _).mpr (by decide))
  have hind : ∀ a b c : Bool, Stroth42Core.bpow ((dD.a : G) ^ 2 ^ m) a *
      Stroth42Core.bpow ((dD.b : G) ^ 2 ^ m) b * Stroth42Core.bpow dD.t c = 1 →
        a = false ∧ b = false ∧ c = false := by
    intro a b c h
    have hD : Stroth42Core.bpow ((dD.a : G) ^ 2 ^ m) a * Stroth42Core.bpow ((dD.b : G) ^ 2 ^ m) b ∈
        D := by
      cases a <;> cases b <;> simp [Stroth42Core.bpow, dD.t100_a_pow, dD.t100_b_pow,
        mul_mem, dD.ofTorus_mem]
    cases c
    · refine ⟨?_, ?_, rfl⟩ <;>
      · simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at h
        rw [dD.t100_a_pow, dD.t100_b_pow] at h
        have key : ∀ a b : Bool, (if a = true then dD.ofTorus (om100 m ![0, 1, 0]) else 1) *
            (if b = true then dD.ofTorus (om100 m ![0, 0, 1]) else 1) = 1 →
              a = false ∧ b = false := by
          intro a b h'
          cases a <;> cases b <;> simp only [if_true, Bool.false_eq_true, ↓reduceIte, mul_one,
            one_mul, and_self, and_true, true_and, reduceCtorEq] at h' ⊢
          · rw [← dD.ofTorus_zero, ← om100_zero] at h'
            exact absurd ((om100_eq_iff hm1 _ _).mp (dD.ofTorus_inj h') 2) (by decide)
          · rw [← dD.ofTorus_zero, ← om100_zero] at h'
            exact absurd ((om100_eq_iff hm1 _ _).mp (dD.ofTorus_inj h') 1) (by decide)
          · rw [← dD.ofTorus_add, iii_om100_add, ← dD.ofTorus_zero, ← om100_zero] at h'
            exact absurd ((om100_eq_iff hm1 _ _).mp (dD.ofTorus_inj h') 1) (by decide)
        first | exact (key a b h).1 | exact (key a b h).2
    · simp only [Stroth42Core.bpow, if_true] at h
      have ht : dD.t = (Stroth42Core.bpow ((dD.a : G) ^ 2 ^ m) a *
          Stroth42Core.bpow ((dD.b : G) ^ 2 ^ m) b)⁻¹ := by
        rw [eq_comm, inv_eq_iff_mul_eq_one]
        simpa only [Stroth42Core.bpow] using h
      exact absurd (ht ▸ inv_mem hD) (dD.iii_t_not_mem hm1)
  obtain ⟨hinv, hcard⟩ := Stroth43Core.closure_three_inv hza hzb dD.t_sq hab hat hbt hind
  refine ⟨?_, hinv, hcard⟩
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] <;>
    apply dD.iii_eq_of_nf <;>
    rw [dD.iii_c_ofInt, dD.iii_a_ofInt] <;>
    (try rw [dD.iii_b_ofInt]) <;> s_nf <;> nf_coord <;> (try push_cast) <;> ring_nf <;> dvd_const

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem iii_hM_sq (n : ℕ) (dD : StrothWeakTypeData D (.t100 (n + 2))) :
    (dD.c : G) * dD.a * dD.uv * ((dD.c : G) ^ 2 ^ (n + 2 - 1) * dD.u) *
        ((dD.c : G) * dD.a * dD.uv * ((dD.c : G) ^ 2 ^ (n + 2 - 1) * dD.u)) =
      dD.ofTorus (Torus.ofInt _ ![-2 ^ (n + 2), 1 - 2 ^ (n + 2), -1 - 2 ^ (n + 2)]) := by
  rw [dD.iii_c_npow, dD.iii_c_ofInt, dD.iii_a_ofInt]
  apply dD.iii_eq_of_nf
  s_nf
  nf_coord <;> (try push_cast) <;> ring_nf <;> dvd_const

theorem t100_iii_hM (hm : 2 ≤ m) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1) :
    (dD.c : G) ^ 2 ^ (m - 1) * dD.u * (dD.u * e) =
        dD.u * e * ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ∧
      ((dD.c : G) * dD.a * dD.uv * ((dD.c : G) ^ 2 ^ (m - 1) * dD.u)) ^ 2 ^ (m + 1) ≠ 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have r1 := dD.iii_e_mul_ofInt he hce hae hbe
  have r1' := dD.iii_e_mul_ofInt' he hce hae hbe
  have r4 := dD.iii_e_mul_u he hue
  have r4' := dD.iii_e_mul_u' he hue
  refine ⟨?_, ?_⟩
  · rw [dD.iii_c_npow]
    apply dD.iii_eq_of_nf
    simp only [mul_assoc, dD.iii_ofInt_mul, dD.iii_ofInt_mul', dD.iii_u_mul_ofInt,
      dD.iii_u_mul_ofInt', dD.u_mul_u, dD.u_sq, one_mul, mul_one, r1, r1', r4, r4']
    nf_coord <;> (try push_cast) <;> ring_nf <;> dvd_const
  · rw [Stroth42Core.pow_two_pow_eq_mul_self _ (by omega), Nat.add_sub_cancel, iii_hM_sq n dD,
      dD.iii_ofInt_npow, Ne, ofTorus_eq_one_iff, t100_ofInt_eq_zero_iff]
    rintro ⟨-, h1, -⟩
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.head_cons] at h1
    push_cast at h1
    rw [show (2 : ℤ) ^ (n + 2 + 1) = 2 ^ (n + 2) * 2 by ring,
      mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)] at h1
    have h2 : (2 : ℤ) ∣ 2 ^ (n + 2) := dvd_pow_self 2 (by omega)
    omega

end StrothWeakTypeData

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m)) {e : G}

theorem t100_iii_hC15 (hm : 2 ≤ m) (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (he : e * e = 1) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y ∈ D ⊔ Subgroup.zpowers dD.u ∨ y * e ∈ D ⊔ Subgroup.zpowers dD.u := by
  intro y hy hcomm
  obtain ⟨v, i, j, l, k, rfl⟩ :=
    (dD.iiiAction heuv het hue hce hae hbe he).mem_sup_zpowers_iff.mp hy
  have hφ : (dD.iiiAction heuv het hue hce hae hbe he).φe (om100 m ![1, 0, 0]) =
      om100 m ![1, 0, 0] := by
    rw [iiiAction_φe]
    exact torusDiag_om100_of_odd (by omega) (by decide) (by decide) (by decide) _
  obtain ⟨rfl, rfl⟩ := EAction.t100_comm_c₁ (hE := dD.iiiAction heuv het hue hce hae hbe he)
    (hm := by omega) (hφ := hφ) (h := hcomm)
  cases l <;> cases k <;> simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one]
  · exact Or.inl (dD.iii_mem_Du_iff.mpr ⟨v, false, rfl⟩)
  · exact Or.inr (dD.iii_mem_Du_iff.mpr ⟨v, false, by rw [mul_assoc, he, mul_one]⟩)
  · exact Or.inl (dD.iii_mem_Du_iff.mpr ⟨v, true, rfl⟩)
  · exact Or.inr (dD.iii_mem_Du_iff.mpr ⟨v, true, by rw [mul_assoc, he, mul_one]⟩)

end StrothWeakTypeData

end CFSG.CGT.Stroth77
