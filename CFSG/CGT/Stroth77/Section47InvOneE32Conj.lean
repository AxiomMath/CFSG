module

public import CFSG.CGT.Stroth77.Section47InvOneAction

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core Stroth34T200

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))
  {e : G}

theorem t200_u_conj_uvte (he : dD.u * e = e * dD.u) (v : Torus (StrothTypeIndex.t200 m).k) :
    dD.u⁻¹ * (dD.ofTorus v * dD.d8 true true false * e) * dD.u =
      dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) * dD.d8 false true false * e := by
  have hte : dD.u⁻¹ * e * dD.u = e := by
    rw [dD.u_inv]
    calc dD.u * e * dD.u = e * dD.u * dD.u := by rw [he]
      _ = e := by rw [mul_assoc, dD.u_sq, mul_one]
  have hut : dD.u⁻¹ * (dD.uv * dD.t) * dD.u = dD.t := by
    rw [dD.u_inv]
    calc dD.u * (dD.uv * dD.t) * dD.u
        = dD.uv * (dD.u * dD.t) * dD.u := by rw [dD.u_mul_uv]
      _ = dD.uv * (dD.uv * dD.t * dD.u) * dD.u := by rw [dD.u_mul_t_eq]
      _ = dD.t := by
          calc dD.uv * (dD.uv * dD.t * dD.u) * dD.u
              = (dD.uv * dD.uv) * dD.t * (dD.u * dD.u) := by group
            _ = dD.t := by rw [dD.uv_sq, dD.u_sq]; group
  rw [dD.d8_ttf, dD.d8_ftf]
  calc dD.u⁻¹ * (dD.ofTorus v * (dD.uv * dD.t) * e) * dD.u
      = (dD.u⁻¹ * dD.ofTorus v * dD.u) * (dD.u⁻¹ * (dD.uv * dD.t) * dD.u) *
          (dD.u⁻¹ * e * dD.u) := by group
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) * dD.t * e := by
          rw [dD.conj_ofTorus dD.u_mem dD.u_conj v, hut, hte]

theorem t200inv1_conj_ofTorus_Dte {j p : ℕ} (hrel : Rel34inv dD e j 1 p)
    (w v : Torus (StrothTypeIndex.t200 m).k) :
    (dD.ofTorus w)⁻¹ * (dD.ofTorus v * dD.d8 false true false * e) * dD.ofTorus w =
      dD.ofTorus (v - w + (StrothTypeIndex.t200 m).action.φt
        ((dD.t200inv1EAction hrel).φe w)) * dD.d8 false true false * e := by
  let hE := dD.t200inv1EAction hrel
  rw [dD.d8_ftf]
  calc (dD.ofTorus w)⁻¹ * (dD.ofTorus v * dD.t * e) * dD.ofTorus w
      = dD.ofTorus (-w) * dD.ofTorus v * (dD.t * (e * dD.ofTorus w)) := by
        rw [← dD.ofTorus_neg]
        group
    _ = dD.ofTorus (-w) * dD.ofTorus v * (dD.t * (dD.ofTorus (hE.φe w) * e)) := by
        rw [hE.e_mul_ofTorus]
    _ = dD.ofTorus (-w) * dD.ofTorus v *
          (dD.ofTorus ((StrothTypeIndex.t200 m).action.φt (hE.φe w)) * (dD.t * e)) := by
        rw [dD.t_mul_ofTorus_mul]
    _ = dD.ofTorus (-w) * dD.ofTorus v * dD.ofTorus ((StrothTypeIndex.t200 m).action.φt
          (hE.φe w)) * (dD.t * e) := by group
    _ = dD.ofTorus (-w + v + (StrothTypeIndex.t200 m).action.φt (hE.φe w)) * (dD.t * e) := by
        rw [← dD.ofTorus_add, ← dD.ofTorus_add]
    _ = dD.ofTorus (v - w + (StrothTypeIndex.t200 m).action.φt (hE.φe w)) * dD.t * e := by
        rw [show -w + v + (StrothTypeIndex.t200 m).action.φt (hE.φe w) =
          v - w + (StrothTypeIndex.t200 m).action.φt (hE.φe w) by abel]
        group

theorem t200inv1_Dte_mul_self {j p : ℕ} (hrel : Rel34inv dD e j 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) :
    (dD.ofTorus v * dD.t * e) * (dD.ofTorus v * dD.t * e) =
      dD.ofTorus (v + (StrothTypeIndex.t200 m).action.φt ((dD.t200inv1EAction hrel).φe v) +
        (StrothTypeIndex.t200 m).action.φt (dD.t200inv1EAction hrel).wt) := by
  rw [← dD.d8_ftf, (dD.t200inv1EAction hrel).nfe_e_mul_self, Bool.false_and, dD.d8_fff,
    mul_one, StrothWeakTypeData.EAction.sqE, StrothWeakTypeData.EAction.twist,
    show (dD.t200inv1EAction hrel).ve = 0 from rfl]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, map_zero, map_add, zero_add, sub_zero, add_zero, add_assoc]

theorem t200inv1_sq_Dte_j0 (hrel : Rel34inv dD e 0 1 2) (x : Fin 3 → ℤ) :
    (dD.ofTorus (Torus.ofInt _ x) * dD.t * e) *
        (dD.ofTorus (Torus.ofInt _ x) * dD.t * e) =
      dD.ofTorus (Torus.ofInt _ ![x 2, -4 * x 0 + 2 * x 1 + 2 * x 2 + 2, 2 * x 2]) := by
  rw [t200inv1_Dte_mul_self dD hrel]
  congr 1
  rw [StrothWeakTypeData.t200inv1_φe dD hrel, t200_φt_vec,
    show (dD.t200inv1EAction hrel).wt = Torus.ofInt _ ![0, -2, 0] from rfl, t200_φt_vec]
  rw [← Torus.ofInt_add, ← Torus.ofInt_add]
  congr 1
  funext i
  fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail] <;> ring

theorem t200inv1_sq_Dte_j2M (hrel : Rel34inv dD e (2 ^ (m + 1)) 1 2) (x : Fin 3 → ℤ) :
    (dD.ofTorus (Torus.ofInt _ x) * dD.t * e) *
        (dD.ofTorus (Torus.ofInt _ x) * dD.t * e) =
      dD.ofTorus (Torus.ofInt _ ![(1 - (2 : ℤ) ^ (m + 1)) * x 2,
        (2 - (2 : ℤ) ^ (m + 1)) * x 1 - 4 * x 0 + 2 * (1 - (2 : ℤ) ^ (m + 1)) * x 2 + 2,
        (2 - (2 : ℤ) ^ (m + 1)) * x 2]) := by
  rw [t200inv1_Dte_mul_self dD hrel]
  congr 1
  rw [StrothWeakTypeData.t200inv1_φe dD hrel, t200_φt_vec,
    show (dD.t200inv1EAction hrel).wt = Torus.ofInt _ ![0, -2, 0] from rfl, t200_φt_vec]
  rw [← Torus.ofInt_add, ← Torus.ofInt_add]
  congr 1
  funext i
  fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail] <;> ring

theorem t200inv1_prod_Dte_e (k l : ℤ) :
    dD.ofTorus (Torus.ofInt _ ![0, -1 + (2 : ℤ) ^ (m + 1) * k, (2 : ℤ) ^ (m + 1) * l]) *
        dD.d8 false true false * e =
      ((dD.a : G) ^ 2 ^ (m + 1)) ^ k * ((dD.b : G) ^ 2 ^ (m + 1)) ^ l *
        ((dD.a : G)⁻¹ * dD.d8 false true false) * e := by
  have ha_inv_t : (dD.a : G)⁻¹ * dD.d8 false true false =
      dD.ofTorus (Torus.ofInt (StrothTypeIndex.t200 m).k ![0, -1, 0]) *
        dD.d8 false true false := by
    rw [dD.d8_ftf, dD.a_eq, ← dD.ofTorus_neg, a_eq_ofInt, t200_neg_vec]
    congr 1
  have ha₁ : dD.ofTorus (Torus.ofInt (StrothTypeIndex.t200 m).k ![0, (2 : ℤ) ^ (m + 1), 0]) =
      (dD.a : G) ^ 2 ^ (m + 1) := by
    rw [dD.t200_a_pow, om200_apply]
    congr 1
    funext i
    fin_cases i <;> simp
  have hb₁ : dD.ofTorus (Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 0, (2 : ℤ) ^ (m + 1)]) =
      (dD.b : G) ^ 2 ^ (m + 1) := by
    rw [dD.t200_b_pow, om200_apply]
    congr 1
    funext i
    fin_cases i <;> simp
  have hvec : k • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, (2 : ℤ) ^ (m + 1), 0] +
      l • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 0, (2 : ℤ) ^ (m + 1)] +
      Torus.ofInt (StrothTypeIndex.t200 m).k ![0, -1, 0] =
      Torus.ofInt (StrothTypeIndex.t200 m).k
        ![0, -1 + (2 : ℤ) ^ (m + 1) * k, (2 : ℤ) ^ (m + 1) * l] := by
    rw [t200_zsmul_vec, t200_zsmul_vec, t200_add_vec, t200_add_vec]
    congr 1
    funext i
    fin_cases i <;> simp <;> ring
  have h : ((dD.a : G) ^ 2 ^ (m + 1)) ^ k * ((dD.b : G) ^ 2 ^ (m + 1)) ^ l *
      ((dD.a : G)⁻¹ * dD.d8 false true false) * e =
      dD.ofTorus (Torus.ofInt _ ![0, -1 + (2 : ℤ) ^ (m + 1) * k, (2 : ℤ) ^ (m + 1) * l]) *
        dD.d8 false true false * e := by
    calc ((dD.a : G) ^ 2 ^ (m + 1)) ^ k * ((dD.b : G) ^ 2 ^ (m + 1)) ^ l *
          ((dD.a : G)⁻¹ * dD.d8 false true false) * e
        = (dD.ofTorus (Torus.ofInt _ ![0, (2 : ℤ) ^ (m + 1), 0])) ^ k *
          (dD.ofTorus (Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)])) ^ l *
          (dD.ofTorus (Torus.ofInt _ ![0, -1, 0]) * dD.d8 false true false) * e := by
          rw [← ha₁, ← hb₁, ha_inv_t]
      _ = dD.ofTorus (k • Torus.ofInt _ ![0, (2 : ℤ) ^ (m + 1), 0]) *
          dD.ofTorus (l • Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)]) *
          (dD.ofTorus (Torus.ofInt _ ![0, -1, 0]) * dD.d8 false true false) * e := by
          rw [← dD.ofTorus_zsmul, ← dD.ofTorus_zsmul]
      _ = dD.ofTorus (k • Torus.ofInt _ ![0, (2 : ℤ) ^ (m + 1), 0]) *
          dD.ofTorus (l • Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)]) *
          dD.ofTorus (Torus.ofInt _ ![0, -1, 0]) * dD.d8 false true false * e := by
          group
      _ = dD.ofTorus (k • Torus.ofInt _ ![0, (2 : ℤ) ^ (m + 1), 0] +
            l • Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)] + Torus.ofInt _ ![0, -1, 0]) *
          dD.d8 false true false * e := by
          rw [← dD.ofTorus_add, ← dD.ofTorus_add]
      _ = dD.ofTorus (Torus.ofInt _ ![0, -1 + (2 : ℤ) ^ (m + 1) * k, (2 : ℤ) ^ (m + 1) * l]) *
          dD.d8 false true false * e := by
          rw [hvec]
  exact h.symm

theorem t200inv1_prod_Dte_c₁e (hm : 1 ≤ m) (k l : ℤ) :
    dD.ofTorus (Torus.ofInt _ ![(2 : ℤ) ^ (m - 1), -1 + (2 : ℤ) ^ (m + 1) * k,
        (2 : ℤ) ^ (m + 1) * l]) * dD.d8 false true false * e =
      ((dD.a : G) ^ 2 ^ (m + 1)) ^ (k - 1) * ((dD.b : G) ^ 2 ^ (m + 1)) ^ l *
        ((dD.a : G)⁻¹ * dD.d8 false true false) *
        ((dD.c : G) ^ 2 ^ (m - 1) * e) := by
  have hpow : 4 * (2 : ℤ) ^ (m - 1) = (2 : ℤ) ^ (m + 1) := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have ha_inv_t' : (dD.a : G)⁻¹ * dD.t =
      dD.ofTorus (Torus.ofInt (StrothTypeIndex.t200 m).k ![0, -1, 0]) * dD.t := by
    rw [dD.a_eq, ← dD.ofTorus_neg, a_eq_ofInt, t200_neg_vec]
    congr 1
  have ha₁ : dD.ofTorus (Torus.ofInt (StrothTypeIndex.t200 m).k ![0, (2 : ℤ) ^ (m + 1), 0]) =
      (dD.a : G) ^ 2 ^ (m + 1) := by
    rw [dD.t200_a_pow, om200_apply]
    congr 1
    funext i
    fin_cases i <;> simp
  have hb₁ : dD.ofTorus (Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 0, (2 : ℤ) ^ (m + 1)]) =
      (dD.b : G) ^ 2 ^ (m + 1) := by
    rw [dD.t200_b_pow, om200_apply]
    congr 1
    funext i
    fin_cases i <;> simp
  have hc₁ : dD.ofTorus (Torus.ofInt (StrothTypeIndex.t200 m).k ![(2 : ℤ) ^ (m - 1), 0, 0]) =
      (dD.c : G) ^ 2 ^ (m - 1) := by
    rw [dD.t200_c_pow, om200_apply]
    congr 1
    funext i
    fin_cases i <;> simp
  have hφt₁ : (StrothTypeIndex.t200 m).action.φt
      (Torus.ofInt (StrothTypeIndex.t200 m).k ![(2 : ℤ) ^ (m - 1), 0, 0]) =
      Torus.ofInt (StrothTypeIndex.t200 m).k
        ![(2 : ℤ) ^ (m - 1), (2 : ℤ) ^ (m + 1), 0] := by
    rw [t200_φt_vec]
    congr 1
    funext i
    fin_cases i <;> simp
    rw [hpow]
  have hvec : (k - 1) • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, (2 : ℤ) ^ (m + 1), 0] +
      l • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 0, (2 : ℤ) ^ (m + 1)] +
      Torus.ofInt (StrothTypeIndex.t200 m).k ![0, -1, 0] +
      Torus.ofInt (StrothTypeIndex.t200 m).k ![(2 : ℤ) ^ (m - 1), (2 : ℤ) ^ (m + 1), 0] =
      Torus.ofInt (StrothTypeIndex.t200 m).k
        ![(2 : ℤ) ^ (m - 1), -1 + (2 : ℤ) ^ (m + 1) * k, (2 : ℤ) ^ (m + 1) * l] := by
    rw [t200_zsmul_vec, t200_zsmul_vec, t200_add_vec, t200_add_vec, t200_add_vec]
    congr 1
    funext i
    fin_cases i <;> simp <;> ring
  have h : ((dD.a : G) ^ 2 ^ (m + 1)) ^ (k - 1) * ((dD.b : G) ^ 2 ^ (m + 1)) ^ l *
      ((dD.a : G)⁻¹ * dD.t) * ((dD.c : G) ^ 2 ^ (m - 1) * e) =
      dD.ofTorus (Torus.ofInt _ ![(2 : ℤ) ^ (m - 1), -1 + (2 : ℤ) ^ (m + 1) * k,
        (2 : ℤ) ^ (m + 1) * l]) * dD.t * e := by
    calc ((dD.a : G) ^ 2 ^ (m + 1)) ^ (k - 1) * ((dD.b : G) ^ 2 ^ (m + 1)) ^ l *
          ((dD.a : G)⁻¹ * dD.t) * ((dD.c : G) ^ 2 ^ (m - 1) * e)
        = (dD.ofTorus (Torus.ofInt _ ![0, (2 : ℤ) ^ (m + 1), 0])) ^ (k - 1) *
          (dD.ofTorus (Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)])) ^ l *
          (dD.ofTorus (Torus.ofInt _ ![0, -1, 0]) * dD.t) *
          (dD.ofTorus (Torus.ofInt _ ![(2 : ℤ) ^ (m - 1), 0, 0]) * e) := by
          rw [← ha₁, ← hb₁, ← hc₁, ha_inv_t']
      _ = dD.ofTorus ((k - 1) • Torus.ofInt _ ![0, (2 : ℤ) ^ (m + 1), 0]) *
          dD.ofTorus (l • Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)]) *
          (dD.ofTorus (Torus.ofInt _ ![0, -1, 0]) * dD.t) *
          (dD.ofTorus (Torus.ofInt _ ![(2 : ℤ) ^ (m - 1), 0, 0]) * e) := by
          rw [← dD.ofTorus_zsmul, ← dD.ofTorus_zsmul]
      _ = dD.ofTorus ((k - 1) • Torus.ofInt _ ![0, (2 : ℤ) ^ (m + 1), 0]) *
          dD.ofTorus (l • Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)]) *
          dD.ofTorus (Torus.ofInt _ ![0, -1, 0]) * dD.t *
          dD.ofTorus (Torus.ofInt _ ![(2 : ℤ) ^ (m - 1), 0, 0]) * e := by
          group
      _ = dD.ofTorus ((k - 1) • Torus.ofInt _ ![0, (2 : ℤ) ^ (m + 1), 0] +
            l • Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)] + Torus.ofInt _ ![0, -1, 0]) *
          dD.t * dD.ofTorus (Torus.ofInt _ ![(2 : ℤ) ^ (m - 1), 0, 0]) * e := by
          rw [← dD.ofTorus_add, ← dD.ofTorus_add]
      _ = dD.ofTorus ((k - 1) • Torus.ofInt _ ![0, (2 : ℤ) ^ (m + 1), 0] +
            l • Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)] + Torus.ofInt _ ![0, -1, 0]) *
          (dD.ofTorus (Torus.ofInt _ ![(2 : ℤ) ^ (m - 1), (2 : ℤ) ^ (m + 1), 0]) * dD.t) * e := by
          rw [mul_assoc (dD.ofTorus ((k - 1) • Torus.ofInt _ ![0, (2 : ℤ) ^ (m + 1), 0] +
              l • Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)] + Torus.ofInt _ ![0, -1, 0]))
            dD.t (dD.ofTorus (Torus.ofInt _ ![(2 : ℤ) ^ (m - 1), 0, 0]))]
          rw [dD.t_mul_ofTorus, hφt₁]
      _ = dD.ofTorus ((k - 1) • Torus.ofInt _ ![0, (2 : ℤ) ^ (m + 1), 0] +
            l • Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)] + Torus.ofInt _ ![0, -1, 0] +
            Torus.ofInt _ ![(2 : ℤ) ^ (m - 1), (2 : ℤ) ^ (m + 1), 0]) *
          dD.t * e := by
          rw [← mul_assoc, ← dD.ofTorus_add]
      _ = dD.ofTorus (Torus.ofInt _ ![(2 : ℤ) ^ (m - 1), -1 + (2 : ℤ) ^ (m + 1) * k,
            (2 : ℤ) ^ (m + 1) * l]) * dD.t * e := by
          rw [hvec]
  rw [dD.d8_ftf]
  exact h.symm

theorem t200inv1_sq_Dte_j0_arith (hrel : Rel34inv dD e 0 1 2) (x : Fin 3 → ℤ)
    (h2 : dD.ofTorus (Torus.ofInt _ x) * dD.t * e *
      (dD.ofTorus (Torus.ofInt _ x) * dD.t * e) = 1) :
    (2 : ℤ) ^ (m + 1) ∣ x 2 ∧ (2 : ℤ) ^ (m + 1) ∣ x 1 - 2 * x 0 + 1 := by
  have hsq := h2
  rw [t200inv1_sq_Dte_j0 dD hrel x] at hsq
  rw [dD.ofTorus_eq_one_iff, t200_ofInt_eq_zero_iff] at hsq
  obtain ⟨-, h1, h3⟩ := hsq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h1 h3
  have hpow : (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ]; ring
  have hz : (2 : ℤ) ^ (m + 1) ∣ x 2 := by
    rw [hpow] at h3
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h3
  refine ⟨hz, ?_⟩
  rw [hpow] at h1
  have h1' : (2 : ℤ) ^ (m + 1) ∣ x 1 - 2 * x 0 + x 2 + 1 := by
    refine (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp ?_
    convert h1 using 1
    ring
  have hsub := dvd_sub h1' hz
  convert hsub using 1
  ring

theorem t200inv1_conj_Dte_coord_j0 (hrel : Rel34inv dD e 0 1 2) (x : Fin 3 → ℤ) :
    Torus.ofInt _ x - Torus.ofInt _ ![0, 0, -x 0] +
      (StrothTypeIndex.t200 m).action.φt
        ((dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![0, 0, -x 0])) =
      Torus.ofInt _ ![0, x 1 - 2 * x 0, x 2] := by
  rw [StrothWeakTypeData.t200inv1_φe dD hrel, t200_φt_vec, ← Torus.ofInt_sub,
    ← Torus.ofInt_add]
  congr 1
  funext i
  fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]
  ring

theorem t200inv1_conj_Dte_e (hrel : Rel34inv dD e 0 1 2)
    (v : Torus (StrothTypeIndex.t200 m).k)
    (h2 : dD.ofTorus v * dD.t * e * (dD.ofTorus v * dD.t * e) = 1) :
    ∃ q ∈ D, q⁻¹ * (dD.ofTorus v * dD.t * e) * q ∈ Subgroup.closure
      {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.cab * dD.uv, (dD.a : G)⁻¹ * dD.t,
        e} := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  obtain ⟨hz, hy⟩ := t200inv1_sq_Dte_j0_arith dD hrel x h2
  obtain ⟨α, hα⟩ := hy
  obtain ⟨β, hβ⟩ := hz
  refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 0, -x 0]), dD.ofTorus_mem _, ?_⟩
  have hconj := t200inv1_conj_ofTorus_Dte dD hrel (Torus.ofInt _ ![0, 0, -x 0])
    (Torus.ofInt _ x)
  rw [← dD.d8_ftf, hconj, t200inv1_conj_Dte_coord_j0 dD hrel x]
  have hα' : x 1 - 2 * x 0 = -1 + (2 : ℤ) ^ (m + 1) * α := by linarith
  rw [hα', hβ, t200inv1_prod_Dte_e dD α β]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _
        ((Subgroup.closure _).zpow_mem (Subgroup.subset_closure (by simp)) α)
        ((Subgroup.closure _).zpow_mem (Subgroup.subset_closure (by simp)) β))
      (Subgroup.subset_closure (by simp)))
    (Subgroup.subset_closure (by simp))

theorem t200inv1_sq_Dte_j2M_arith (hm : 1 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) 1 2) (x : Fin 3 → ℤ)
    (h2 : dD.ofTorus (Torus.ofInt _ x) * dD.t * e *
      (dD.ofTorus (Torus.ofInt _ x) * dD.t * e) = 1) (s : ℤ)
    (hs : s = (2 : ℤ) ^ (m - 1) - x 0) :
    (2 : ℤ) ^ (m + 1) ∣ x 2 ∧
      (2 : ℤ) ^ (m + 1) ∣ x 1 + 2 * (1 - (2 : ℤ) ^ (m + 1)) * s + 1 := by
  have hsq := h2
  rw [t200inv1_sq_Dte_j2M dD hrel x] at hsq
  rw [dD.ofTorus_eq_one_iff, t200_ofInt_eq_zero_iff] at hsq
  obtain ⟨-, h1, h3⟩ := hsq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h1 h3
  have hpow1 : (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ]; ring
  have h2M : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have h2P : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hodd : Odd (1 - (2 : ℤ) ^ m) :=
    Odd.sub_even odd_one ((even_two : Even (2 : ℤ)).pow_of_ne_zero (by omega : m ≠ 0))
  have hcop : IsCoprime ((2 : ℤ) ^ (m + 1)) (1 - (2 : ℤ) ^ m) := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    exact (show IsCoprime (2 : ℤ) (2 * k + 1) from ⟨-k, 1, by ring⟩).pow_left
  have hz : (2 : ℤ) ^ (m + 1) ∣ x 2 := by
    have h := h3
    rw [hpow1] at h
    have h2' : (2 : ℤ) ^ (m + 1) ∣ (1 - (2 : ℤ) ^ m) * x 2 := by
      refine (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp ?_
      convert h using 1
      ring
    exact hcop.dvd_of_dvd_mul_left h2'
  have h1' : (2 : ℤ) ^ (m + 1) ∣ (1 - (2 : ℤ) ^ m) * x 1 - 2 * x 0 + 1 := by
    have h := h1
    rw [hpow1] at h
    have hB : (2 : ℤ) ^ (m + 1) ∣
        (1 - (2 : ℤ) ^ m) * x 1 - 2 * x 0 + (1 - (2 : ℤ) ^ (m + 1)) * x 2 + 1 := by
      refine (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp ?_
      convert h using 1
      ring
    have hC : (2 : ℤ) ^ (m + 1) ∣ (1 - (2 : ℤ) ^ (m + 1)) * x 2 :=
      dvd_mul_of_dvd_right hz _
    have hsub := dvd_sub hB hC
    convert hsub using 1
    ring
  have hyodd : Odd (x 1) := by
    rw [← Int.not_even_iff_odd]
    intro hye
    have h2dvd : (2 : ℤ) ∣ (1 - (2 : ℤ) ^ m) * x 1 - 2 * x 0 + 1 :=
      dvd_trans (dvd_pow_self 2 (by omega : m + 1 ≠ 0)) h1'
    have h1dvd : (2 : ℤ) ∣ (1 - (2 : ℤ) ^ m) * x 1 :=
      dvd_mul_of_dvd_right (even_iff_two_dvd.mp hye) _
    have h2dvd' : (2 : ℤ) ∣ 2 * x 0 := ⟨x 0, by ring⟩
    have hone : (2 : ℤ) ∣ 1 := by
      have h := dvd_add (dvd_sub h2dvd h1dvd) h2dvd'
      convert h using 1
      ring
    norm_num at hone
  refine ⟨hz, ?_⟩
  have hkey : x 1 + 2 * (1 - (2 : ℤ) ^ (m + 1)) * s + 1 =
      ((1 - (2 : ℤ) ^ m) * x 1 - 2 * x 0 + 1) + (2 : ℤ) ^ m * (x 1 + 1) +
        2 * (2 : ℤ) ^ m * (2 * x 0 - (2 : ℤ) ^ m) := by
    rw [h2M, h2P, hs]
    ring
  rw [hkey]
  have hM : (2 : ℤ) ^ (m + 1) ∣ (2 : ℤ) ^ m * (x 1 + 1) := by
    obtain ⟨t, ht⟩ := hyodd
    refine ⟨t + 1, ?_⟩
    rw [ht, pow_succ]
    ring
  have h2Mdiv : (2 : ℤ) ^ (m + 1) ∣ 2 * (2 : ℤ) ^ m * (2 * x 0 - (2 : ℤ) ^ m) := by
    refine ⟨2 * x 0 - (2 : ℤ) ^ m, ?_⟩
    rw [pow_succ]
    ring
  exact dvd_add (dvd_add h1' hM) h2Mdiv

theorem t200inv1_conj_Dte_coord_j2M (hrel : Rel34inv dD e (2 ^ (m + 1)) 1 2)
    (x : Fin 3 → ℤ) (s : ℤ) :
    Torus.ofInt _ x - Torus.ofInt _ ![0, 0, s] +
      (StrothTypeIndex.t200 m).action.φt
        ((dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![0, 0, s])) =
      Torus.ofInt _ ![x 0 + (1 - (2 : ℤ) ^ (m + 1)) * s,
        x 1 + 2 * (1 - (2 : ℤ) ^ (m + 1)) * s, x 2 - (2 : ℤ) ^ (m + 1) * s] := by
  rw [StrothWeakTypeData.t200inv1_φe dD hrel, t200_φt_vec, ← Torus.ofInt_sub,
    ← Torus.ofInt_add]
  congr 1
  funext i
  fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail] <;> ring

theorem t200inv1_conj_Dte_target_j2M (hm : 1 ≤ m) {x : Fin 3 → ℤ} {s α β : ℤ}
    (hs : s = (2 : ℤ) ^ (m - 1) - x 0)
    (hα : x 1 + 2 * (1 - (2 : ℤ) ^ (m + 1)) * s + 1 = (2 : ℤ) ^ (m + 1) * α)
    (hβ : x 2 = (2 : ℤ) ^ (m + 1) * β) :
    Torus.ofInt (StrothTypeIndex.t200 m).k
        ![x 0 + (1 - (2 : ℤ) ^ (m + 1)) * s,
          x 1 + 2 * (1 - (2 : ℤ) ^ (m + 1)) * s, x 2 - (2 : ℤ) ^ (m + 1) * s] =
      Torus.ofInt (StrothTypeIndex.t200 m).k
        ![(2 : ℤ) ^ (m - 1), -1 + (2 : ℤ) ^ (m + 1) * α,
          (2 : ℤ) ^ (m + 1) * (β - s)] := by
  have h2P : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
    ring
  rw [t200_ofInt_eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨2 * s, ?_⟩
    simp only [Matrix.cons_val_zero]
    rw [hs, pow_succ, h2P]
    ring
  · have hx1 : x 1 + 2 * (1 - (2 : ℤ) ^ (m + 1)) * s = (2 : ℤ) ^ (m + 1) * α - 1 := by
      linarith [hα]
    refine ⟨0, ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hx1]
    ring
  · refine ⟨0, ?_⟩
    simp only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [hβ]
    ring

theorem t200inv1_conj_Dte_c₁e (hm : 1 ≤ m) (hrel : Rel34inv dD e (2 ^ (m + 1)) 1 2)
    (v : Torus (StrothTypeIndex.t200 m).k)
    (h2 : dD.ofTorus v * dD.t * e * (dD.ofTorus v * dD.t * e) = 1) :
    ∃ q ∈ D, q⁻¹ * (dD.ofTorus v * dD.t * e) * q ∈ Subgroup.closure
      {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.cab * dD.uv, (dD.a : G)⁻¹ * dD.t,
        (dD.c : G) ^ 2 ^ (m - 1) * e} := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  let s : ℤ := (2 : ℤ) ^ (m - 1) - x 0
  obtain ⟨hz, hnew⟩ := t200inv1_sq_Dte_j2M_arith dD hm hrel x h2 s rfl
  obtain ⟨α, hα⟩ := hnew
  obtain ⟨β, hβ⟩ := hz
  refine ⟨dD.ofTorus (Torus.ofInt _ ![0, 0, s]), dD.ofTorus_mem _, ?_⟩
  have hconj := t200inv1_conj_ofTorus_Dte dD hrel (Torus.ofInt _ ![0, 0, s])
    (Torus.ofInt _ x)
  rw [← dD.d8_ftf, hconj, t200inv1_conj_Dte_coord_j2M dD hrel x s]
  rw [t200inv1_conj_Dte_target_j2M (x := x) (s := s) (α := α) (β := β) hm rfl hα hβ]
  rw [t200inv1_prod_Dte_c₁e dD hm α (β - s)]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _
        ((Subgroup.closure _).zpow_mem (Subgroup.subset_closure (by simp)) (α - 1))
        ((Subgroup.closure _).zpow_mem (Subgroup.subset_closure (by simp)) (β - s)))
      (Subgroup.subset_closure (by simp)))
    (Subgroup.subset_closure (by simp))

end Stroth47Core

end CFSG.CGT.Stroth77
