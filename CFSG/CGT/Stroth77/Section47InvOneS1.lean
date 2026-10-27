module

public import CFSG.CGT.Stroth77.Section47ExtremalH9
public import CFSG.CGT.Stroth77.Section47Harada

public section

namespace CFSG.CGT.Stroth77

open Stroth34T200

namespace Stroth47Inv1

theorem two_pow_dvd_two_mul {m : ℕ} (hm : 1 ≤ m) {x : ℤ} (h : (2 : ℤ) ^ m ∣ 2 * x) :
    (∃ k : ℤ, x = (2 : ℤ) ^ m * k) ∨
      ∃ k : ℤ, x = (2 : ℤ) ^ (m - 1) + (2 : ℤ) ^ m * k := by
  have hm' : m = (m - 1) + 1 := by omega
  have h2m : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by
    conv_lhs => rw [hm']
    rw [pow_succ']
  rw [h2m] at h
  have hx : (2 : ℤ) ^ (m - 1) ∣ x := by
    refine (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp ?_
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  obtain ⟨t, ht⟩ := hx
  rcases Int.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine Or.inl ⟨k, ?_⟩
    rw [ht, hk, h2m]
    ring
  · refine Or.inr ⟨k, ?_⟩
    rw [ht, hk, h2m]
    ring

end Stroth47Inv1

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))

theorem t200_c_pow_coord (j : ℕ) :
    (dD.c : G) ^ j = dD.ofTorus (Torus.ofInt _ ![(j : ℤ), 0, 0]) := by
  rw [dD.c_eq, ← dD.ofTorus_nsmul, c_eq_ofInt, ← natCast_zsmul, t200_zsmul_vec]
  simp only [mul_one, mul_zero]

theorem t200_a_pow_coord (j : ℕ) :
    (dD.a : G) ^ j = dD.ofTorus (Torus.ofInt _ ![0, (j : ℤ), 0]) := by
  rw [dD.a_eq, ← dD.ofTorus_nsmul, a_eq_ofInt, ← natCast_zsmul, t200_zsmul_vec]
  simp only [mul_one, mul_zero]

theorem t200_b_pow_coord (j : ℕ) :
    (dD.b : G) ^ j = dD.ofTorus (Torus.ofInt _ ![0, 0, (j : ℤ)]) := by
  rw [dD.b_eq, ← dD.ofTorus_nsmul, b_eq_ofInt, ← natCast_zsmul, t200_zsmul_vec]
  simp only [mul_one, mul_zero]

theorem t200_u_conj_a_coord : dD.u⁻¹ * (dD.a : G) * dD.u = dD.b := by
  rw [dD.a_eq, a_eq_ofInt, dD.conj_ofTorus dD.u_mem dD.u_conj, t200_φu_vec, dD.b_eq,
    b_eq_ofInt]

theorem t200_cab_eq : dD.cab = dD.ofTorus (Torus.ofInt _ ![1, 1, 1]) := by
  rw [StrothWeakTypeData.cab, dD.c_eq, dD.a_eq, dD.b_eq, c_eq_ofInt, a_eq_ofInt, b_eq_ofInt,
    ← dD.ofTorus_add, ← dD.ofTorus_add, t200_add_vec, t200_add_vec]
  congr 1

theorem t200_uv_conj_c₁ (hm : 1 ≤ m) :
    dD.uv⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * dD.uv =
      (dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) := by
  rw [t200_c_pow_coord, dD.conj_ofTorus dD.uv_mem dD.uv_conj, t200_φuv_vec,
    t200_a_pow_coord, t200_b_pow_coord, ← dD.ofTorus_add, ← dD.ofTorus_add]
  have hpow : (2 : ℤ) ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hpow1 : (2 : ℤ) ^ (m + 1) = 2 ^ (m - 1) * 4 := by
    rw [pow_succ, hpow]
    ring
  have hpow2 : (2 : ℤ) ^ (m + 2) = 2 ^ (m - 1) * 8 := by
    rw [pow_succ, hpow1]
    ring
  congr 1
  rw [t200_add_vec, t200_add_vec, t200_vec_eq_iff]
  refine ⟨⟨2, ?_⟩, ⟨1, ?_⟩, ⟨1, ?_⟩⟩ <;> push_cast <;>
    simp only [hpow, hpow1, hpow2] <;> ring

theorem t200_cab_uv_mul_self : dD.cab * dD.uv * (dD.cab * dD.uv) = 1 := by
  rw [t200_cab_eq, ← dD.d8_tff, dD.nf_mul_self, Bool.and_false, dD.d8_fff, mul_one]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, t200_φuv_vec, t200_add_vec]
  rw [← dD.ofTorus_zero, dD.ofTorus_inj.eq_iff, ← Torus.ofInt_zero]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t200_u_comm_cab_uv : dD.u * (dD.cab * dD.uv) = dD.cab * dD.uv * dD.u := by
  rw [t200_cab_eq, dD.u_mul_ofTorus_mul, t200_φu_vec, ← dD.uv_comm_u, mul_assoc]

theorem t200_isConj_u_mul_cab_uv : IsConj (dD.u * (dD.cab * dD.uv)) dD.u := by
  have ht_cab : dD.t * (dD.cab : G) * dD.t = (dD.a : G) * (dD.b : G)⁻¹ := by
    rw [t200_cab_eq, dD.t_mul_ofTorus, t200_φt_vec, mul_assoc, dD.t_sq, mul_one]
    rw [show Torus.ofInt _ ![1 - 1, 4 * 1 - 1 - 2 * 1, -1] =
        Torus.ofInt _ ![0, 1, 0] + Torus.ofInt _ ![0, 0, -1] by
      rw [t200_add_vec]
      congr 1]
    have hb_inv : (dD.b : G)⁻¹ = dD.ofTorus (Torus.ofInt _ ![0, 0, -1]) := by
      rw [dD.b_eq, ← dD.ofTorus_neg, b_eq_ofInt, t200_neg_vec]
      congr 1
    rw [dD.ofTorus_add, dD.a_eq, a_eq_ofInt, hb_inv]
  have ht_uv : dD.t * dD.uv * dD.t = dD.uv := by
    rw [← dD.uv_comm_t, mul_assoc, dD.t_sq, mul_one]
  have ht_u : dD.t * dD.u * dD.t = dD.u * dD.uv := by
    rw [dD.t_u, mul_assoc, dD.t_sq, mul_one]
  have hcomm := t200_u_comm_cab_uv dD
  have hconj_mul (x y : G) :
      (dD.t * x * dD.t) * (dD.t * y * dD.t) = dD.t * (x * y) * dD.t := by
    calc (dD.t * x * dD.t) * (dD.t * y * dD.t)
        = dD.t * x * (dD.t * dD.t) * y * dD.t := by group
      _ = dD.t * x * y * dD.t := by rw [dD.t_sq]; group
      _ = dD.t * (x * y) * dD.t := by group
  have ht_y : dD.t * ((dD.cab * dD.uv) * dD.u) * dD.t =
      dD.a * (dD.b : G)⁻¹ * dD.u := by
    calc dD.t * ((dD.cab * dD.uv) * dD.u) * dD.t
        = (dD.t * (dD.cab * dD.uv) * dD.t) * (dD.t * dD.u * dD.t) :=
          (hconj_mul _ _).symm
      _ = ((dD.t * dD.cab * dD.t) * (dD.t * dD.uv * dD.t)) * (dD.t * dD.u * dD.t) := by
          rw [← hconj_mul]
      _ = (dD.a * (dD.b : G)⁻¹) * (dD.uv * (dD.u * dD.uv)) := by
        rw [ht_cab, ht_uv, ht_u]
        simp only [mul_assoc]
      _ = dD.a * (dD.b : G)⁻¹ * dD.u := by
        rw [← mul_assoc dD.uv dD.u dD.uv, dD.uv_comm_u, mul_assoc dD.u dD.uv dD.uv,
          dD.uv_sq, mul_one]
  have hu_a : dD.u * dD.a = dD.b * dD.u := by
    have h := t200_u_conj_a_coord dD
    rw [dD.u_inv] at h
    rw [← h, mul_assoc, dD.u_sq, mul_one]
  have hfinal : (dD.a : G)⁻¹ * (dD.a * (dD.b : G)⁻¹ * dD.u) * dD.a = dD.u := by
    calc (dD.a : G)⁻¹ * (dD.a * (dD.b : G)⁻¹ * dD.u) * dD.a
        = (dD.b : G)⁻¹ * (dD.u * dD.a) := by group
      _ = (dD.b : G)⁻¹ * (dD.b * dD.u) := by rw [hu_a]
      _ = dD.u := by group
  refine isConj_iff.mpr ⟨(dD.a : G)⁻¹ * dD.t, ?_⟩
  have hginv : ((dD.a : G)⁻¹ * dD.t)⁻¹ = dD.t * dD.a := by
    rw [mul_inv_rev, dD.t_inv, inv_inv]
  calc ((dD.a : G)⁻¹ * dD.t) * (dD.u * (dD.cab * dD.uv)) * ((dD.a : G)⁻¹ * dD.t)⁻¹
      = (dD.a : G)⁻¹ * (dD.t * ((dD.cab * dD.uv) * dD.u) * dD.t) * dD.a := by
        rw [hcomm, hginv]
        group
    _ = (dD.a : G)⁻¹ * (dD.a * (dD.b : G)⁻¹ * dD.u) * dD.a := by rw [ht_y]
    _ = dD.u := hfinal

theorem t200_rho_conj_cab_uv : dD.ρ⁻¹ * (dD.cab * dD.uv) * dD.ρ = (dD.a : G)⁻¹ * dD.t := by
  have ha_inv : (dD.a : G)⁻¹ = dD.ofTorus (Torus.ofInt _ ![0, -1, 0]) := by
    rw [dD.a_eq, ← dD.ofTorus_neg, a_eq_ofInt, t200_neg_vec]
    congr 1
  have hcab : dD.ρ⁻¹ * (dD.cab : G) * dD.ρ = (dD.a : G)⁻¹ := by
    rw [t200_cab_eq, dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, t200_φρ_vec, ha_inv]
    congr 1
  have huv : dD.ρ⁻¹ * dD.uv * dD.ρ = dD.t := by
    calc dD.ρ⁻¹ * dD.uv * dD.ρ = dD.ρ⁻¹ * (dD.uv * dD.ρ) := by rw [mul_assoc]
      _ = dD.ρ⁻¹ * (dD.ρ * dD.t) := by rw [dD.uv_rho]
      _ = dD.t := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  calc dD.ρ⁻¹ * (dD.cab * dD.uv) * dD.ρ
      = (dD.ρ⁻¹ * dD.cab * dD.ρ) * (dD.ρ⁻¹ * dD.uv * dD.ρ) := by group
    _ = (dD.a : G)⁻¹ * dD.t := by rw [hcab, huv]

theorem t200_isConj_a_t : IsConj ((dD.a : G) * dD.t) (dD.cab * dD.uv) := by
  have hρ : IsConj (dD.cab * dD.uv) ((dD.a : G)⁻¹ * dD.t) := by
    refine isConj_iff.mpr ⟨dD.ρ⁻¹, ?_⟩
    rw [inv_inv]
    exact t200_rho_conj_cab_uv dD
  have ha_inv : (dD.a : G)⁻¹ = dD.ofTorus (Torus.ofInt _ ![0, -1, 0]) := by
    rw [dD.a_eq, ← dD.ofTorus_neg, a_eq_ofInt, t200_neg_vec]
    congr 1
  have h2 : dD.t * (dD.a : G)⁻¹ = dD.a * dD.t := by
    rw [ha_inv, dD.t_mul_ofTorus, t200_φt_vec, dD.a_eq, a_eq_ofInt]
    congr 1
  have h3 : dD.t * dD.a = (dD.a : G)⁻¹ * dD.t := by
    have h4 : dD.t * (dD.a : G)⁻¹ * dD.t = dD.a := by
      rw [h2, mul_assoc, dD.t_sq, mul_one]
    calc dD.t * dD.a
        = dD.t * (dD.t * (dD.a : G)⁻¹ * dD.t) := by
          conv_lhs => rw [← h4]
      _ = (dD.t * dD.t) * ((dD.a : G)⁻¹ * dD.t) := by group
      _ = (dD.a : G)⁻¹ * dD.t := by rw [dD.t_sq, one_mul]
  have hat : IsConj ((dD.a : G) * dD.t) ((dD.a : G)⁻¹ * dD.t) := by
    refine isConj_iff.mpr ⟨(dD.a : G)⁻¹, ?_⟩
    calc (dD.a : G)⁻¹ * (dD.a * dD.t) * ((dD.a : G)⁻¹)⁻¹
        = dD.t * dD.a := by group
      _ = (dD.a : G)⁻¹ * dD.t := h3
  exact hat.trans hρ.symm

theorem t200_conj_Du_of_mul_self (hm : 1 ≤ m) {y : G} (hy : y * dD.u ∈ D) (h2 : y * y = 1) :
    ∃ q ∈ D, q⁻¹ * y * q = dD.u ∨ q⁻¹ * y * q = (dD.c : G) ^ 2 ^ (m - 1) * dD.u := by
  obtain ⟨v, hv⟩ := dD.exists_ofTorus hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hy_eq : y = dD.ofTorus (Torus.ofInt _ x) * dD.d8 false false true := by
    rw [dD.d8_fft, ← hv, mul_assoc, dD.u_sq, mul_one]
  have hsq : (2 : ℤ) ^ m ∣ x 0 + x 0 ∧ (2 : ℤ) ^ (m + 2) ∣ x 1 + x 2 := by
    have h := h2
    rw [hy_eq, dD.nf_mul_self, Bool.and_false, dD.d8_fff, mul_one] at h
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply] at h
    rw [t200_φu, ← Torus.ofInt_add, dD.ofTorus_eq_one_iff, Torus.ofInt_eq_zero_iff] at h
    refine ⟨h 0, ?_⟩
    simpa [t200_k] using h 1
  set q : G := dD.ofTorus (Torus.ofInt _ ![0, x 1, 0]) with hq
  have hqD : q ∈ D := dD.ofTorus_mem _
  have hqd : q⁻¹ * dD.ofTorus (Torus.ofInt _ x) * q = dD.ofTorus (Torus.ofInt _ x) := by
    have hc : q * dD.ofTorus (Torus.ofInt _ x) =
        dD.ofTorus (Torus.ofInt _ x) * q := by
      rw [hq]
      exact dD.ofTorus_comm _ _
    calc q⁻¹ * dD.ofTorus (Torus.ofInt _ x) * q
        = q⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * q) := by rw [mul_assoc]
      _ = q⁻¹ * (q * dD.ofTorus (Torus.ofInt _ x)) := by rw [← hc]
      _ = dD.ofTorus (Torus.ofInt _ x) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have huq : q⁻¹ * dD.u * q =
      dD.ofTorus (Torus.ofInt _ ![0, -x 1, x 1]) * dD.u := by
    rw [hq, mul_assoc, dD.u_mul_ofTorus, t200_φu, ← mul_assoc, ← dD.ofTorus_neg,
      ← Torus.ofInt_neg, ← dD.ofTorus_add, ← Torus.ofInt_add, mul_right_cancel_iff,
      dD.ofTorus_inj.eq_iff, Torus.ofInt_eq_ofInt_iff]
    intro i
    fin_cases i <;> simp
  have hqy : q⁻¹ * y * q =
      dD.ofTorus (Torus.ofInt _ ![x 0, 0, x 2 + x 1]) * dD.u := by
    calc q⁻¹ * y * q
        = (q⁻¹ * dD.ofTorus (Torus.ofInt _ x) * q) * (q⁻¹ * dD.u * q) := by
          rw [hy_eq, dD.d8_fft]
          group
      _ = dD.ofTorus (Torus.ofInt _ x) *
          (dD.ofTorus (Torus.ofInt _ ![0, -x 1, x 1]) * dD.u) := by rw [hqd, huq]
      _ = dD.ofTorus (Torus.ofInt _ ![x 0, 0, x 2 + x 1]) * dD.u := by
        rw [← mul_assoc, ← dD.ofTorus_add, ← Torus.ofInt_add, mul_right_cancel_iff,
          dD.ofTorus_inj.eq_iff, Torus.ofInt_eq_ofInt_iff]
        intro i
        fin_cases i <;> simp
  have hxsum : dD.ofTorus (Torus.ofInt _ ![x 0, 0, x 2 + x 1]) =
      dD.ofTorus (Torus.ofInt _ ![x 0, 0, 0]) := by
    rw [dD.ofTorus_inj.eq_iff, Torus.ofInt_eq_ofInt_iff]
    intro i
    fin_cases i
    · simp
    · simp
    · exact Int.modEq_zero_iff_dvd.mpr (by simpa [t200_k, add_comm] using hsq.2)
  have hclass : dD.ofTorus (Torus.ofInt _ ![x 0, 0, 0]) = 1 ∨
      dD.ofTorus (Torus.ofInt _ ![x 0, 0, 0]) = (dD.c : G) ^ 2 ^ (m - 1) := by
    have h2x : (2 : ℤ) ^ m ∣ 2 * x 0 := by simpa [two_mul] using hsq.1
    rcases Stroth47Inv1.two_pow_dvd_two_mul hm h2x with ⟨k, hk⟩ | ⟨k, hk⟩
    · left
      rw [dD.ofTorus_eq_one_iff, t200_vec_eq_zero_iff]
      refine ⟨⟨k, ?_⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
      rw [hk]
    · right
      rw [t200_c_pow_coord, dD.ofTorus_inj.eq_iff, t200_vec_eq_iff]
      refine ⟨⟨-k, ?_⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
      rw [hk]
      push_cast
      ring
  refine ⟨q, hqD, ?_⟩
  rcases hclass with h1 | h1
  · left
    rw [hqy, hxsum, h1, one_mul]
  · right
    rw [hqy, hxsum, h1]

theorem t200_conj_Duv_of_mul_self (hm : 1 ≤ m) {y : G} (hy : y * dD.uv ∈ D) (h2 : y * y = 1) :
    ∃ q ∈ D, q⁻¹ * y * q = dD.uv ∨ q⁻¹ * y * q = dD.cab * dD.uv := by
  obtain ⟨v, hv⟩ := dD.exists_ofTorus hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hy_eq : y = dD.ofTorus (Torus.ofInt _ x) * dD.uv := by
    rw [← hv, mul_assoc, dD.uv_sq, mul_one]
  have hsq : (2 : ℤ) ^ (m + 2) ∣ 2 * (x 1 + x 2 - 2 * x 0) := by
    have h := h2
    rw [hy_eq, ← dD.d8_tff, dD.nf_mul_self, Bool.and_false, dD.d8_fff, mul_one] at h
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply] at h
    rw [t200_φuv, ← Torus.ofInt_add, dD.ofTorus_eq_one_iff, Torus.ofInt_eq_zero_iff] at h
    have := h 1
    simp only [t200_k, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at this
    convert this using 1; ring
  have hdvd : ∀ B : ℤ, (2 : ℤ) ^ (m + 2) ∣ 2 * B → (2 : ℤ) ^ (m + 1) ∣ B := by
    intro B h
    rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) by rw [pow_succ]; ring] at h
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h
  have hA : (2 : ℤ) ^ (m + 1) ∣ x 1 + x 2 - 2 * x 0 := hdvd _ hsq
  have hdvd1 : ∀ B : ℤ, (2 : ℤ) ^ (m + 1) ∣ 2 * B → (2 : ℤ) ^ m ∣ B := by
    intro B h
    rw [show (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ]; ring] at h
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h
  have h2dvd : (2 : ℤ) ∣ x 1 + x 2 := by
    have h1 : (2 : ℤ) ∣ x 1 + x 2 - 2 * x 0 :=
      dvd_trans (dvd_pow_self 2 (by omega : m + 1 ≠ 0)) hA
    have h2 : (2 : ℤ) ∣ 2 * x 0 := dvd_mul_right _ _
    have h3 := dvd_add h1 h2
    simpa [sub_add_cancel, add_comm, add_left_comm, add_assoc] using h3
  set q : ℤ → ℤ → G := fun a b => dD.ofTorus (Torus.ofInt _ ![0, -b, -a]) with hq
  have hqD : ∀ a b, q a b ∈ D := fun a b => dD.ofTorus_mem _
  have hqd : ∀ a b, (q a b)⁻¹ * dD.ofTorus (Torus.ofInt _ x) * q a b =
      dD.ofTorus (Torus.ofInt _ x) := by
    intro a b
    have hc : q a b * dD.ofTorus (Torus.ofInt _ x) =
        dD.ofTorus (Torus.ofInt _ x) * q a b := by
      simp only [hq]
      exact dD.ofTorus_comm _ _
    calc (q a b)⁻¹ * dD.ofTorus (Torus.ofInt _ x) * q a b
        = (q a b)⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * q a b) := by rw [mul_assoc]
      _ = (q a b)⁻¹ * (q a b * dD.ofTorus (Torus.ofInt _ x)) := by rw [← hc]
      _ = dD.ofTorus (Torus.ofInt _ x) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hquv : ∀ a b, (q a b)⁻¹ * dD.uv * q a b =
      dD.ofTorus (Torus.ofInt _ ![-(a + b), -2 * a, -2 * b]) * dD.uv := by
    intro a b
    simp only [hq]
    rw [mul_assoc, dD.uv_mul_ofTorus, t200_φuv, ← mul_assoc, ← dD.ofTorus_neg,
      ← Torus.ofInt_neg, ← dD.ofTorus_add, ← Torus.ofInt_add, mul_right_cancel_iff,
      dD.ofTorus_inj.eq_iff, Torus.ofInt_eq_ofInt_iff]
    intro i
    fin_cases i <;> rw [Int.modEq_iff_dvd] <;>
      simp [add_comm]
  have hconj : ∀ a b, (q a b)⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * dD.uv) * q a b =
      dD.ofTorus (Torus.ofInt _ ![x 0 - (a + b), x 1 - 2 * a, x 2 - 2 * b]) * dD.uv := by
    intro a b
    calc (q a b)⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * dD.uv) * q a b
        = ((q a b)⁻¹ * dD.ofTorus (Torus.ofInt _ x) * q a b) *
            ((q a b)⁻¹ * dD.uv * q a b) := by group
      _ = dD.ofTorus (Torus.ofInt _ x) *
          (dD.ofTorus (Torus.ofInt _ ![-(a + b), -2 * a, -2 * b]) * dD.uv) := by
            rw [hqd, hquv]
      _ = dD.ofTorus (Torus.ofInt _ ![x 0 - (a + b), x 1 - 2 * a, x 2 - 2 * b]) * dD.uv := by
        rw [← mul_assoc, ← dD.ofTorus_add, ← Torus.ofInt_add, mul_right_cancel_iff,
          dD.ofTorus_inj.eq_iff, Torus.ofInt_eq_ofInt_iff]
        intro i
        fin_cases i <;> rw [Int.modEq_iff_dvd] <;>
          simp [sub_eq_add_neg, add_comm, add_assoc]
  rcases Int.even_or_odd (x 1) with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
    rcases Int.even_or_odd (x 2) with ⟨b, hb⟩ | ⟨b, hb⟩
  · refine ⟨q a b, hqD a b, Or.inl ?_⟩
    rw [hy_eq, hconj a b, ha, hb]
    have hdiv : (2 : ℤ) ^ m ∣ x 0 - (a + b) := by
      have h := hA
      rw [ha, hb] at h
      have hB : (2 : ℤ) ^ m ∣ a + b - x 0 :=
        hdvd1 (a + b - x 0) (by convert h using 1; ring)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using dvd_neg.mpr hB
    rw [show dD.ofTorus (Torus.ofInt _ ![x 0 - (a + b), a + a - 2 * a, b + b - 2 * b]) =
        1 by
      rw [dD.ofTorus_eq_one_iff, t200_vec_eq_zero_iff]
      exact ⟨hdiv, ⟨0, by ring⟩, ⟨0, by ring⟩⟩]
    rw [one_mul]
  · exfalso
    have he : Even (x 1 + x 2) := even_iff_two_dvd.mpr h2dvd
    rw [ha, hb] at he
    exact (Int.not_even_iff_odd.mpr ⟨a + b, by ring⟩) he
  · exfalso
    have he : Even (x 1 + x 2) := even_iff_two_dvd.mpr h2dvd
    rw [ha, hb] at he
    exact (Int.not_even_iff_odd.mpr ⟨a + b, by ring⟩) he
  · refine ⟨q a b, hqD a b, Or.inr ?_⟩
    rw [hy_eq, hconj a b, ha, hb, t200_cab_eq]
    have hdiv : (2 : ℤ) ^ m ∣ 1 - (x 0 - (a + b)) := by
      have h := hA
      rw [ha, hb] at h
      have hB : (2 : ℤ) ^ m ∣ a + b + 1 - x 0 :=
        hdvd1 (a + b + 1 - x 0) (by convert h using 1; ring)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hB
    rw [show dD.ofTorus (Torus.ofInt _ ![x 0 - (a + b), 2 * a + 1 - 2 * a, 2 * b + 1 - 2 * b]) =
        dD.ofTorus (Torus.ofInt _ ![1, 1, 1]) by
      congr 1
      rw [t200_vec_eq_iff]
      exact ⟨hdiv, ⟨0, by ring⟩, ⟨0, by ring⟩⟩]

theorem t200_conj_Dt_of_mul_self (hm : 1 ≤ m) {y : G} (hy : y * dD.t ∈ D) (h2 : y * y = 1) :
    ∃ q ∈ D, q⁻¹ * y * q = dD.t ∨ q⁻¹ * y * q = (dD.a : G) * dD.t := by
  obtain ⟨v, hv⟩ := dD.exists_ofTorus hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hy_eq : y = dD.ofTorus (Torus.ofInt _ x) * dD.t := by
    rw [← hv, mul_assoc, dD.t_sq, mul_one]
  have hsq : (2 : ℤ) ^ (m + 2) ∣ 2 * (2 * x 0 - x 2) := by
    have h := h2
    rw [hy_eq, ← dD.d8_ftf, dD.nf_mul_self, Bool.false_and, dD.d8_fff, mul_one] at h
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply] at h
    rw [t200_φt, ← Torus.ofInt_add, dD.ofTorus_eq_one_iff, Torus.ofInt_eq_zero_iff] at h
    have := h 1
    simp only [t200_k, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at this
    convert this using 1; ring
  have hdvd : ∀ B : ℤ, (2 : ℤ) ^ (m + 2) ∣ 2 * B → (2 : ℤ) ^ (m + 1) ∣ B := by
    intro B h
    rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) by rw [pow_succ]; ring] at h
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h
  have hdvd1 : ∀ B : ℤ, (2 : ℤ) ^ (m + 1) ∣ 2 * B → (2 : ℤ) ^ m ∣ B := by
    intro B h
    rw [show (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ]; ring] at h
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h
  have hA : (2 : ℤ) ^ (m + 1) ∣ 2 * x 0 - x 2 := hdvd _ hsq
  have hx2 : (2 : ℤ) ∣ x 2 := by
    have h1 : (2 : ℤ) ∣ 2 * x 0 - x 2 :=
      dvd_trans (dvd_pow_self 2 (by omega : m + 1 ≠ 0)) hA
    have h2 : (2 : ℤ) ∣ 2 * x 0 := dvd_mul_right _ _
    have h3 := dvd_sub h2 h1
    simpa using h3
  obtain ⟨b, hb⟩ := even_iff_two_dvd.mpr hx2
  set q : ℤ → G := fun a => dD.ofTorus (Torus.ofInt _ ![0, a - b, b]) with hq
  have hqD : ∀ a, q a ∈ D := fun a => dD.ofTorus_mem _
  have hqd : ∀ a, (q a)⁻¹ * dD.ofTorus (Torus.ofInt _ x) * q a =
      dD.ofTorus (Torus.ofInt _ x) := by
    intro a
    have hc : q a * dD.ofTorus (Torus.ofInt _ x) =
        dD.ofTorus (Torus.ofInt _ x) * q a := by
      simp only [hq]
      exact dD.ofTorus_comm _ _
    calc (q a)⁻¹ * dD.ofTorus (Torus.ofInt _ x) * q a
        = (q a)⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * q a) := by rw [mul_assoc]
      _ = (q a)⁻¹ * (q a * dD.ofTorus (Torus.ofInt _ x)) := by rw [← hc]
      _ = dD.ofTorus (Torus.ofInt _ x) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hqt : ∀ a, (q a)⁻¹ * dD.t * q a =
      dD.ofTorus (Torus.ofInt _ ![-b, -2 * a, -2 * b]) * dD.t := by
    intro a
    simp only [hq]
    rw [mul_assoc, dD.t_mul_ofTorus, t200_φt, ← mul_assoc, ← dD.ofTorus_neg,
      ← Torus.ofInt_neg, ← dD.ofTorus_add, ← Torus.ofInt_add, mul_right_cancel_iff,
      dD.ofTorus_inj.eq_iff, Torus.ofInt_eq_ofInt_iff]
    intro i
    fin_cases i <;> rw [Int.modEq_iff_dvd] <;>
      simp [t200_k, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc] <;>
      (convert dvd_zero _ using 1; ring)
  have hconj : ∀ a, (q a)⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * dD.t) * q a =
      dD.ofTorus (Torus.ofInt _ ![x 0 - b, x 1 - 2 * a, x 2 - 2 * b]) * dD.t := by
    intro a
    calc (q a)⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * dD.t) * q a
        = ((q a)⁻¹ * dD.ofTorus (Torus.ofInt _ x) * q a) *
            ((q a)⁻¹ * dD.t * q a) := by group
      _ = dD.ofTorus (Torus.ofInt _ x) *
          (dD.ofTorus (Torus.ofInt _ ![-b, -2 * a, -2 * b]) * dD.t) := by
            rw [hqd, hqt]
      _ = dD.ofTorus (Torus.ofInt _ ![x 0 - b, x 1 - 2 * a, x 2 - 2 * b]) * dD.t := by
        rw [← mul_assoc, ← dD.ofTorus_add, ← Torus.ofInt_add, mul_right_cancel_iff,
          dD.ofTorus_inj.eq_iff, Torus.ofInt_eq_ofInt_iff]
        intro i
        fin_cases i <;> rw [Int.modEq_iff_dvd] <;>
          simp [sub_eq_add_neg, add_comm]
  rcases Int.even_or_odd (x 1) with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨q a, hqD a, Or.inl ?_⟩
    rw [hy_eq, hconj a, ha, hb]
    have hdiv : (2 : ℤ) ^ m ∣ x 0 - b := by
      have h := hA
      rw [hb] at h
      exact hdvd1 (x 0 - b) (by convert h using 1; ring)
    rw [show dD.ofTorus (Torus.ofInt _ ![x 0 - b, a + a - 2 * a, b + b - 2 * b]) = 1 by
      rw [dD.ofTorus_eq_one_iff, t200_vec_eq_zero_iff]
      exact ⟨hdiv, ⟨0, by ring⟩, ⟨0, by ring⟩⟩]
    rw [one_mul]
  · refine ⟨q a, hqD a, Or.inr ?_⟩
    rw [hy_eq, hconj a, ha, hb, dD.a_eq, a_eq_ofInt]
    have hdiv : (2 : ℤ) ^ m ∣ x 0 - b := by
      have h := hA
      rw [hb] at h
      exact hdvd1 (x 0 - b) (by convert h using 1; ring)
    rw [show dD.ofTorus (Torus.ofInt _ ![x 0 - b, 2 * a + 1 - 2 * a, b + b - 2 * b]) =
        dD.ofTorus (Torus.ofInt _ ![0, 1, 0]) by
      congr 1
      rw [t200_vec_eq_iff]
      exact ⟨by simpa using dvd_neg.mpr hdiv, ⟨0, by ring⟩, ⟨0, by ring⟩⟩]

theorem t200_conj_of_mem_S₁ (hm : 1 ≤ m) {y : G}
    (hy : y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) (hyD : y ∉ D) (h2 : y * y = 1) :
    ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      q⁻¹ * y * q = dD.u ∨ q⁻¹ * y * q = (dD.c : G) ^ 2 ^ (m - 1) * dD.u ∨
        q⁻¹ * y * q = dD.uv ∨ q⁻¹ * y * q = dD.cab * dD.uv ∨
          q⁻¹ * y * q = dD.t ∨ q⁻¹ * y * q = (dD.a : G) * dD.t := by
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  have hF := Stroth47Core.t200_faithful (m := m) hm
  have hnotfff : ¬ (i = false ∧ j = false ∧ l = false) := by
    rintro ⟨rfl, rfl, rfl⟩
    exact hyD (by simpa [dD.d8_fff] using dD.ofTorus_mem v)
  have huvD : dD.uv ∉ D := by
    have := dD.d8_not_mem hF (i := true) (j := false) (l := false) (by decide) 0
    simpa [dD.d8_tff, dD.ofTorus_zero] using this
  have htS : dD.t ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have huS : dD.u ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hconj_mul (x z : G) : dD.t⁻¹ * (x * z) * dD.t =
      (dD.t⁻¹ * x * dD.t) * (dD.t⁻¹ * z * dD.t) := by group
  have hconj_mul_u (x z : G) : dD.u⁻¹ * (x * z) * dD.u =
      (dD.u⁻¹ * x * dD.u) * (dD.u⁻¹ * z * dD.u) := by group
  have ht_uv : dD.t⁻¹ * dD.uv * dD.t = dD.uv := by
    calc dD.t⁻¹ * dD.uv * dD.t = dD.t⁻¹ * (dD.uv * dD.t) := by rw [mul_assoc]
      _ = dD.t⁻¹ * (dD.t * dD.uv) := by rw [dD.uv_comm_t]
      _ = dD.uv := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have ht_u : dD.t⁻¹ * dD.u * dD.t = dD.u * dD.uv := by
    rw [dD.t_inv, dD.t_u, mul_assoc, dD.t_sq, mul_one]
  have hu_uv : dD.u⁻¹ * dD.uv * dD.u = dD.uv := by
    calc dD.u⁻¹ * dD.uv * dD.u = dD.u⁻¹ * (dD.uv * dD.u) := by rw [mul_assoc]
      _ = dD.u⁻¹ * (dD.u * dD.uv) := by rw [dD.uv_comm_u]
      _ = dD.uv := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hu_t : dD.u⁻¹ * dD.t * dD.u = dD.uv * dD.t := by
    rw [dD.u_inv, mul_assoc, dD.t_u, mul_assoc dD.u dD.uv dD.t,
      ← mul_assoc dD.u dD.u (dD.uv * dD.t), dD.u_sq, one_mul]
  cases i <;> cases j <;> cases l
  · exact absurd ⟨rfl, rfl, rfl⟩ hnotfff
  · have hyu : (dD.ofTorus v * dD.d8 false false true) * dD.u ∈ D := by
      rw [dD.d8_fft, mul_assoc, dD.u_sq, mul_one]
      exact dD.ofTorus_mem v
    obtain ⟨q, hqD, hq | hq⟩ := dD.t200_conj_Du_of_mul_self hm hyu h2
    · exact ⟨q, Subgroup.mem_sup_left hqD, Or.inl hq⟩
    · exact ⟨q, Subgroup.mem_sup_left hqD, Or.inr (Or.inl hq)⟩
  · have hyt : (dD.ofTorus v * dD.d8 false true false) * dD.t ∈ D := by
      rw [dD.d8_ftf, mul_assoc, dD.t_sq, mul_one]
      exact dD.ofTorus_mem v
    obtain ⟨q, hqD, hq | hq⟩ := dD.t200_conj_Dt_of_mul_self hm hyt h2
    · exact ⟨q, Subgroup.mem_sup_left hqD, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq))))⟩
    · exact ⟨q, Subgroup.mem_sup_left hqD,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq))))⟩
  · exfalso
    have hsq := h2
    rw [dD.nf_mul_self, Bool.true_and, dD.d8_tff] at hsq
    apply huvD
    rw [← inv_eq_of_mul_eq_one_right hsq]
    exact D.inv_mem (dD.ofTorus_mem _)
  · have hyuv : (dD.ofTorus v * dD.d8 true false false) * dD.uv ∈ D := by
      rw [dD.d8_tff, mul_assoc, dD.uv_sq, mul_one]
      exact dD.ofTorus_mem v
    obtain ⟨q, hqD, hq | hq⟩ := dD.t200_conj_Duv_of_mul_self hm hyuv h2
    · exact ⟨q, Subgroup.mem_sup_left hqD, Or.inr (Or.inr (Or.inl hq))⟩
    · exact ⟨q, Subgroup.mem_sup_left hqD, Or.inr (Or.inr (Or.inr (Or.inl hq)))⟩
  · have hyu : (dD.t⁻¹ * (dD.ofTorus v * dD.d8 true false true) * dD.t) *
        dD.u ∈ D := by
      rw [dD.d8_tft]
      have hc : (dD.t⁻¹ * (dD.ofTorus v * (dD.uv * dD.u)) * dD.t) * dD.u =
          dD.ofTorus ((StrothTypeIndex.t200 m).action.φt v) := by
        rw [hconj_mul (dD.ofTorus v) (dD.uv * dD.u),
          hconj_mul dD.uv dD.u, dD.conj_ofTorus dD.t_mem dD.t_conj v, ht_uv, ht_u]
        rw [← mul_assoc dD.uv dD.u dD.uv, dD.uv_comm_u, mul_assoc dD.u dD.uv dD.uv,
          dD.uv_sq, mul_one, mul_assoc, dD.u_sq, mul_one]
      rw [hc]
      exact dD.ofTorus_mem _
    have h2' : (dD.t⁻¹ * (dD.ofTorus v * dD.d8 true false true) * dD.t) *
        (dD.t⁻¹ * (dD.ofTorus v * dD.d8 true false true) * dD.t) = 1 := by
      rw [dD.d8_tft] at h2
      rw [dD.d8_tft, ← hconj_mul (dD.ofTorus v * (dD.uv * dD.u))
        (dD.ofTorus v * (dD.uv * dD.u))]
      rw [h2]
      group
    obtain ⟨q, hqD, hq | hq⟩ := dD.t200_conj_Du_of_mul_self hm hyu h2'
    · refine ⟨dD.t * q, ?_, Or.inl ?_⟩
      · exact mul_mem htS (Subgroup.mem_sup_left hqD)
      · rw [mul_inv_rev]
        calc (q⁻¹ * dD.t⁻¹) * (dD.ofTorus v * dD.d8 true false true) *
            (dD.t * q) = q⁻¹ * (dD.t⁻¹ * (dD.ofTorus v *
              dD.d8 true false true) * dD.t) * q := by group
          _ = dD.u := hq
    · refine ⟨dD.t * q, ?_, Or.inr (Or.inl ?_)⟩
      · exact mul_mem htS (Subgroup.mem_sup_left hqD)
      · rw [mul_inv_rev]
        calc (q⁻¹ * dD.t⁻¹) * (dD.ofTorus v * dD.d8 true false true) *
            (dD.t * q) = q⁻¹ * (dD.t⁻¹ * (dD.ofTorus v *
              dD.d8 true false true) * dD.t) * q := by group
          _ = (dD.c : G) ^ 2 ^ (m - 1) * dD.u := hq
  · have hyt : (dD.u⁻¹ * (dD.ofTorus v * dD.d8 true true false) * dD.u) *
        dD.t ∈ D := by
      rw [dD.d8_ttf]
      have hc : (dD.u⁻¹ * (dD.ofTorus v * (dD.uv * dD.t)) * dD.u) * dD.t =
          dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) := by
        rw [hconj_mul_u (dD.ofTorus v) (dD.uv * dD.t),
          hconj_mul_u dD.uv dD.t, dD.conj_ofTorus dD.u_mem dD.u_conj v, hu_uv, hu_t]
        rw [← mul_assoc dD.uv dD.uv dD.t, dD.uv_sq, one_mul, mul_assoc, dD.t_sq, mul_one]
      rw [hc]
      exact dD.ofTorus_mem _
    have h2' : (dD.u⁻¹ * (dD.ofTorus v * dD.d8 true true false) * dD.u) *
        (dD.u⁻¹ * (dD.ofTorus v * dD.d8 true true false) * dD.u) = 1 := by
      rw [dD.d8_ttf] at h2
      rw [dD.d8_ttf, ← hconj_mul_u (dD.ofTorus v * (dD.uv * dD.t))
        (dD.ofTorus v * (dD.uv * dD.t))]
      rw [h2]
      group
    obtain ⟨q, hqD, hq | hq⟩ := dD.t200_conj_Dt_of_mul_self hm hyt h2'
    · refine ⟨dD.u * q, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
      · exact mul_mem huS (Subgroup.mem_sup_left hqD)
      · rw [mul_inv_rev]
        calc (q⁻¹ * dD.u⁻¹) * (dD.ofTorus v * dD.d8 true true false) *
            (dD.u * q) = q⁻¹ * (dD.u⁻¹ * (dD.ofTorus v *
              dD.d8 true true false) * dD.u) * q := by group
          _ = dD.t := hq
    · refine ⟨dD.u * q, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))⟩
      · exact mul_mem huS (Subgroup.mem_sup_left hqD)
      · rw [mul_inv_rev]
        calc (q⁻¹ * dD.u⁻¹) * (dD.ofTorus v * dD.d8 true true false) *
            (dD.u * q) = q⁻¹ * (dD.u⁻¹ * (dD.ofTorus v *
              dD.d8 true true false) * dD.u) * q := by group
          _ = (dD.a : G) * dD.t := hq
  · exfalso
    have hsq := h2
    rw [dD.nf_mul_self, Bool.true_and, dD.d8_tff] at hsq
    apply huvD
    rw [← inv_eq_of_mul_eq_one_right hsq]
    exact D.inv_mem (dD.ofTorus_mem _)

theorem t200_elabE' [Finite G] (hm : 1 ≤ m) :
    (∀ x ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
        dD.cab * dD.uv, (dD.a : G)⁻¹ * dD.t}, x * x = 1) ∧
      Nat.card (Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
        dD.cab * dD.uv, (dD.a : G)⁻¹ * dD.t}) = 16 := by
  set x1 : G := (dD.a : G) ^ 2 ^ (m + 1) with hx1
  set x2 : G := (dD.b : G) ^ 2 ^ (m + 1) with hx2
  set y3 : G := dD.cab * dD.uv with hy3
  set y4 : G := (dD.a : G)⁻¹ * dD.t with hy4
  have hF := Stroth47Core.t200_faithful (m := m) hm
  have hx1D : x1 ∈ D := by
    rw [hx1, t200_a_pow]
    exact dD.ofTorus_mem _
  have hx2D : x2 ∈ D := by
    rw [hx2, t200_b_pow]
    exact dD.ofTorus_mem _
  have h1 : x1 * x1 = 1 := by
    rw [hx1, t200_a_pow, dD.ofTorus_mul_self, Stroth47Core.om200_add_self hm, dD.ofTorus_zero]
  have h2 : x2 * x2 = 1 := by
    rw [hx2, t200_b_pow, dD.ofTorus_mul_self, Stroth47Core.om200_add_self hm, dD.ofTorus_zero]
  have h3 : y3 * y3 = 1 := by
    rw [hy3]
    exact t200_cab_uv_mul_self dD
  have hy4eq : y4 = dD.ofTorus (Torus.ofInt _ ![0, -1, 0]) * dD.d8 false true false := by
    rw [hy4, dD.a_eq, ← dD.ofTorus_neg, a_eq_ofInt, t200_neg_vec, ← dD.d8_ftf]
    congr 1
  have h4 : y4 * y4 = 1 := by
    rw [hy4eq, dD.nf_mul_self, Bool.false_and, dD.d8_fff, mul_one]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φt_vec, t200_add_vec, dD.ofTorus_eq_one_iff,
      t200_ofInt_eq_zero_iff]
    simp
  have h12 : x1 * x2 = x2 * x1 := by
    rw [hx1, hx2, t200_a_pow, t200_b_pow]
    exact dD.ofTorus_comm _ _
  have h13 : x1 * y3 = y3 * x1 := by
    rw [hx1, t200_a_pow, hy3, t200_cab_eq, ← dD.d8_tff]
    refine dD.t200_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [Stroth47Core.t200_φuv_om hm]
    exact (Stroth47Core.om200_eq_iff hm _ _).mpr (by decide)
  have h23 : x2 * y3 = y3 * x2 := by
    rw [hx2, t200_b_pow, hy3, t200_cab_eq, ← dD.d8_tff]
    refine dD.t200_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [Stroth47Core.t200_φuv_om hm]
    exact (Stroth47Core.om200_eq_iff hm _ _).mpr (by decide)
  have h14 : x1 * y4 = y4 * x1 := by
    rw [hx1, t200_a_pow, hy4eq]
    refine dD.t200_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [Stroth47Core.t200_φt_om hm]
    exact (Stroth47Core.om200_eq_iff hm _ _).mpr (by decide)
  have h24 : x2 * y4 = y4 * x2 := by
    rw [hx2, t200_b_pow, hy4eq]
    refine dD.t200_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [Stroth47Core.t200_φt_om hm]
    exact (Stroth47Core.om200_eq_iff hm _ _).mpr (by decide)
  have h34 : y3 * y4 = y4 * y3 := by
    rw [hy3, hy4eq, t200_cab_eq, ← dD.d8_tff, dD.nf_mul_nf, dD.nf_mul_nf]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    congr 1
    rw [t200_φuv_vec, t200_φt_vec, t200_add_vec, t200_add_vec]
    congr 1
  have hx1ne : x1 ≠ 1 := by
    rw [hx1, t200_a_pow, Ne, dD.ofTorus_eq_one_iff, ← Stroth47Core.om200_zero,
      Stroth47Core.om200_eq_iff hm]
    decide
  have hx2ne : x2 ≠ 1 := by
    rw [hx2, t200_b_pow, Ne, dD.ofTorus_eq_one_iff, ← Stroth47Core.om200_zero,
      Stroth47Core.om200_eq_iff hm]
    decide
  have hx12ne : x1 ≠ x2 := by
    intro h
    rw [hx1, hx2, t200_a_pow, t200_b_pow, dD.ofTorus_inj.eq_iff, Stroth47Core.om200_eq_iff hm] at h
    exact absurd (h 1) (by decide)
  have hy3D : y3 ∉ D := by
    rw [hy3, t200_cab_eq, ← dD.d8_tff]
    exact dD.d8_not_mem hF (by decide) _
  have hy4D : y4 ∉ D := by
    rw [hy4eq]
    exact dD.d8_not_mem hF (by decide) _
  have h34D : y3 * y4 ∉ D := by
    rw [hy3, hy4eq, t200_cab_eq, ← dD.d8_tff, dD.nf_mul_nf]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φuv_vec, t200_add_vec]
    change dD.ofTorus (Torus.ofInt _ ![0, 0, -1]) * dD.d8 true true false ∉ D
    exact dD.d8_not_mem hF (by decide) _
  have hmul := Stroth42Core.prod4_mul_prod4 h1 h2 h3 h4 h12 h13 h14 h23 h24 h34
  have hsq : ∀ w, Stroth42Core.prod4 x1 x2 y3 y4 w * Stroth42Core.prod4 x1 x2 y3 y4 w = 1 :=
    fun w => by rw [hmul, Stroth42Core.xor4_self, Stroth42Core.prod4_zero]
  have hind : ∀ w, Stroth42Core.prod4 x1 x2 y3 y4 w = 1 →
      w = ((false, false), (false, false)) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ h
    simp only [Stroth42Core.prod4] at h
    have hPH : Stroth42Core.bpow x1 a * Stroth42Core.bpow x2 b ∈ D := by
      cases a <;> cases b <;> simp [Stroth42Core.bpow, hx1D, hx2D, mul_mem]
    have hQ : Stroth42Core.bpow y3 c * Stroth42Core.bpow y4 d ∈ D := by
      rw [eq_inv_of_mul_eq_one_right h]
      exact D.inv_mem hPH
    have hcd : c = false ∧ d = false := by
      cases c <;> cases d
      · exact ⟨rfl, rfl⟩
      · exact absurd (by simpa [Stroth42Core.bpow] using hQ) hy4D
      · exact absurd (by simpa [Stroth42Core.bpow] using hQ) hy3D
      · exact absurd (by simpa [Stroth42Core.bpow] using hQ) h34D
    obtain ⟨rfl, rfl⟩ := hcd
    have h' : Stroth42Core.bpow x1 a * Stroth42Core.bpow x2 b = 1 := by
      simpa [Stroth42Core.bpow] using h
    have hab : a = false ∧ b = false := by
      cases a <;> cases b
      · exact ⟨rfl, rfl⟩
      · exact absurd (by simpa [Stroth42Core.bpow] using h') hx2ne
      · exact absurd (by simpa [Stroth42Core.bpow] using h') hx1ne
      · have h12eq : x1 * x2 = 1 := by simpa [Stroth42Core.bpow] using h'
        have hx1x2 : x1 = x2 := by
          have := congrArg (fun z => z * x2) h12eq
          simpa [mul_assoc, h2] using this
        exact absurd hx1x2 hx12ne
    obtain ⟨rfl, rfl⟩ := hab
    rfl
  have hinj : Function.Injective (Stroth42Core.prod4 x1 x2 y3 y4) := by
    intro w w' h
    have h1' : Stroth42Core.prod4 x1 x2 y3 y4 (Stroth42Core.xor4 w w') = 1 := by
      rw [← hmul, h, hsq]
    have h2' := hind _ h1'
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := w
    obtain ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ := w'
    simp only [Stroth42Core.xor4, Prod.mk.injEq] at h2'
    obtain ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩ := h2'
    revert ha hb hc hd
    cases a <;> cases a' <;> cases b <;> cases b' <;> cases c <;> cases c' <;> cases d <;>
      cases d' <;> decide
  let E : Subgroup G :=
    { carrier := Set.range (Stroth42Core.prod4 x1 x2 y3 y4)
      mul_mem' := by
        rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
        exact ⟨_, (hmul w w').symm⟩
      one_mem' := ⟨_, Stroth42Core.prod4_zero x1 x2 y3 y4⟩
      inv_mem' := by
        rintro _ ⟨w, rfl⟩
        exact ⟨w, (inv_eq_of_mul_eq_one_right (hsq w)).symm⟩ }
  have hclosure_eq : Subgroup.closure ({x1, x2, y3, y4} : Set G) = E := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact ⟨((true, false), (false, false)), by simp [Stroth42Core.prod4, Stroth42Core.bpow]⟩
      · exact ⟨((false, true), (false, false)), by simp [Stroth42Core.prod4, Stroth42Core.bpow]⟩
      · exact ⟨((false, false), (true, false)), by simp [Stroth42Core.prod4, Stroth42Core.bpow]⟩
      · exact ⟨((false, false), (false, true)), by simp [Stroth42Core.prod4, Stroth42Core.bpow]⟩
    · rintro z ⟨w, rfl⟩
      have hx1c : x1 ∈ Subgroup.closure ({x1, x2, y3, y4} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hx2c : x2 ∈ Subgroup.closure ({x1, x2, y3, y4} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hy3c : y3 ∈ Subgroup.closure ({x1, x2, y3, y4} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hy4c : y4 ∈ Subgroup.closure ({x1, x2, y3, y4} : Set G) :=
        Subgroup.subset_closure (by simp)
      obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := w
      simp only [Stroth42Core.prod4]
      refine mul_mem (mul_mem ?_ ?_) (mul_mem ?_ ?_)
      · cases a <;> simp [Stroth42Core.bpow, hx1c]
      · cases b <;> simp [Stroth42Core.bpow, hx2c]
      · cases c <;> simp [Stroth42Core.bpow, hy3c]
      · cases d <;> simp [Stroth42Core.bpow, hy4c]
  constructor
  · intro x hx
    rw [hclosure_eq] at hx
    rcases hx with ⟨w, rfl⟩
    exact hsq w
  · rw [hclosure_eq]
    change Nat.card (Set.range (Stroth42Core.prod4 x1 x2 y3 y4)) = 16
    rw [Nat.card_range_of_injective hinj]
    simp

end StrothWeakTypeData

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (.t200 m)}

theorem t200_not_isConj_c₁_a₁ (h : F.IsD D dD) (hm : 1 ≤ m)
    (hnc : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) :
    ¬ IsConj ((dD.c : G) ^ 2 ^ (m - 1)) ((dD.a : G) ^ 2 ^ (m + 1)) := by
  have hnc' : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
    obtain ⟨x, hx, hox, y, hy, hoy, hxy⟩ := hnc
    rw [h.omegaIn_one_eq] at hx hy
    exact ⟨x, hx, y, hy, hox, hoy, hxy⟩
  exact h.not_isConj_of_omega hnc' (dD.t200_h3 hm)

theorem t200_isConj_w₀_a₁ (h : F.IsD D dD) :
    IsConj ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) ((dD.a : G) ^ 2 ^ (m + 1)) := by
  have hmem : (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) ∈
      Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv, dD.t} :=
    mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hb1 : (dD.b : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) = 1 :=
    Stroth47Fus.t200_b₁_mul_self dD
  have hab : (dD.a : G) ^ 2 ^ (m + 1) ≠ (dD.b : G) ^ 2 ^ (m + 1) := by
    intro hEq
    rw [dD.t200_a_pow, dD.t200_b_pow, dD.ofTorus_inj.eq_iff,
      Stroth47Core.om200_eq_iff (h.one_le_of_t200) ] at hEq
    exact absurd (hEq 1) (by decide)
  have hw1 : (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) ≠ 1 := by
    intro h1
    apply hab
    calc (dD.a : G) ^ 2 ^ (m + 1)
        = ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) *
            (dD.b : G) ^ 2 ^ (m + 1) := by
          rw [mul_assoc, hb1, mul_one]
      _ = (dD.b : G) ^ 2 ^ (m + 1) := by rw [h1, one_mul]
  exact h.t200_fusion.1 _ hmem hw1

theorem t200_isConj_of_mem_Du (h : F.IsD D dD) (hm : 1 ≤ m) :
    ∀ y ∈ D ⊔ Subgroup.zpowers dD.u, y * y = 1 → y ≠ 1 →
      IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨ IsConj y ((dD.a : G) ^ 2 ^ (m + 1)) := by
  intro y hy hy2 hy1
  obtain ⟨w, hwD, k, rfl⟩ :=
    (Stroth47.mem_sup_zpowers_iff_of_mul_self_mem dD.u_mem (by rw [dD.u_sq]; exact D.one_mem)).mp hy
  cases k
  · simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hy2 hy1 ⊢
    rcases dD.t200_h3 hm w hwD hy2 hy1 with ⟨p, -, hp⟩ | ⟨g, -, hg⟩
    · left
      exact isConj_iff.mpr ⟨p⁻¹, by rw [inv_inv]; exact hp⟩
    · right
      exact isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]; exact hg⟩
  · simp only [Stroth42Core.bpow, ↓reduceIte] at hy2 hy1 ⊢
    have hwu : (w * dD.u) * dD.u ∈ D := by
      rw [mul_assoc, dD.u_sq, mul_one]
      exact hwD
    obtain ⟨q, -, hq | hq⟩ := dD.t200_conj_Du_of_mul_self hm hwu hy2
    · left
      exact (isConj_iff.mpr ⟨q⁻¹, by rw [inv_inv]; exact hq⟩).trans h.t200_fusion.2.1
    · right
      exact (isConj_iff.mpr ⟨q⁻¹, by rw [inv_inv]; exact hq⟩).trans h.t200_fusion.2.2

theorem t200_not_isConj_c₁_mul_of_mem_Du (h : F.IsD D dD) (hm : 1 ≤ m)
    (hnc : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) :
    ∀ l ∈ D ⊔ Subgroup.zpowers dD.u, l * l = 1 → l ≠ 1 → l ≠ (dD.c : G) ^ 2 ^ (m - 1) →
      IsConj l ((dD.c : G) ^ 2 ^ (m - 1)) →
        ¬ IsConj ((dD.c : G) ^ 2 ^ (m - 1) * l) ((dD.c : G) ^ 2 ^ (m - 1)) := by
  intro l hl hl2 hl1 hne hlconj
  set c1 : G := (dD.c : G) ^ 2 ^ (m - 1) with hc1
  have hc1D : c1 ∈ D := by
    rw [hc1]
    exact D.pow_mem dD.c.2 _
  have hc1sq : c1 * c1 = 1 := by
    rw [hc1]
    exact Stroth47Fus.t200_c₁_mul_self dD hm
  have := dD.isMulCommutative
  have hca : ¬ IsConj c1 ((dD.a : G) ^ 2 ^ (m + 1)) := by
    rw [hc1]
    exact t200_not_isConj_c₁_a₁ h hm hnc
  have hmemE : ∀ δ1 δ2 : ℤ, (δ1 = 0 ∨ δ1 = 1) → (δ2 = 0 ∨ δ2 = 1) →
      dD.ofTorus (Stroth47Core.om200 m ![0, δ1, δ2]) ∈
        Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
          dD.uv, dD.t} := by
    intro δ1 δ2 h1 h2
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · rw [show (![0, (0 : ℤ), 0] : Fin 3 → ℤ) = (0 : Fin 3 → ℤ) by
          funext i
          fin_cases i <;> rfl,
        Stroth47Core.om200_zero, dD.ofTorus_zero]
      exact one_mem _
    · rw [show (![0, (0 : ℤ), 1] : Fin 3 → ℤ) = ![0, 0, 1] by rfl, dD.t200_b_pow]
      exact Subgroup.subset_closure (by simp)
    · rw [show (![0, (1 : ℤ), 0] : Fin 3 → ℤ) = ![0, 1, 0] by rfl, dD.t200_a_pow]
      exact Subgroup.subset_closure (by simp)
    · rw [show (![0, (1 : ℤ), 1] : Fin 3 → ℤ) = ![0, 1, 1] by rfl]
      have hsum : Stroth47Core.om200 m ![0, 1, 1] =
          Stroth47Core.om200 m ![0, 1, 0] + Stroth47Core.om200 m ![0, 0, 1] := by
        rw [Stroth47Core.om200_apply, Stroth47Core.om200_apply, Stroth47Core.om200_apply,
          ← Torus.ofInt_add]
        congr 1
        funext i
        fin_cases i <;> simp
      rw [hsum, dD.ofTorus_add, dD.t200_a_pow, dD.t200_b_pow]
      exact mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  obtain ⟨w, hwD, k, rfl⟩ :=
    (Stroth47.mem_sup_zpowers_iff_of_mul_self_mem dD.u_mem
      (by rw [dD.u_sq]; exact D.one_mem)).mp hl
  cases k
  · simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hl2 hl1 hne hlconj ⊢
    obtain ⟨ε, hε, hεl⟩ := dD.t200_eq_om_of_mul_self hm hwD hl2
    rcases hε 0 with e0 | e0
    · exfalso
      have hεvec : ε = ![0, ε 1, ε 2] := by
        funext i
        fin_cases i <;> simp [e0]
      have hmem : dD.ofTorus (Stroth47Core.om200 m ε) ∈
          Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
            dD.uv, dD.t} := by
        rw [hεvec]
        exact hmemE (ε 1) (ε 2) (hε 1) (hε 2)
      have hne1 : dD.ofTorus (Stroth47Core.om200 m ε) ≠ 1 := by
        rw [← hεl]
        exact hl1
      have ha1 := h.t200_fusion.1 _ hmem hne1
      rw [hεl] at hlconj
      exact hca (hlconj.symm.trans ha1)
    · have hεvec : ε = ![1, ε 1, ε 2] := by
        funext i
        fin_cases i <;> simp [e0]
      have hc1l : c1 * w = dD.ofTorus (Stroth47Core.om200 m ![0, ε 1, ε 2]) := by
        rw [hc1, dD.t200_c_pow, hεl, hεvec, ← dD.ofTorus_add, Stroth47Core.om200_add]
        congr 1
        rw [Stroth47Core.om200_eq_iff hm]
        intro i
        fin_cases i <;> simp
      have hmem : c1 * w ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1),
          (dD.b : G) ^ 2 ^ (m + 1), dD.uv, dD.t} := by
        rw [hc1l]
        exact hmemE (ε 1) (ε 2) (hε 1) (hε 2)
      have hne1 : c1 * w ≠ 1 := by
        intro h1
        apply hne
        calc w = c1 * (c1 * w) := by rw [← mul_assoc, hc1sq, one_mul]
          _ = c1 := by rw [h1, mul_one]
      have ha1 := h.t200_fusion.1 _ hmem hne1
      intro hconj
      exact hca (hconj.symm.trans ha1)
  · simp only [Stroth42Core.bpow, ↓reduceIte] at hl2 hl1 hne hlconj ⊢
    have hwu : (w * dD.u) * dD.u ∈ D := by
      rw [mul_assoc, dD.u_sq, mul_one]
      exact hwD
    obtain ⟨q, hqD, hq | hq⟩ := dD.t200_conj_Du_of_mul_self hm hwu hl2
    · have hcomm : q⁻¹ * c1 = c1 * q⁻¹ :=
        Subgroup.mul_comm_of_mem_isMulCommutative D (D.inv_mem hqD) hc1D
      have hc1l : IsConj (c1 * (w * dD.u)) (c1 * dD.u) := by
        refine isConj_iff.mpr ⟨q⁻¹, ?_⟩
        rw [inv_inv]
        calc q⁻¹ * (c1 * (w * dD.u)) * q = c1 * (q⁻¹ * (w * dD.u) * q) := by
              rw [← mul_assoc (q⁻¹) c1 (w * dD.u), hcomm]
              group
          _ = c1 * dD.u := by rw [hq]
      have ha1 : IsConj (c1 * (w * dD.u)) ((dD.a : G) ^ 2 ^ (m + 1)) :=
        hc1l.trans h.t200_fusion.2.2
      intro hconj
      exact hca (hconj.symm.trans ha1)
    · have hl_c1u : IsConj (w * dD.u) (c1 * dD.u) :=
        isConj_iff.mpr ⟨q⁻¹, by rw [inv_inv]; exact hq⟩
      have hla1 : IsConj (w * dD.u) ((dD.a : G) ^ 2 ^ (m + 1)) :=
        hl_c1u.trans h.t200_fusion.2.2
      exfalso
      exact hca (hlconj.symm.trans hla1)

theorem t200_isConj_of_mem_S₁ (h : F.IsD D dD) (hm : 1 ≤ m) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}, y * y = 1 → y ≠ 1 →
      IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨ IsConj y ((dD.a : G) ^ 2 ^ (m + 1)) ∨
        IsConj y (dD.cab * dD.uv) := by
  intro y hy hy2 hy1
  by_cases hyD : y ∈ D
  · rcases dD.t200_h3 hm y hyD hy2 hy1 with ⟨p, -, hp⟩ | ⟨g, -, hg⟩
    · left
      exact isConj_iff.mpr ⟨p⁻¹, by rw [inv_inv]; exact hp⟩
    · right
      left
      exact isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]; exact hg⟩
  · have hF := Stroth47Core.t200_faithful (m := m) hm
    have huv1 : dD.uv ≠ 1 := by
      intro h1
      have hmem : dD.uv ∈ D := by rw [h1]; exact one_mem _
      exact (dD.d8_not_mem hF (i := true) (j := false) (l := false) (by decide) 0)
        (by simpa [dD.d8_tff, dD.ofTorus_zero] using hmem)
    have ht1 : dD.t ≠ 1 := by
      intro h1
      have hmem : dD.t ∈ D := by rw [h1]; exact one_mem _
      exact (dD.d8_not_mem hF (i := false) (j := true) (l := false) (by decide) 0)
        (by simpa [dD.d8_ftf, dD.ofTorus_zero] using hmem)
    have huv_a1 : IsConj dD.uv ((dD.a : G) ^ 2 ^ (m + 1)) :=
      h.t200_fusion.1 _ (Subgroup.subset_closure (by simp)) huv1
    have ht_a1 : IsConj dD.t ((dD.a : G) ^ 2 ^ (m + 1)) :=
      h.t200_fusion.1 _ (Subgroup.subset_closure (by simp)) ht1
    obtain ⟨q, -, hq | hq | hq | hq | hq | hq⟩ :=
      dD.t200_conj_of_mem_S₁ hm hy hyD hy2
    · left
      exact (isConj_iff.mpr ⟨q⁻¹, by rw [inv_inv]; exact hq⟩).trans h.t200_fusion.2.1
    · right
      left
      exact (isConj_iff.mpr ⟨q⁻¹, by rw [inv_inv]; exact hq⟩).trans h.t200_fusion.2.2
    · right
      left
      exact (isConj_iff.mpr ⟨q⁻¹, by rw [inv_inv]; exact hq⟩).trans huv_a1
    · right
      right
      exact isConj_iff.mpr ⟨q⁻¹, by rw [inv_inv]; exact hq⟩
    · right
      left
      exact (isConj_iff.mpr ⟨q⁻¹, by rw [inv_inv]; exact hq⟩).trans ht_a1
    · right
      right
      exact (isConj_iff.mpr ⟨q⁻¹, by rw [inv_inv]; exact hq⟩).trans
        (StrothWeakTypeData.t200_isConj_a_t dD)

end StrothFrame.IsD

end CFSG.CGT.Stroth77
