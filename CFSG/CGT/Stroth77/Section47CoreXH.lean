module

public import CFSG.CGT.Stroth77.Section47CoreX

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 StrothWeakTypeData

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t200 m)) {f : G} {p : ℕ}

theorem pow_four_eq (y : G) : y ^ 4 = y * y * (y * y) := by rw [← sq, ← sq, ← pow_mul]

theorem t200x_pow_eq (hm : 2 ≤ m) (hp : p % 2 = 1)
    (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) :
    f ^ 2 ^ (m + 1) = (dD.c : G) ^ 2 ^ (m - 1) := by
  have h4 : f ^ 4 = dD.ofTorus (Torus.ofInt _ ![2 ^ (m - 1) - (p : ℤ), 0, 0]) := by
    rw [pow_four_eq, dD.t200x_e_mul_self hrel]
  rw [show 2 ^ (m + 1) = 4 * 2 ^ (m - 1) by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega,
    pow_mul, h4, ← dD.ofTorus_nsmul, dD.t200_c_pow]
  congr 1
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, p = 2 * r + 1 := ⟨p / 2, by omega⟩
  rw [← natCast_zsmul, t200_zsmul_vec, om200_apply, t200_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, show m' + 2 - 1 = m' + 1 by omega]
  push_cast
  refine ⟨⟨1 + r - 2 ^ m', by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem t200x_h4 (hm : 1 ≤ m) (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f),
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y ^ 2 ^ (m + 1) ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  intro y hy hcomm hpow
  have hyy : y * y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * (y * y) := by
    rw [mul_assoc, hcomm, ← mul_assoc, hcomm, mul_assoc]
  rcases (dD.t200xEAction hrel).mul_self_mem_or y hy with h2 | h2
  · obtain ⟨v, hv⟩ := dD.exists_ofTorus h2
    rw [pow_two_pow_eq_mul_self _ (by omega : 1 ≤ m + 1), Nat.add_sub_cancel, hv,
      ← dD.ofTorus_nsmul, dD.t200_c_pow] at hpow
    have h := dD.ofTorus_inj hpow
    obtain ⟨x0, x1, x2, rfl⟩ := t200_exists_vec v
    rw [← natCast_zsmul, t200_zsmul_vec, om200_apply, t200_ofInt_eq_iff] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h
    obtain ⟨⟨k, hk⟩, -, -⟩ := h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hk
    push_cast at hk
    have h2 : (2 : ℤ) ^ m' * 1 = 2 ^ m' * (2 * (x0 + k)) := by linear_combination hk
    have h3 := mul_left_cancel₀ (pow_ne_zero m' (two_ne_zero : (2 : ℤ) ≠ 0)) h2
    omega
  · obtain ⟨v, hv⟩ := dD.exists_ofTorus h2
    have hyy' : y * y = dD.ofTorus v * dD.d8 true false false := by
      rw [d8_tff, ← hv, mul_assoc, dD.uv_sq, mul_one]
    rw [hyy'] at hyy
    obtain ⟨h1, -⟩ := dD.t200_comm_z hm hyy
    exact Bool.noConfusion h1

theorem t200x_h5 (hfN : f ∈ Subgroup.normalizer (D : Set G))
    (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f) ⊔
        Subgroup.zpowers f, y ^ 4 ∈ D := by
  intro y hy
  rw [pow_four_eq]
  by_cases hyU : y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f)
  · rcases (dD.t200xEAction hrel).mul_self_mem_or y hyU with h2 | h2
    · exact D.mul_mem h2 h2
    · obtain ⟨v, hv⟩ := dD.exists_ofTorus h2
      have hyy' : y * y = dD.ofTorus v * dD.d8 true false false := by
        rw [d8_tff, ← hv, mul_assoc, dD.uv_sq, mul_one]
      rw [hyy', nf_mul_self, Bool.and_false, d8_fff, mul_one]
      exact dD.ofTorus_mem _
  · obtain ⟨v, i, hv⟩ := dD.t200x_mul_self_of_not_mem hfN hrel y hy hyU
    rw [hv, (dD.t200xEAction hrel).nfe_e_mul_self, Bool.and_false, d8_fff, mul_one]
    exact dD.ofTorus_mem _

theorem t200x_sqE_ne_zero (hm : 2 ≤ m) (hp : p % 2 = 1)
    (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) (x0 x1 x2 : ℤ) (i : Bool) :
    (dD.t200xEAction hrel).sqE (Torus.ofInt _ ![x0, x1, x2]) i false false ≠ 0 := by
  intro h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, p = 2 * r + 1 := ⟨p / 2, by omega⟩
  simp only [EAction.sqE, EAction.twist, t200xEAction_ve, t200xEAction_wuv,
    t200xEAction_wt, show m' + 2 - 1 = m' + 1 by omega] at h
  cases i <;>
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, Bool.and_false, map_add, map_sub, map_zero, t200xEAction_φe_apply,
    t200_φuv, ← Torus.ofInt_add, ← Torus.ofInt_sub, add_zero, zero_add, t200_ofInt_eq_zero_iff,
    Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h <;>
  obtain ⟨⟨k0, hk0⟩, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h <;>
  push_cast at hk0 hk1 hk2
  ·
    have : (2 : ℤ) * (x0 + 2 ^ m' - r - 2 * 2 ^ m' * k0) = 1 := by linear_combination hk0
    omega
  ·
    have h' : (8 * 2 ^ m' : ℤ) * ((2 * 2 ^ m' + 1) * (x2 - x1)) =
        (8 * 2 ^ m') * (2 * (k1 - k2)) := by linear_combination hk1 - hk2
    have h'' := mul_left_cancel₀ (by positivity : (8 * 2 ^ m' : ℤ) ≠ 0) h'
    have hd : x2 - x1 = 2 * ((k1 - k2) - 2 ^ m' * (x2 - x1)) := by linear_combination h''
    have key : 2 * (16 * x1 * 2 ^ m' * 2 ^ m' + 128 * 2 ^ m' * 2 ^ m' * 2 ^ m' -
        128 * 2 ^ m' * 2 ^ m' * r + 16 * 2 ^ m' * 2 ^ m' * ((k1 - k2) - 2 ^ m' * (x2 - x1)) +
        8 * x1 * 2 ^ m' - 56 * 2 ^ m' * r - 2 * 2 ^ m' * k0 +
        8 * 2 ^ m' * ((k1 - k2) - 2 ^ m' * (x2 - x1)) - x0 + x1 - 31 * 2 ^ m' + r +
        ((k1 - k2) - 2 ^ m' * (x2 - x1))) + 1 = (0 : ℤ) := by
      linear_combination hk0 - (16 * 2 ^ m' * 2 ^ m' + 8 * 2 ^ m' + 1) * hd
    omega

theorem t200x_h6 (hm : 2 ≤ m) (hp : p % 2 = 1) (hfN : f ∈ Subgroup.normalizer (D : Set G))
    (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f) ⊔
        Subgroup.zpowers f,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f) → y ^ 4 ≠ 1 := by
  intro y hy hyU h1
  obtain ⟨v, i, hv⟩ := dD.t200x_mul_self_of_not_mem hfN hrel y hy hyU
  rw [pow_four_eq, hv, (dD.t200xEAction hrel).nfe_e_mul_self, Bool.and_false, d8_fff, mul_one,
    dD.ofTorus_eq_one_iff] at h1
  obtain ⟨x0, x1, x2, rfl⟩ := t200_exists_vec v
  exact t200x_sqE_ne_zero dD hm hp hrel x0 x1 x2 i h1

theorem t200x_h8 (hm : 2 ≤ m) (hp : p % 2 = 1) (hfN : f ∈ Subgroup.normalizer (D : Set G))
    (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f) ⊔
        Subgroup.zpowers f,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f) →
      ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = (dD.c : G) ^ 2 ^ (m - 1) → y ^ 2 ^ (m + 1) ≠ 1 := by
  intro y hy hyU l _ hyl
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  have hcomm : y * z = z * y := by rw [← hyl]; exact ((Commute.refl y).pow_right _).eq
  obtain ⟨v, i, hv⟩ := dD.t200x_mul_self_of_not_mem hfN hrel y hy hyU
  have hfc : Commute f (dD.c : G) := by
    have h := hrel.1.c_conj
    show f * (dD.c : G) = (dD.c : G) * f
    calc f * (dD.c : G) = f * (f⁻¹ * (dD.c : G) * f) := by rw [h]
      _ = (dD.c : G) * f := by group
  have hec : Commute (f * f) z := (hfc.pow_right _).mul_left (hfc.pow_right _)
  have hyy : y * y * z = z * (y * y) := by rw [mul_assoc, hcomm, ← mul_assoc, hcomm, mul_assoc]
  rw [hv] at hyy
  have hX : dD.ofTorus v * dD.d8 i false false * z = z * (dD.ofTorus v * dD.d8 i false false) := by
    have h1 : dD.ofTorus v * dD.d8 i false false * z * (f * f) =
        z * (dD.ofTorus v * dD.d8 i false false) * (f * f) := by
      rw [mul_assoc, ← hec.eq, ← mul_assoc, hyy]
      simp only [mul_assoc]
    exact mul_right_cancel h1
  obtain ⟨rfl, -⟩ := dD.t200_comm_z (by omega) hX
  have h4 : y ^ 4 = dD.ofTorus ((dD.t200xEAction hrel).sqE v false false false) := by
    rw [pow_four_eq, hv, (dD.t200xEAction hrel).nfe_e_mul_self, Bool.and_false, d8_fff, mul_one]
  rw [show 2 ^ (m + 1) = 4 * 2 ^ (m - 1) by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega,
    pow_mul, h4, ← dD.ofTorus_nsmul, Ne, dD.ofTorus_eq_one_iff]
  obtain ⟨x0, x1, x2, rfl⟩ := t200_exists_vec v
  intro h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, p = 2 * r + 1 := ⟨p / 2, by omega⟩
  simp only [EAction.sqE, EAction.twist, t200xEAction_ve, t200xEAction_wuv,
    t200xEAction_wt, show m' + 2 - 1 = m' + 1 by omega, SigmaFourAction.d8Act,
    Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
    Bool.and_false, map_add, map_sub, map_zero, t200xEAction_φe_apply, ← Torus.ofInt_add,
    ← Torus.ofInt_sub, add_zero, zero_add, ← natCast_zsmul, ← Torus.ofInt_zsmul,
    t200_ofInt_eq_zero_iff, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h
  obtain ⟨⟨k, hk⟩, -, -⟩ := h
  push_cast at hk
  have h2 : (2 : ℤ) ^ (m' + 1) * (2 * x0 + 2 * 2 ^ m' - 2 * r - 1) = 2 ^ (m' + 1) * (2 * k) := by
    linear_combination hk
  have h3 := mul_left_cancel₀ (pow_ne_zero (m' + 1) (two_ne_zero : (2 : ℤ) ≠ 0)) h2
  omega

end Stroth47Core

end CFSG.CGT.Stroth77
