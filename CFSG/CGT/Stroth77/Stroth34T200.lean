module

public import CFSG.CGT.Stroth77.Stroth34T200Normal
public import CFSG.CGT.Stroth77.Stroth34Defs

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)
open Stroth34T200

namespace Stroth34T200

theorem y_cases {m : ℕ} {y : ℤ} (h : (2 : ℤ) ^ (m + 2) ∣ y * y - 1) :
    (2 : ℤ) ^ (m + 2) ∣ y - 1 ∨ (2 : ℤ) ^ (m + 2) ∣ y + 1 ∨
      (2 : ℤ) ^ (m + 2) ∣ y - (1 + 2 ^ (m + 1)) ∨ (2 : ℤ) ^ (m + 2) ∣ y - (-1 + 2 ^ (m + 1)) :=
  Stroth34Arith.sq_cases' (by rwa [sq])

theorem four_dvd_two_pow {m : ℕ} (hm : 2 ≤ m) : (4 : ℤ) ∣ 2 ^ m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  exact ⟨2 ^ j, by ring⟩

theorem y_cases_three {m : ℕ} (hm : 1 ≤ m) {y : ℤ} (hy4 : y % 4 = 3)
    (h : (2 : ℤ) ^ (m + 2) ∣ y * y - 1) :
    (2 : ℤ) ^ (m + 2) ∣ y + 1 ∨ (2 : ℤ) ^ (m + 2) ∣ y - (-1 + 2 ^ (m + 1)) := by
  have h4 := four_dvd_two_pow (m := m + 2) (by omega)
  obtain ⟨c, hc⟩ := four_dvd_two_pow (m := m + 1) (by omega)
  rcases y_cases h with h1 | h1 | h1 | h1
  · have := dvd_trans h4 h1; omega
  · exact Or.inl h1
  · have := dvd_trans h4 h1; rw [hc] at this; omega
  · exact Or.inr h1

theorem dvd_sq_negN_two {m : ℕ} {y : ℤ} (hy : (2 : ℤ) ^ (m + 2) ∣ y - (-1 + 2 ^ (m + 1))) :
    (2 : ℤ) ^ (m + 2) ∣ (y + 1) * 2 := by
  obtain ⟨k, hk⟩ := hy
  exact ⟨1 + 2 * k, by linear_combination 2 * hk⟩

theorem dvd_sq_negN_odd {m : ℕ} (hm : 1 ≤ m) {y q : ℤ} (hq : q = 1 ∨ q = 3)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - (-1 + 2 ^ (m + 1))) :
    (2 : ℤ) ^ (m + 2) ∣ (y + 1) * q + 4 * 2 ^ (m - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k, hk⟩ := hy
  rw [Nat.add_sub_cancel]
  rcases hq with rfl | rfl
  · exact ⟨1 + k, by linear_combination hk⟩
  · exact ⟨2 + 3 * k, by linear_combination 3 * hk⟩

theorem cyc_f4 {m : ℕ} (hm : 2 ≤ m) {y p : ℤ} (hp : p = 1 ∨ p = 3)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - (1 + 2 ^ m)) :
    (2 : ℤ) ^ (m + 2) ∣ y * y * (y * p + p) + (y * p + p) + 4 * (-p + 2 ^ (m - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  obtain ⟨k, hk⟩ := hy
  have hy' : y = 1 + 2 ^ (j + 2) + 2 ^ (j + 2 + 2) * k := by linear_combination hk
  subst hy'
  rw [show j + 2 - 1 = j + 1 by omega]
  rcases hp with rfl | rfl
  · exact ⟨2 + 4 * 2 ^ j + 32 * 2 ^ j * k + 64 * 2 ^ j * k ^ 2 + 4 * (2 ^ j) ^ 2 +
      48 * (2 ^ j) ^ 2 * k + 192 * (2 ^ j) ^ 2 * k ^ 2 + 256 * (2 ^ j) ^ 2 * k ^ 3 + 6 * k,
      by ring⟩
  · exact ⟨5 + 12 * 2 ^ j + 96 * 2 ^ j * k + 192 * 2 ^ j * k ^ 2 + 12 * (2 ^ j) ^ 2 +
      144 * (2 ^ j) ^ 2 * k + 576 * (2 ^ j) ^ 2 * k ^ 2 + 768 * (2 ^ j) ^ 2 * k ^ 3 + 18 * k,
      by ring⟩

theorem cyc_cube {m : ℕ} (hm : 2 ≤ m) {y : ℤ} (hy : (2 : ℤ) ^ (m + 2) ∣ y - (1 + 3 * 2 ^ m)) :
    (2 : ℤ) ^ (m + 2) ∣ y * y * y - (1 + 2 ^ m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  obtain ⟨k, hk⟩ := hy
  have hy' : y = 1 + 3 * 2 ^ (j + 2) + 2 ^ (j + 2 + 2) * k := by linear_combination hk
  subst hy'
  exact ⟨2 + 27 * 2 ^ j + 72 * 2 ^ j * k + 48 * 2 ^ j * k ^ 2 + 108 * (2 ^ j) ^ 2 +
    432 * (2 ^ j) ^ 2 * k + 576 * (2 ^ j) ^ 2 * k ^ 2 + 256 * (2 ^ j) ^ 2 * k ^ 3 + 3 * k, by ring⟩

theorem cube_class {y p : ℤ} (hy : (4 : ℤ) ∣ y - 1) :
    (4 : ℤ) ∣ y * (y * p + p) + p - (4 - p) := by
  obtain ⟨c, hc⟩ := hy
  exact ⟨p * c * (y + 2) + p - 1, by linear_combination (p * (y + 2)) * hc⟩

theorem klein_y {m : ℕ} {y₁ y₃ : ℤ} (h₁ : (2 : ℤ) ^ (m + 2) ∣ y₁ + 1)
    (h₃ : (2 : ℤ) ^ (m + 2) ∣ y₃ - (-1 + 2 ^ (m + 1))) :
    (2 : ℤ) ^ (m + 2) ∣ y₁ * y₃ - (1 + 2 ^ (m + 1)) := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₃
  exact ⟨-1 - a - b + 2 * 2 ^ m * a + 4 * 2 ^ m * a * b,
    by linear_combination y₃ * ha + (-1 + 2 ^ (m + 2) * a) * hb⟩

theorem klein_y' {m : ℕ} {y₁ y₃ : ℤ} (h₁ : (2 : ℤ) ^ (m + 2) ∣ y₁ - (-1 + 2 ^ (m + 1)))
    (h₃ : (2 : ℤ) ^ (m + 2) ∣ y₃ + 1) :
    (2 : ℤ) ^ (m + 2) ∣ y₁ * y₃ - (1 + 2 ^ (m + 1)) := by
  have := klein_y h₃ h₁
  rwa [mul_comm y₃ y₁] at this

theorem klein_rel {m : ℕ} (hm : 1 ≤ m) {ye yf q : ℤ} (hq : q = 1 ∨ q = 3)
    (he : (2 : ℤ) ^ (m + 2) ∣ ye - (1 + 2 ^ (m + 1))) (hf : (2 : ℤ) ^ (m + 2) ∣ yf + 1) :
    (2 : ℤ) ^ (m + 2) ∣ yf * 2 + q - (ye * q + 2 - 4 * (1 + 2 ^ (m - 1))) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := he
  rw [Nat.add_sub_cancel]
  rcases hq with rfl | rfl
  · exact ⟨2 * a - b, by linear_combination 2 * ha - hb⟩
  · exact ⟨-1 + 2 * a - 3 * b, by linear_combination 2 * ha - 3 * hb⟩

end Stroth34T200

namespace Normal200

open StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t200 m)} {hS : Local.Setting (F.S : Subgroup G) D}

theorem odd {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) : y % 2 = 1 := by
  by_contra hy
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ y := Int.dvd_of_emod_eq_zero (by omega)
  have heN := hS.R_le_normalizer hn.mem.1
  have h1 := hn.scalar ((2 ^ (m + 1) : ℤ) • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 1, 0])
  have h2 : (y * 2 ^ (m + 1)) • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 1, 0] = 0 := by
    rw [hk, t200_zsmul_vec, t200_vec_eq_zero_iff]
    exact ⟨⟨0, by ring⟩, ⟨k, by ring⟩, ⟨0, by ring⟩⟩
  rw [smul_smul, h2] at h1
  have h3 := congrArg (dD.thetaT (inv_mem heN)) h1
  rw [dD.thetaT_inv_thetaT, map_zero, t200_zsmul_vec, t200_vec_eq_zero_iff] at h3
  exact not_two_pow_succ_dvd_mul_odd (m + 1) (z := 1) (by norm_num) h3.2.1

theorem renorm {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) {p' : ℤ} (h : (4 : ℤ) ∣ p - p') :
    ∃ d ∈ D, Normal200 hS dD (e * d) y p' := by
  obtain ⟨μ, hμ⟩ := h
  refine ⟨_, dD.ofT_mem (μ • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]), ?_⟩
  have := hn.mul_c μ
  rwa [show p - 4 * μ = p' by linear_combination hμ] at this

theorem cls_of {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) {q : ℤ} (hq : (4 : ℤ) ∣ p - q) :
    ∃ e' : G, ∃ y' : ℤ, Normal200 hS dD e' y' q := by
  obtain ⟨d, -, hd⟩ := hn.renorm hq
  exact ⟨_, _, hd⟩

theorem c_conj_one {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) (hy : (2 : ℤ) ^ m ∣ y - 1) :
    e⁻¹ * (dD.c : G) * e = dD.c := by
  rw [hn.c_conj_eq hy, one_zsmul, ← dD.t200_c_eq]

theorem c_conj_neg {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) (hy : (2 : ℤ) ^ m ∣ y + 1) :
    e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ := by
  rw [hn.c_conj_eq (l := -1) (by rwa [sub_neg_eq_add]), dD.t200_c_inv_eq]

theorem a_conj_mul {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) (j : ℕ)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - (1 + j)) :
    e⁻¹ * (dD.a : G) * e = (dD.a : G) * (dD.a : G) ^ j := by
  rw [hn.a_conj_eq hy, dD.t200_a_mul_pow_eq]

theorem a_conj_inv_mul {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) (j : ℕ)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - (-1 + j)) :
    e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ j := by
  rw [hn.a_conj_eq hy, dD.t200_a_inv_mul_pow_eq]

theorem b_conj_mul {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) (j : ℕ)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - (1 + j)) :
    e⁻¹ * (dD.b : G) * e = (dD.b : G) * (dD.b : G) ^ j := by
  rw [hn.b_conj_eq hy, dD.t200_b_mul_pow_eq]

theorem b_conj_inv_mul {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p) (j : ℕ)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - (-1 + j)) :
    e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ j := by
  rw [hn.b_conj_eq hy, dD.t200_b_inv_mul_pow_eq]

theorem sq_eq_one (h : F.IsD D dD) {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p)
    (hμ : (2 : ℤ) ^ (m + 2) ∣ (y + 1) * p) : e * e = 1 := by
  rw [hn.sq_eq h (μ := 0) (by simpa using hμ), zero_zsmul, dD.ofT_zero]

theorem sq_eq_c_pow (h : F.IsD D dD) {e : G} {y p : ℤ} (hn : Normal200 hS dD e y p)
    (hμ : (2 : ℤ) ^ (m + 2) ∣ (y + 1) * p + 4 * 2 ^ (m - 1)) :
    e * e = (dD.c : G) ^ 2 ^ (m - 1) := by
  rw [hn.sq_eq h hμ, dD.t200_c_pow_eq]
  push_cast
  rfl

theorem rel34i (h : F.IsD D dD) {e : G} {y : ℤ} (hn : Normal200 hS dD e y 2)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - (1 + 2 ^ (m + 1))) : Rel34i dD e (2 ^ (m + 1)) := by
  obtain ⟨k, hk⟩ := hy
  have hy' : (2 : ℤ) ^ (m + 2) ∣ y - (1 + ((2 ^ (m + 1) : ℕ) : ℤ)) :=
    ⟨k, by push_cast; exact hk⟩
  have hq : (2 : ℤ) ^ (m + 2) ∣ 2 - ((2 : ℕ) : ℤ) := by norm_num
  refine ⟨hn.c_conj_one ⟨4 * k + 2, by linear_combination hk⟩, hn.a_conj_mul _ hy',
    hn.b_conj_mul _ hy', ?_, hn.uv_conj_eq hq, hn.t_conj_eq hq, hn.u_conj_eq⟩
  rw [hn.sq_eq h (μ := -1) ⟨1 + 2 * k, by linear_combination 2 * hk⟩, dD.t200_c_inv_eq]

theorem rel34inv {e : G} {y p : ℤ} {q : ℕ} (hn : Normal200 hS dD e y p) (hpq : p = q) (j : ℕ)
    (hj : (2 : ℤ) ^ m ∣ j) (hy : (2 : ℤ) ^ (m + 2) ∣ y - (-1 + j)) {s : G} (hs : e * e = s) :
    Rel34inv dD e j s q := by
  have hc : (2 : ℤ) ^ m ∣ y + 1 := by
    have h1 : (2 : ℤ) ^ m ∣ y - (-1 + j) := dvd_trans (pow_dvd_pow 2 (by omega)) hy
    have := dvd_add h1 hj
    rwa [show y - (-1 + (j : ℤ)) + j = y + 1 by ring] at this
  have hq : (2 : ℤ) ^ (m + 2) ∣ p - q := by rw [hpq, sub_self]; exact dvd_zero _
  exact ⟨hn.c_conj_neg hc, hn.a_conj_inv_mul j hy, hn.b_conj_inv_mul j hy, hs,
    hn.uv_conj_eq hq, hn.t_conj_eq hq, hn.u_conj_eq⟩

theorem rel34x {f : G} {y p : ℤ} {q : ℕ} (hn : Normal200 hS dD f y p) (hpq : p = q)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - (1 + 2 ^ m))
    (hf4 : f * f * (f * f) = ((dD.c : G) ^ q)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) :
    Rel34x dD f (2 ^ m) (2 ^ (m - 1)) q := by
  obtain ⟨k, hk⟩ := hy
  have hy' : (2 : ℤ) ^ (m + 2) ∣ y - (1 + ((2 ^ m : ℕ) : ℤ)) := ⟨k, by push_cast; exact hk⟩
  have hq : (2 : ℤ) ^ (m + 2) ∣ p - q := by rw [hpq, sub_self]; exact dvd_zero _
  exact ⟨⟨hn.c_conj_one ⟨4 * k + 1, by linear_combination hk⟩, hn.a_conj_mul _ hy',
    hn.b_conj_mul _ hy', rfl, hn.uv_conj_eq hq, hn.t_conj_eq hq, hn.u_conj_eq⟩, hf4⟩

theorem f4_eq (h : F.IsD D dD) {f : G} {y p : ℤ} {q : ℕ} (hn : Normal200 hS dD f y p)
    (hpq : p = q) (hm : 2 ≤ m) (hp : p = 1 ∨ p = 3) (hy : (2 : ℤ) ^ (m + 2) ∣ y - (1 + 2 ^ m)) :
    f * f * (f * f) = ((dD.c : G) ^ q)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) := by
  rw [((hn.mul hn).mul (hn.mul hn)).eq_ofT h (cyc_f4 hm hp hy), dD.t200_c_pow_inv_mul_pow_eq,
    hpq]
  push_cast
  rfl

end Normal200

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t200 m)}

theorem t200_exists_rep (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {r : G} (hr : r ∈ hS.R) :
    ∃ d ∈ D, ∃ y q : ℤ, Normal200 hS dD (r * d) y q ∧ 0 ≤ q ∧ q < 4 := by
  have hr1 : r ∈ hS.R1 dD.uv dD.t := by rw [h.t200_R1_eq_R hS hm hfus]; exact hr
  obtain ⟨d, hd, y, p, hn⟩ := h.exists_normal200 hS hm hfus hr1
  obtain ⟨d', hd', hn'⟩ := hn.renorm (p' := p % 4) (by omega)
  exact ⟨d * d', mul_mem hd hd', y, p % 4, by rwa [← mul_assoc], by omega, by omega⟩

theorem t200_R_le (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {K : Subgroup G}
    (hDK : D ≤ K)
    (hK : ∀ q : ℤ, (q = 1 ∨ q = 2 ∨ q = 3) → (∃ e : G, ∃ y : ℤ, Normal200 hS dD e y q) →
      ∃ g ∈ K, ∃ y' p' : ℤ, Normal200 hS dD g y' p' ∧ (4 : ℤ) ∣ q - p') :
    hS.R ≤ K := by
  intro r hr
  obtain ⟨d, hd, y, q, hn, hq0, hq4⟩ := h.t200_exists_rep hS hm hfus hr
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with hq | hq
  · subst hq
    have hrd := hn.mem_of_dvd h (dvd_zero 4)
    have : r = r * d * d⁻¹ := by group
    rw [this]
    exact mul_mem (hDK hrd) (hDK (inv_mem hd))
  · obtain ⟨g, hgK, y', p', hg, hqp⟩ := hK q hq ⟨_, _, hn⟩
    have h1 := hn.mul_inv_mem h hg hqp
    have : r = r * d * g⁻¹ * g * d⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem (hDK h1) hgK) (hDK (inv_mem hd))

theorem t200_case_two (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {e : G} {y : ℤ}
    (hn : Normal200 hS dD e y 2) (h1 : ¬ ∃ e : G, ∃ y : ℤ, Normal200 hS dD e y 1)
    (h3 : ¬ ∃ e : G, ∃ y : ℤ, Normal200 hS dD e y 3) :
    e ∈ hS.R ∧ hS.R = D ⊔ Subgroup.zpowers e ∧
      (Rel34i dD e (2 ^ (m + 1)) ∨ Rel34inv dD e 0 1 2 ∨ Rel34inv dD e (2 ^ (m + 1)) 1 2) := by
  have hodd := hn.odd
  have heR := hn.mem.1
  refine ⟨heR, le_antisymm (h.t200_R_le hS hm hfus le_sup_left fun q hq hex => ?_)
    (sup_le hS.D_le_R (Subgroup.zpowers_le.mpr heR)), ?_⟩
  · rcases hq with rfl | rfl | rfl
    · exact absurd hex h1
    · exact ⟨e, Subgroup.mem_sup_right (Subgroup.mem_zpowers e), y, 2, hn, by norm_num⟩
    · exact absurd hex h3
  ·
    have hsq := hn.mul hn
    have hyy := hsq.scalar_dvd_of_mem (hsq.mem_of_dvd h (by omega))
    rcases y_cases hyy with hy | hy | hy | hy
    · exact absurd (hn.dvd_of_mem (hn.mem_of_scalar hy)) (by norm_num)
    · exact Or.inr (Or.inl (hn.rel34inv (by norm_num) 0 (by simp) (by simpa using hy)
        (hn.sq_eq_one h (dvd_mul_of_dvd_left hy _))))
    · exact Or.inl (hn.rel34i h hy)
    · exact Or.inr (Or.inr (hn.rel34inv (by norm_num) _
        (by push_cast; exact pow_dvd_pow 2 (by omega)) (by push_cast; exact hy)
        (hn.sq_eq_one h (dvd_sq_negN_two hy))))

theorem t200_case_odd (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {e : G} {y p : ℤ}
    {q : ℕ} (hpq : p = q) (hp : p = 1 ∨ p = 3) (hn : Normal200 hS dD e y p)
    (h2 : ¬ ∃ e : G, ∃ y : ℤ, Normal200 hS dD e y 2)
    (hp' : ¬ ∃ e : G, ∃ y : ℤ, Normal200 hS dD e y (4 - p)) :
    e ∈ hS.R ∧ hS.R = D ⊔ Subgroup.zpowers e ∧
      (Rel34inv dD e 0 1 q ∨ Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) q) := by
  have hodd := hn.odd
  have heR := hn.mem.1
  refine ⟨heR, le_antisymm (h.t200_R_le hS hm hfus le_sup_left fun q' hq' hex => ?_)
    (sup_le hS.D_le_R (Subgroup.zpowers_le.mpr heR)), ?_⟩
  · have hm' : q' = p ∨ q' = 2 ∨ q' = 4 - p := by omega
    rcases hm' with rfl | rfl | rfl
    · exact ⟨e, Subgroup.mem_sup_right (Subgroup.mem_zpowers e), y, q', hn, by norm_num⟩
    · exact absurd hex h2
    · exact absurd hex hp'
  ·
    have hy4 : y % 4 = 3 := by
      by_contra hne
      exact h2 ((hn.mul hn).cls_of (by rcases hp with rfl | rfl <;> omega))
    have hsq := hn.mul hn
    have hyy := hsq.scalar_dvd_of_mem (hsq.mem_of_dvd h (by rcases hp with rfl | rfl <;> omega))
    rcases y_cases_three hm hy4 hyy with hy | hy
    · exact Or.inl (hn.rel34inv hpq 0 (by simp) (by simpa using hy)
        (hn.sq_eq_one h (dvd_mul_of_dvd_left hy _)))
    · exact Or.inr (hn.rel34inv hpq _ (by push_cast; exact pow_dvd_pow 2 (by omega))
        (by push_cast; exact hy) (hn.sq_eq_c_pow h (dvd_sq_negN_odd hm hp hy)))

theorem t200_case_cyclic_of (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm2 : 2 ≤ m) (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {f : G}
    {y p : ℤ} (hp : p = 1 ∨ p = 3) (hn : Normal200 hS dD f y p)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y - (1 + 2 ^ m)) :
    f ∈ hS.R ∧ hS.R = D ⊔ Subgroup.zpowers f ∧
      (Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 1 ∨ Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 3) := by
  have hm : 1 ≤ m := by omega
  have hy4 : (4 : ℤ) ∣ y - 1 := by
    have := dvd_add (dvd_trans (four_dvd_two_pow (m := m + 2) (by omega)) hy)
      (four_dvd_two_pow hm2)
    rwa [show y - (1 + 2 ^ m) + 2 ^ m = y - 1 by ring] at this
  have hfR := hn.mem.1
  have hn2 := hn.mul hn
  have hn3 := hn2.mul hn
  refine ⟨hfR, le_antisymm (h.t200_R_le hS hm hfus le_sup_left fun q' hq' hex => ?_)
    (sup_le hS.D_le_R (Subgroup.zpowers_le.mpr hfR)), ?_⟩
  · have hz : f ∈ Subgroup.zpowers f := Subgroup.mem_zpowers f
    have hm' : q' = p ∨ q' = 2 ∨ q' = 4 - p := by omega
    rcases hm' with rfl | rfl | rfl
    · exact ⟨f, Subgroup.mem_sup_right hz, y, q', hn, by norm_num⟩
    · refine ⟨f * f, Subgroup.mem_sup_right (mul_mem hz hz), _, _, hn2, ?_⟩
      obtain ⟨c, hc⟩ := hy4
      rcases hp with rfl | rfl
      · exact ⟨-c, by linear_combination -hc⟩
      · exact ⟨-1 - 3 * c, by linear_combination -3 * hc⟩
    · refine ⟨f * f * f, Subgroup.mem_sup_right (mul_mem (mul_mem hz hz) hz), _, _, hn3, ?_⟩
      exact dvd_sub_comm.mp (cube_class hy4)
  · rcases hp with rfl | rfl
    · exact Or.inl (hn.rel34x (q := 1) (by norm_num) hy
        (hn.f4_eq h (by norm_num) hm2 (Or.inl rfl) hy))
    · exact Or.inr (hn.rel34x (q := 3) (by norm_num) hy
        (hn.f4_eq h (by norm_num) hm2 (Or.inr rfl) hy))

theorem t200_case_cyclic (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {g : G} {y p : ℤ}
    (hp : p = 1 ∨ p = 3) (hn : Normal200 hS dD g y p) (hy4 : y % 4 = 1) :
    2 ≤ m ∧ ∃ f ∈ hS.R, hS.R = D ⊔ Subgroup.zpowers f ∧
      (Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 1 ∨ Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 3) := by
  have hodd := hn.odd
  have hn2 := hn.mul hn
  have hg2D : g * g ∉ D := fun hD => by
    have := hn2.dvd_of_mem hD
    rcases hp with rfl | rfl <;> omega
  have hn4 := hn2.mul hn2
  have hg4D : g * g * (g * g) ∈ D := by
    refine hn4.mem_of_dvd h ?_
    obtain ⟨c, hc⟩ : ∃ c, y = 2 * c + 1 := ⟨y / 2, by omega⟩
    obtain ⟨d, hd⟩ : (2 : ℤ) ∣ y * p + p := by rcases hp with rfl | rfl <;> omega
    exact ⟨(2 * c * c + 2 * c + 1) * d, by rw [show y * y * (y * p + p) + (y * p + p) =
      (y * y + 1) * (y * p + p) by ring, hd, hc]; ring⟩
  have hz := hn4.scalar_dvd_of_mem hg4D
  have hz1 : ¬ (2 : ℤ) ^ (m + 2) ∣ y * y - 1 := fun hz1 => hg2D (hn2.mem_of_scalar hz1)
  have h8 : (8 : ℤ) ∣ y * y - 1 := by
    have := Stroth34Arith.sq_odd_mod_eight (Int.odd_iff.mpr hodd)
    rwa [sq] at this
  have h8m : (8 : ℤ) ∣ 2 ^ (m + 2) := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    exact ⟨2 ^ j, by ring⟩
  obtain ⟨hm2, hzz⟩ : 2 ≤ m ∧ (2 : ℤ) ^ (m + 2) ∣ y * y - (1 + 2 ^ (m + 1)) := by
    rcases y_cases (y := y * y) hz with hz' | hz' | hz' | hz'
    · exact absurd hz' hz1
    · have := dvd_trans h8m hz'
      generalize y * y = z at h8 this
      omega
    · refine ⟨?_, hz'⟩
      by_contra hlt
      have hm1 : m = 1 := by omega
      have := dvd_trans h8m hz'
      rw [hm1] at this
      norm_num at this
      generalize y * y = z at h8 this
      omega
    · exfalso
      have := dvd_trans h8m hz'
      rcases Nat.lt_or_ge m 2 with hlt | hge
      · have hm1 : m = 1 := by omega
        rw [hm1] at this
        norm_num at this
        generalize y * y = z at h8 this
        omega
      · obtain ⟨w, hw⟩ : (8 : ℤ) ∣ 2 ^ (m + 1) := by
          obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
          exact ⟨2 ^ j, by ring⟩
        rw [hw] at this
        generalize y * y = z at h8 this
        omega
  obtain ⟨k, hk⟩ := Stroth34Arith.sq_eq_one_add_cases (j := m) (y := y) hm (by omega)
    (by rw [sq]; exact hzz)
  refine ⟨hm2, ?_⟩
  rcases Int.even_or_odd k with ⟨k', hk'⟩ | ⟨k', hk'⟩
  ·
    obtain ⟨hfR, hR, hrel⟩ := h.t200_case_cyclic_of hS hm2 hfus hp hn
      ⟨k', by rw [hk, hk']; ring⟩
    exact ⟨g, hfR, hR, hrel⟩
  ·
    have hn3 := hn2.mul hn
    obtain ⟨d, -, hd⟩ := hn3.renorm (p' := 4 - p) (cube_class (by omega))
    have hy3 : (2 : ℤ) ^ (m + 2) ∣ y * y * y - (1 + 2 ^ m) :=
      cyc_cube hm2 ⟨k', by linear_combination hk + 2 ^ (m + 1) * hk'⟩
    obtain ⟨hfR, hR, hrel⟩ := h.t200_case_cyclic_of hS hm2 hfus (by omega) hd hy3
    exact ⟨_, hfR, hR, hrel⟩

theorem t200_klein_of (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {e f : G}
    {ye yf p : ℤ} {q : ℕ} (hpq : p = q) (hp : p = 1 ∨ p = 3) (he : Normal200 hS dD e ye 2)
    (hf : Normal200 hS dD f yf p) (hye : (2 : ℤ) ^ (m + 2) ∣ ye - (1 + 2 ^ (m + 1)))
    (hyf : (2 : ℤ) ^ (m + 2) ∣ yf + 1) :
    e ∈ hS.R ∧ f ∈ hS.R ∧ hS.R = D ⊔ Subgroup.closure {e, f} ∧ Rel34i dD e (2 ^ (m + 1)) ∧
      Rel34inv dD f 0 1 q ∧ f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) := by
  have heR := he.mem.1
  have hfR := hf.mem.1
  have hrel := he.rel34i h hye
  have hyf4 : (4 : ℤ) ∣ yf + 1 := dvd_trans (four_dvd_two_pow (m := m + 2) (by omega)) hyf
  refine ⟨heR, hfR, le_antisymm (h.t200_R_le hS hm hfus le_sup_left fun q' hq' hex => ?_)
    (sup_le hS.D_le_R ((Subgroup.closure_le _).mpr
      (Set.insert_subset_iff.mpr ⟨heR, Set.singleton_subset_iff.mpr hfR⟩))), hrel,
    hf.rel34inv hpq 0 (by simp) (by simpa using hyf) (hf.sq_eq_one h (dvd_mul_of_dvd_left hyf _)),
    ?_⟩
  · have hec : e ∈ Subgroup.closure ({e, f} : Set G) := Subgroup.subset_closure (by simp)
    have hfc : f ∈ Subgroup.closure ({e, f} : Set G) := Subgroup.subset_closure (by simp)
    have hm' : q' = p ∨ q' = 2 ∨ q' = 4 - p := by omega
    rcases hm' with rfl | rfl | rfl
    · exact ⟨f, Subgroup.mem_sup_right hfc, yf, q', hf, by norm_num⟩
    · exact ⟨e, Subgroup.mem_sup_right hec, ye, 2, he, by norm_num⟩
    · refine ⟨e * f, Subgroup.mem_sup_right (mul_mem hec hfc), _, _, he.mul hf, ?_⟩
      rcases hp with rfl | rfl <;> omega
  ·
    have hef := (he.mul hf).eq h ((hf.mul he).mul_c (1 + 2 ^ (m - 1))) (klein_rel hm hp hye hyf)
    have hc : dD.ofT ((1 + 2 ^ (m - 1) : ℤ) • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) =
        (dD.c : G) * (dD.c : G) ^ 2 ^ (m - 1) := by
      rw [add_zsmul, one_zsmul, dD.ofT_add, ← dD.t200_c_eq, dD.t200_c_pow_eq]
      push_cast
      rfl
    have he2 : e * (dD.c : G) = e⁻¹ := by
      have := hrel.e_sq
      calc e * (dD.c : G) = e * ((dD.c : G)⁻¹)⁻¹ := by rw [inv_inv]
        _ = e * (e * e)⁻¹ := by rw [this]
        _ = e⁻¹ := by group
    rw [hc] at hef
    calc f⁻¹ * e * f = f⁻¹ * (e * f) := by group
      _ = f⁻¹ * (f * e * ((dD.c : G) * (dD.c : G) ^ 2 ^ (m - 1))) := by rw [hef]
      _ = e * (dD.c : G) * (dD.c : G) ^ 2 ^ (m - 1) := by group
      _ = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) := by rw [he2]

theorem t200_case_klein (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {e₁ e₃ : G} {y₁ y₃ : ℤ}
    (h₁ : Normal200 hS dD e₁ y₁ 1) (h₃ : Normal200 hS dD e₃ y₃ 3) (hy₁ : y₁ % 4 = 3)
    (hy₃ : y₃ % 4 = 3) :
    ∃ e ∈ hS.R, ∃ f ∈ hS.R, hS.R = D ⊔ Subgroup.closure {e, f} ∧ Rel34i dD e (2 ^ (m + 1)) ∧
      (Rel34inv dD f 0 1 1 ∨ Rel34inv dD f 0 1 3) ∧
      f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) := by
  have c₁ := y_cases_three hm hy₁
    ((h₁.mul h₁).scalar_dvd_of_mem ((h₁.mul h₁).mem_of_dvd h (by omega)))
  have c₃ := y_cases_three hm hy₃
    ((h₃.mul h₃).scalar_dvd_of_mem ((h₃.mul h₃).mem_of_dvd h (by omega)))
  have hne : ¬ (2 : ℤ) ^ (m + 2) ∣ y₁ - y₃ := fun hd => by
    have := h₁.dvd_of_mul_inv_mem h₃ (h₁.mul_inv_mem_of_scalar h₃ hd)
    omega
  obtain ⟨d, -, he⟩ := (h₁.mul h₃).renorm (p' := 2) (by omega)
  rcases c₁ with c₁ | c₁ <;> rcases c₃ with c₃ | c₃
  · exact absurd (by simpa using dvd_sub c₁ c₃) hne
  · obtain ⟨heR, hfR, hR, hi, hinv, hc⟩ := h.t200_klein_of hS hm hfus (q := 1) (by norm_num)
      (Or.inl rfl) he h₁ (klein_y c₁ c₃) c₁
    exact ⟨_, heR, e₁, hfR, hR, hi, Or.inl hinv, hc⟩
  · obtain ⟨heR, hfR, hR, hi, hinv, hc⟩ := h.t200_klein_of hS hm hfus (q := 3) (by norm_num)
      (Or.inr rfl) he h₃ (klein_y' c₁ c₃) c₃
    exact ⟨_, heR, e₃, hfR, hR, hi, Or.inr hinv, hc⟩
  · exact absurd (by simpa using dvd_sub c₁ c₃) hne

theorem t200_classify (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) :
    hS.R = D ∨
      (∃ e ∈ hS.R, hS.R = D ⊔ Subgroup.zpowers e ∧
        (Rel34i dD e (2 ^ (m + 1)) ∨ Rel34inv dD e 0 1 2 ∨ Rel34inv dD e 0 1 1 ∨
          Rel34inv dD e 0 1 3 ∨ Rel34inv dD e (2 ^ (m + 1)) 1 2 ∨
          Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
          Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3)) ∨
      (∃ e ∈ hS.R, ∃ f ∈ hS.R, hS.R = D ⊔ Subgroup.closure {e, f} ∧
        Rel34i dD e (2 ^ (m + 1)) ∧ (Rel34inv dD f 0 1 1 ∨ Rel34inv dD f 0 1 3) ∧
        f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
      (2 ≤ m ∧ ∃ f ∈ hS.R, hS.R = D ⊔ Subgroup.zpowers f ∧
        (Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 1 ∨ Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 3)) := by
  have four : ∀ {e₁ e₃ : G} {y₁ y₃ : ℤ}, Normal200 hS dD e₁ y₁ 1 → Normal200 hS dD e₃ y₃ 3 →
      (∃ e ∈ hS.R, ∃ f ∈ hS.R, hS.R = D ⊔ Subgroup.closure {e, f} ∧
        Rel34i dD e (2 ^ (m + 1)) ∧ (Rel34inv dD f 0 1 1 ∨ Rel34inv dD f 0 1 3) ∧
        f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
      (2 ≤ m ∧ ∃ f ∈ hS.R, hS.R = D ⊔ Subgroup.zpowers f ∧
        (Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 1 ∨ Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 3)) := by
    intro e₁ e₃ y₁ y₃ h₁ h₃
    have o₁ := h₁.odd
    have o₃ := h₃.odd
    rcases (by omega : y₁ % 4 = 1 ∨ y₁ % 4 = 3) with hy₁ | hy₁
    · exact Or.inr (h.t200_case_cyclic hS hm hfus (Or.inl rfl) h₁ hy₁)
    · rcases (by omega : y₃ % 4 = 1 ∨ y₃ % 4 = 3) with hy₃ | hy₃
      · exact Or.inr (h.t200_case_cyclic hS hm hfus (Or.inr rfl) h₃ hy₃)
      · exact Or.inl (h.t200_case_klein hS hm hfus h₁ h₃ hy₁ hy₃)
  by_cases c2 : ∃ e : G, ∃ y : ℤ, Normal200 hS dD e y 2
  · by_cases c1 : ∃ e : G, ∃ y : ℤ, Normal200 hS dD e y 1
    · obtain ⟨e₁, y₁, h₁⟩ := c1
      obtain ⟨e₂, y₂, h₂⟩ := c2
      have o₁ := h₁.odd
      obtain ⟨e₃, y₃, h₃⟩ := (h₂.mul h₁).cls_of (q := 3) (by omega)
      exact Or.inr (Or.inr (four h₁ h₃))
    · by_cases c3 : ∃ e : G, ∃ y : ℤ, Normal200 hS dD e y 3
      · obtain ⟨e₂, y₂, h₂⟩ := c2
        obtain ⟨e₃, y₃, h₃⟩ := c3
        have o₃ := h₃.odd
        exact absurd ((h₂.mul h₃).cls_of (q := 1) (by omega)) c1
      · obtain ⟨e₂, y₂, h₂⟩ := c2
        obtain ⟨heR, hR, hrel⟩ := h.t200_case_two hS hm hfus h₂ c1 c3
        refine Or.inr (Or.inl ⟨e₂, heR, hR, ?_⟩)
        rcases hrel with hr | hr | hr
        · exact Or.inl hr
        · exact Or.inr (Or.inl hr)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))
  · by_cases c1 : ∃ e : G, ∃ y : ℤ, Normal200 hS dD e y 1
    · by_cases c3 : ∃ e : G, ∃ y : ℤ, Normal200 hS dD e y 3
      · exfalso
        obtain ⟨e₁, y₁, h₁⟩ := c1
        obtain ⟨e₃, y₃, h₃⟩ := c3
        have o₁ := h₁.odd
        have o₃ := h₃.odd
        have hy₁ : y₁ % 4 = 3 := by
          by_contra hne
          exact c2 ((h₁.mul h₁).cls_of (by omega))
        have hy₃ : y₃ % 4 = 3 := by
          by_contra hne
          exact c2 ((h₃.mul h₃).cls_of (by omega))
        exact c2 ((h₁.mul h₃).cls_of (by omega))
      · obtain ⟨e₁, y₁, h₁⟩ := c1
        obtain ⟨heR, hR, hrel⟩ := h.t200_case_odd hS hm hfus (q := 1) (by norm_num)
          (Or.inl rfl) h₁ c2 (by rw [show (4 : ℤ) - 1 = 3 by norm_num]; exact c3)
        refine Or.inr (Or.inl ⟨e₁, heR, hR, ?_⟩)
        rcases hrel with hr | hr
        · exact Or.inr (Or.inr (Or.inl hr))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))
    · by_cases c3 : ∃ e : G, ∃ y : ℤ, Normal200 hS dD e y 3
      · obtain ⟨e₃, y₃, h₃⟩ := c3
        obtain ⟨heR, hR, hrel⟩ := h.t200_case_odd hS hm hfus (q := 3) (by norm_num)
          (Or.inr rfl) h₃ c2 (by rw [show (4 : ℤ) - 3 = 1 by norm_num]; exact c1)
        refine Or.inr (Or.inl ⟨e₃, heR, hR, ?_⟩)
        rcases hrel with hr | hr
        · exact Or.inr (Or.inr (Or.inr (Or.inl hr)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))
      · refine Or.inl (le_antisymm (h.t200_R_le hS hm hfus le_rfl fun q hq hex => ?_)
          hS.D_le_R)
        rcases hq with rfl | rfl | rfl
        · exact absurd hex c1
        · exact absurd hex c2
        · exact absurd hex c3

end StrothFrame.IsD

theorem stroth_3_4 {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
    (dD : StrothWeakTypeData D (StrothTypeIndex.t200 m)) (h : F.IsD D dD) (hm : 1 ≤ m)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        (Rel34i dD e (2 ^ (m + 1)) ∨
          Rel34inv dD e 0 1 2 ∨ Rel34inv dD e 0 1 1 ∨ Rel34inv dD e 0 1 3 ∨
          Rel34inv dD e (2 ^ (m + 1)) 1 2 ∨
          Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
          Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3)) ∨
      (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        ∃ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.closure {e, f} ∧
        Rel34i dD e (2 ^ (m + 1)) ∧ (Rel34inv dD f 0 1 1 ∨ Rel34inv dD f 0 1 3) ∧
        f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
      (2 ≤ m ∧ ∃ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers f ∧
        (Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 1 ∨ Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 3)) :=
  h.t200_classify (h.setting hns) hm hfus

end CFSG.CGT.Stroth77
