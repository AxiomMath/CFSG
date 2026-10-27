module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

structure Rel (a b a' b' t : G) (M : ℕ) : Prop where
  one_le : 1 ≤ M
  qg : QG a b (2 * M)
  qg' : QG a' b' (2 * M)
  t_sq : t * t = 1
  ta : t * a = a' * t
  tb : t * b = b' * t
  c_aa : a * a' = a' * a
  c_ab : a * b' = b' * a
  c_ba : b * a' = a' * b
  c_bb : b * b' = b' * b
  z_eq : a' ^ (2 * M) = a ^ (2 * M)

theorem mul_zpow_of_conj_inv {x y : G} (h : x * y * x⁻¹ = y⁻¹) (k : ℤ) : x * y ^ k = y ^ (-k) * x := by
  have h1 : (x * y * x⁻¹) ^ k = x * y ^ k * x⁻¹ := conj_zpow
  rw [h, inv_zpow', ] at h1
  calc x * y ^ k = (x * y ^ k * x⁻¹) * x := by group
    _ = y ^ (-k) * x := by rw [← h1]

namespace Rel

variable {a b a' b' t : G} {M : ℕ}

theorem t_inv (h : Rel a b a' b' t M) : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq

theorem tat (h : Rel a b a' b' t M) : t * a * t = a' := by
  rw [h.ta, mul_assoc, h.t_sq, mul_one]

theorem ta' (h : Rel a b a' b' t M) : t * a' = a * t :=
  calc t * a' = t * a' * (t * t) := by rw [h.t_sq, mul_one]
    _ = t * (a' * t) * t := by simp only [mul_assoc]
    _ = t * (t * a) * t := by rw [h.ta]
    _ = (t * t) * a * t := by simp only [mul_assoc]
    _ = a * t := by rw [h.t_sq, one_mul]

theorem tbt (h : Rel a b a' b' t M) : t * b * t = b' := by
  rw [h.tb, mul_assoc, h.t_sq, mul_one]

theorem tb' (h : Rel a b a' b' t M) : t * b' = b * t :=
  calc t * b' = t * b' * (t * t) := by rw [h.t_sq, mul_one]
    _ = t * (b' * t) * t := by simp only [mul_assoc]
    _ = t * (t * b) * t := by rw [h.tb]
    _ = (t * t) * b * t := by simp only [mul_assoc]
    _ = b * t := by rw [h.t_sq, one_mul]

theorem comm_zpow (h : Rel a b a' b' t M) (i j : ℤ) : a ^ i * a' ^ j = a' ^ j * a ^ i :=
  ((show Commute a a' from h.c_aa).zpow_zpow i j).eq

theorem b_zpow_a (h : Rel a b a' b' t M) (k : ℤ) : b * a ^ k = a ^ (-k) * b := by
  apply mul_zpow_of_conj_inv _ k
  have := h.qg.b_conj 1
  simpa using this

theorem b'_zpow_a' (h : Rel a b a' b' t M) (k : ℤ) : b' * a' ^ k = a' ^ (-k) * b' := by
  apply mul_zpow_of_conj_inv _ k
  have := h.qg'.b_conj 1
  simpa using this

theorem b_zpow_a' (h : Rel a b a' b' t M) (k : ℤ) : b * a' ^ k = a' ^ k * b :=
  ((show Commute b a' from h.c_ba).zpow_right k).eq

theorem b'_zpow_a (h : Rel a b a' b' t M) (k : ℤ) : b' * a ^ k = a ^ k * b' :=
  ((show Commute b' a from h.c_ab.symm).zpow_right k).eq

theorem aN_sq (h : Rel a b a' b' t M) : a ^ (2 * M) * a ^ (2 * M) = 1 := h.qg.aN_sq

theorem b_sq (h : Rel a b a' b' t M) : b * b = a ^ (2 * M) := h.qg.bsq

theorem b'_sq (h : Rel a b a' b' t M) : b' * b' = a ^ (2 * M) := by rw [h.qg'.bsq, h.z_eq]

theorem b0_sq (h : Rel a b a' b' t M) : (b * b') * (b * b') = 1 := by
  calc (b * b') * (b * b') = b * (b' * b) * b' := by simp only [mul_assoc]
    _ = b * (b * b') * b' := by rw [h.c_bb]
    _ = (b * b) * (b' * b') := by simp only [mul_assoc]
    _ = 1 := by rw [h.b_sq, h.b'_sq, h.aN_sq]

theorem t_b0 (h : Rel a b a' b' t M) : t * (b * b') = (b * b') * t := by
  calc t * (b * b') = (t * b) * b' := by rw [mul_assoc]
    _ = b' * (t * b') := by rw [h.tb, mul_assoc]
    _ = b' * (b * t) := by rw [h.tb']
    _ = (b' * b) * t := by rw [mul_assoc]
    _ = (b * b') * t := by rw [h.c_bb]

theorem b0_zpow_a (h : Rel a b a' b' t M) (k : ℤ) :
    (b * b') * a ^ k = a ^ (-k) * (b * b') := by
  calc (b * b') * a ^ k = b * (b' * a ^ k) := by rw [mul_assoc]
    _ = b * (a ^ k * b') := by rw [h.b'_zpow_a]
    _ = (b * a ^ k) * b' := by rw [mul_assoc]
    _ = a ^ (-k) * (b * b') := by rw [h.b_zpow_a, mul_assoc]

theorem b0_zpow_a' (h : Rel a b a' b' t M) (k : ℤ) :
    (b * b') * a' ^ k = a' ^ (-k) * (b * b') := by
  calc (b * b') * a' ^ k = b * (b' * a' ^ k) := by rw [mul_assoc]
    _ = b * (a' ^ (-k) * b') := by rw [h.b'_zpow_a']
    _ = (b * a' ^ (-k)) * b' := by rw [mul_assoc]
    _ = a' ^ (-k) * (b * b') := by rw [h.b_zpow_a', mul_assoc]

theorem orderOf_a (h : Rel a b a' b' t M) : orderOf a = 2 * (2 * M) := h.qg.ord

theorem orderOf_a' (h : Rel a b a' b' t M) : orderOf a' = 2 * (2 * M) := h.qg'.ord

theorem dvd_of_zpow_eq_a (h : Rel a b a' b' t M) {i j : ℤ} (hij : a ^ i = a' ^ j) :
    ((2 * M : ℕ) : ℤ) ∣ i := by
  have h1 : b * a ^ i = a ^ (-i) * b := h.b_zpow_a i
  have h2 : b * a' ^ j = a' ^ j * b := h.b_zpow_a' j
  rw [hij, h2] at h1
  have h3 : a' ^ j = a ^ (-i) := mul_right_cancel h1
  have h4 : a ^ i = a ^ (-i) := hij.trans h3
  have h5 : a ^ (2 * i) = 1 := by
    calc a ^ (2 * i) = a ^ i * a ^ i := by rw [two_mul, zpow_add]
      _ = a ^ (-i) * a ^ i := by rw [← h4]
      _ = 1 := by rw [← zpow_add, neg_add_cancel, zpow_zero]
  have h6 : (orderOf a : ℤ) ∣ 2 * i := orderOf_dvd_iff_zpow_eq_one.2 h5
  rw [h.orderOf_a] at h6
  have h7 : ((2 * (2 * M) : ℕ) : ℤ) = 2 * ((2 * M : ℕ) : ℤ) := by push_cast; ring
  rw [h7] at h6
  exact Int.dvd_of_mul_dvd_mul_left (by norm_num) h6

theorem dvd_of_zpow_eq_a' (h : Rel a b a' b' t M) {i j : ℤ} (hij : a ^ i = a' ^ j) :
    ((2 * M : ℕ) : ℤ) ∣ j := by
  have h1 : b' * a' ^ j = a' ^ (-j) * b' := h.b'_zpow_a' j
  have h2 : b' * a ^ i = a ^ i * b' := h.b'_zpow_a i
  rw [← hij, h2] at h1
  have h3 : a ^ i = a' ^ (-j) := mul_right_cancel h1
  have h4 : a' ^ j = a' ^ (-j) := hij.symm.trans h3
  have h5 : a' ^ (2 * j) = 1 := by
    calc a' ^ (2 * j) = a' ^ j * a' ^ j := by rw [two_mul, zpow_add]
      _ = a' ^ (-j) * a' ^ j := by rw [← h4]
      _ = 1 := by rw [← zpow_add, neg_add_cancel, zpow_zero]
  have h6 : (orderOf a' : ℤ) ∣ 2 * j := orderOf_dvd_iff_zpow_eq_one.2 h5
  rw [h.orderOf_a'] at h6
  have h7 : ((2 * (2 * M) : ℕ) : ℤ) = 2 * ((2 * M : ℕ) : ℤ) := by push_cast; ring
  rw [h7] at h6
  exact Int.dvd_of_mul_dvd_mul_left (by norm_num) h6

end Rel

section FromData

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ}

theorem Data.rel_of_gens (h : Data S P₁ P₂ z t a) {a₀ b₀ : G} {M : ℕ} (ha : a₀ ∈ P₁) (hb : b₀ ∈ P₁)
    (hM : 1 ≤ M) (hqg : QG a₀ b₀ (2 * M)) (hspan : ∀ x ∈ P₁, ∃ k : ℕ, x = a₀ ^ k ∨ x = a₀ ^ k * b₀) :
    z = a₀ ^ (2 * M) ∧ Rel a₀ b₀ (t * a₀ * t⁻¹) (t * b₀ * t⁻¹) t M := by
  have hz : z = a₀ ^ (2 * M) :=
    hqg.eq_aN_of_involution (P := P₁) (by omega) hspan h.z_mem₁ h.z_sq h.z_ne_one
  refine ⟨hz, ?_⟩
  have hσ : ∀ g : G, t * g * t⁻¹ = (MulAut.conj t) g := fun g => (MulAut.conj_apply t g).symm
  have hconjpow : ∀ (g : G) (n : ℕ), (t * g * t⁻¹) ^ n = t * g ^ n * t⁻¹ := fun g n => conj_pow
  refine ⟨hM, hqg, ?_, h.t_inv, ?_, ?_, h.comm_σ ha ha, h.comm_σ ha hb, h.comm_σ hb ha,
    h.comm_σ hb hb, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [hσ, MulEquiv.orderOf_eq]; exact hqg.ord
    · rw [hconjpow, ← Data.σ_mul, hqg.bsq]
    · calc (t * b₀ * t⁻¹) * (t * a₀ * t⁻¹) = t * (b₀ * a₀) * t⁻¹ := by group
        _ = t * (a₀⁻¹ * b₀) * t⁻¹ := by rw [hqg.bcomm]
        _ = (t * a₀ * t⁻¹)⁻¹ * (t * b₀ * t⁻¹) := by group
  · group
  · group
  · rw [hconjpow, ← hz, h.σ_z]

end FromData

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
