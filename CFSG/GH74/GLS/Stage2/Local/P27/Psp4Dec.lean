module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Mm
public import CFSG.GH74.GLS.Stage2.Local.P27.Ps4Iface

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

section Fin

variable [Finite G]

namespace Data

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ}

omit [Finite G] in
theorem Zc_mem_S (h : Data S P₁ P₂ z t a) {y : G} (hy : y ∈ Zc (P₁ ⊔ P₂) z t) :
    y ∈ S ∧ y * y = 1 ∧ y ≠ 1 := by
  rcases hy with hz | ⟨r, hr, rfl⟩
  · have hz' : y = z := hz
    subst hz'
    exact ⟨h.z_mem, h.z_sq, h.z_ne_one⟩
  · have hrS : r ∈ S := h.R_le_S hr
    refine ⟨mul_mem (mul_mem hrS h.t_mem) (Subgroup.inv_mem _ hrS), ?_, ?_⟩
    · calc r * t * r⁻¹ * (r * t * r⁻¹) = r * (t * t) * r⁻¹ := by group
        _ = 1 := by rw [h.t_inv]; group
    · intro e
      apply h.t_not
      have e1 : t = r⁻¹ * (r * t * r⁻¹) * r := by group
      rw [e1, e]
      simp

omit [Finite G] in
theorem Zc_mul_z_mem_Xc (h : Data S P₁ P₂ z t a) {y : G} (hy : y ∈ Zc (P₁ ⊔ P₂) z t) (hyz : y ≠ z) :
    y * z ∈ Xc (P₁ ⊔ P₂) z t := by
  rcases hy with hz | ⟨r, hr, rfl⟩
  · exact absurd hz hyz
  · refine Or.inr ⟨r, hr, ?_⟩
    have hrS : r ∈ S := h.R_le_S hr
    have hzr : z * r⁻¹ = r⁻¹ * z := ((show Commute z r from h.z_cent' hrS).inv_right).eq
    calc r * t * r⁻¹ * z = r * t * (r⁻¹ * z) := mul_assoc _ _ _
      _ = r * t * (z * r⁻¹) := by rw [hzr]
      _ = r * (t * z) * r⁻¹ := by simp only [mul_assoc]

theorem Zc_mul_z_not_mem (h : Data S P₁ P₂ z t a) {y : G} (hy : y ∈ Zc (P₁ ⊔ P₂) z t) (hyz : y ≠ z) :
    y * z ∉ Zc (P₁ ⊔ P₂) z t := by
  obtain ⟨hyS, hysq, hy1⟩ := h.Zc_mem_S hy
  have hzy : z * y = y * z := h.z_cent' hyS
  have hyzS : y * z ∈ S := mul_mem hyS h.z_mem
  have hyzsq : (y * z) * (y * z) = 1 := by
    calc y * z * (y * z) = y * (z * y) * z := by simp only [mul_assoc]
      _ = y * (y * z) * z := by rw [hzy]
      _ = (y * y) * (z * z) := by simp only [mul_assoc]
      _ = 1 := by rw [hysq, h.z_sq, mul_one]
  have hyz1 : y * z ≠ 1 := by
    intro e
    apply hyz
    have := eq_inv_of_mul_eq_one_left e
    rw [this, h.z_inv]
  intro hZ
  exact (h.partition _ hyzS hyzsq hyz1).2 ⟨hZ, h.Zc_mul_z_mem_Xc hy hyz⟩

omit [Finite G] in
theorem mul_mem_R_of_not_mem (h : Data S P₁ P₂ z t a) {y y' : G} (hy : y ∈ S) (hy' : y' ∈ S)
    (hyR : y ∉ P₁ ⊔ P₂) (hy'R : y' ∉ P₁ ⊔ P₂) : y * y' ∈ P₁ ⊔ P₂ := by
  obtain ⟨a₁, ha₁, hall⟩ := Subgroup.relIndex_eq_two_iff.1 h.idx
  have h1 : y * a₁ ∈ P₁ ⊔ P₂ := by
    rcases hall y hy with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hyR
  have hy'inv : y'⁻¹ ∉ P₁ ⊔ P₂ := fun hh => hy'R (by simpa using Subgroup.inv_mem _ hh)
  have h2 : y'⁻¹ * a₁ ∈ P₁ ⊔ P₂ := by
    rcases hall y'⁻¹ (Subgroup.inv_mem _ hy') with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact h2
    · exact absurd h2 hy'inv
  have e : y * y' = (y * a₁) * (y'⁻¹ * a₁)⁻¹ := by group
  rw [e]
  exact mul_mem h1 (Subgroup.inv_mem _ h2)

end Data

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem refl1_eq_rr (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k = rr t (a₀ ^ k) (a₀ ^ (-k)) := by
  rw [h.rel.dl1_zpow]
  unfold rr
  rw [conj_zpow]

theorem refl1_mem_Z (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t ∈ Zc (P₁ ⊔ P₂) z t := by
  rw [h.refl1_eq_rr k]
  exact (h.data.rrt_mem_Zc_iff (zpow_mem h.ha k) (zpow_mem h.ha (-k))).2
    (by rw [← zpow_add, add_neg_cancel, zpow_zero])

theorem refl2_not_mem_Z (h : Canon S P₁ P₂ z t a a₀ b₀ M) (j : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t) ∉ Zc (P₁ ⊔ P₂) z t := by
  intro hZ
  rw [h.refl2_eq j] at hZ
  have hq : a₀ ^ j * b₀ ∈ P₁ := mul_mem (zpow_mem h.ha j) h.hb
  have h1 := (h.data.rrt_mem_Zc_iff hq hq).1 hZ
  have e : (a₀ ^ j * b₀) * (a₀ ^ j * b₀) = z := by
    calc (a₀ ^ j * b₀) * (a₀ ^ j * b₀) = a₀ ^ j * (b₀ * a₀ ^ j) * b₀ := by simp only [mul_assoc]
      _ = a₀ ^ j * (a₀ ^ (-j) * b₀) * b₀ := by rw [h.rel.b_zpow_a j]
      _ = (a₀ ^ j * a₀ ^ (-j)) * (b₀ * b₀) := by simp only [mul_assoc]
      _ = z := by rw [← zpow_add, add_neg_cancel, zpow_zero, one_mul, h.rel.b_sq, ← h.hz]
  rw [e] at h1
  exact h.data.z_ne_one h1

omit [Finite G] in
theorem r_mem_R (h : Canon S P₁ P₂ z t a a₀ b₀ M) : a₀ * (t * a₀ * t⁻¹)⁻¹ ∈ P₁ ⊔ P₂ :=
  mul_mem (mem_sup_left h.ha) (Subgroup.inv_mem _ (mem_sup_right h.a'_mem))

omit [Finite G] in
theorem r2_mem_R (h : Canon S P₁ P₂ z t a a₀ b₀ M) : a₀ * (t * a₀ * t⁻¹) ∈ P₁ ⊔ P₂ :=
  mul_mem (mem_sup_left h.ha) (mem_sup_right h.a'_mem)

omit [Finite G] in
theorem refl1_not_mem_R (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t ∉ P₁ ⊔ P₂ := by
  intro hmem
  apply h.data.t_not
  have hr : (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k ∈ P₁ ⊔ P₂ := zpow_mem h.r_mem_R k
  have h' := mul_mem (Subgroup.inv_mem _ hr) hmem
  rwa [inv_mul_cancel_left] at h'

omit [Finite G] in
theorem refl2_not_mem_R (h : Canon S P₁ P₂ z t a a₀ b₀ M) (j : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t) ∉ P₁ ⊔ P₂ := by
  intro hmem
  apply h.data.t_not
  have hr2 : (a₀ * (t * a₀ * t⁻¹)) ^ j ∈ P₁ ⊔ P₂ := zpow_mem h.r2_mem_R j
  have hbb : b₀ * (t * b₀ * t⁻¹) ∈ P₁ ⊔ P₂ :=
    mul_mem (mem_sup_left h.hb) (mem_sup_right h.b'_mem)
  have h1 := mul_mem (Subgroup.inv_mem _ hr2) hmem
  rw [inv_mul_cancel_left] at h1
  have h2 := mul_mem (Subgroup.inv_mem _ hbb) h1
  rwa [mul_assoc, inv_mul_cancel_left] at h2

end Canon

end Fin

theorem sq3_aux {A B a r r2 : G} (hAB : Commute A B) (hAa : Commute A a) (hBa : Commute B a)
    (haa : a * a = r * r2) (hBr : Commute B r) :
    (A * B * a) * (A * B * a) = (A * A * r) * (B * B * r2) := by
  calc (A * B * a) * (A * B * a) = (A * B * a) ^ 2 := (pow_two _).symm
    _ = (A * B) ^ 2 * a ^ 2 := Commute.mul_pow (hAa.mul_left hBa) 2
    _ = A ^ 2 * B ^ 2 * a ^ 2 := by rw [Commute.mul_pow hAB]
    _ = (A * A) * (B * B) * (a * a) := by simp only [pow_two]
    _ = (A * A) * (B * B) * (r * r2) := by rw [haa]
    _ = (A * A) * ((B * B) * r) * r2 := by simp only [mul_assoc]
    _ = (A * A) * (r * (B * B)) * r2 := by rw [(hBr.mul_left hBr).eq]
    _ = (A * A * r) * (B * B * r2) := by simp only [mul_assoc]

theorem sq4_aux {A e φe a r r2 : G} (hAe : A * e = e * A) (hAa : A * a = a * A)
    (hae : a * e = φe * a) (haa : a * a = r * r2) (hef : e * φe = r2⁻¹) (hrr2 : r * r2 = r2 * r) :
    (A * e * a) * (A * e * a) = A * A * r := by
  calc (A * e * a) * (A * e * a) = A * e * (a * A) * e * a := by simp only [mul_assoc]
    _ = A * e * (A * a) * e * a := by rw [hAa]
    _ = A * (e * A) * a * e * a := by simp only [mul_assoc]
    _ = A * (A * e) * a * e * a := by rw [hAe]
    _ = A * A * e * (a * e) * a := by simp only [mul_assoc]
    _ = A * A * e * (φe * a) * a := by rw [hae]
    _ = A * A * (e * φe) * (a * a) := by simp only [mul_assoc]
    _ = A * A * r2⁻¹ * (r * r2) := by rw [hef, haa]
    _ = A * A * (r2⁻¹ * (r * r2)) := mul_assoc _ _ _
    _ = A * A * (r2⁻¹ * (r2 * r)) := by rw [hrr2]
    _ = A * A * r := by rw [inv_mul_cancel_left]

theorem sq5_aux {ρ ρ' B a r r2 : G} (hBρ' : B * ρ' = ρ' * B)
    (hBa : B * a = a * B) (haρ : a * ρ = ρ' * a) (haa : a * a = r * r2) (hρρ' : ρ * ρ' = r⁻¹)
    (hBr : B * r = r * B) :
    (ρ * B * a) * (ρ * B * a) = B * B * r2 := by
  calc (ρ * B * a) * (ρ * B * a) = ρ * B * (a * ρ) * B * a := by simp only [mul_assoc]
    _ = ρ * B * (ρ' * a) * B * a := by rw [haρ]
    _ = ρ * (B * ρ') * (a * B) * a := by simp only [mul_assoc]
    _ = ρ * (ρ' * B) * (B * a) * a := by rw [hBρ', hBa]
    _ = (ρ * ρ') * (B * B) * (a * a) := by simp only [mul_assoc]
    _ = r⁻¹ * (B * B) * (r * r2) := by rw [hρρ', haa]
    _ = r⁻¹ * ((B * B) * r) * r2 := by simp only [mul_assoc]
    _ = r⁻¹ * (r * (B * B)) * r2 := by rw [(Commute.mul_left (show Commute B r from hBr) (show Commute B r from hBr)).eq]
    _ = B * B * r2 := by rw [inv_mul_cancel_left]

theorem sq6_aux {ρ B : G} (hBρ : B * ρ = ρ * B) (hρ : ρ * ρ = 1) :
    (ρ * B) * (ρ * B) = B * B := by
  calc (ρ * B) * (ρ * B) = ρ * (B * ρ) * B := by simp only [mul_assoc]
    _ = ρ * (ρ * B) * B := by rw [hBρ]
    _ = (ρ * ρ) * (B * B) := by simp only [mul_assoc]
    _ = B * B := by rw [hρ, one_mul]

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem r_odd_ne_one (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (2 * i + 1) ≠ 1 := by
  intro e
  have e3 := h.dih1.zpow_eq_one_iff.1 e
  have e4 : (2 : ℤ) ∣ 2 * i + 1 := dvd_trans ⟨M, by push_cast; ring⟩ e3
  omega

omit [Finite G] in
theorem r2_odd_ne_one (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)) ^ (2 * i + 1) ≠ 1 := by
  intro e
  have e3 := h.dih2.zpow_eq_one_iff.1 e
  have e4 : (2 : ℤ) ∣ 2 * i + 1 := dvd_trans ⟨M, by push_cast; ring⟩ e3
  omega

end Canon

end Fin

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem r_zpow_mem_D1 (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i ∈ D1 a₀ (t * a₀ * t⁻¹) t := h.zpowers_r_le_D1 (zpow_mem (mem_zpowers _) i)

omit [Finite G] in
theorem r2_zpow_mem_D2 (_h : Canon S P₁ P₂ z t a a₀ b₀ M) (i : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)) ^ i ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t :=
  mem_sup_left (zpow_mem (mem_zpowers _) i)

omit [Finite G] in
theorem r_zpow_comm_a (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * a₀ = a₀ * (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i :=
  ((h.rel.commute_dl1_a.zpow_left i).eq)

omit [Finite G] in
theorem r2_zpow_comm_a (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)) ^ i * a₀ = a₀ * (a₀ * (t * a₀ * t⁻¹)) ^ i :=
  ((h.rel.commute_dl2_a.zpow_left i).eq)

omit [Finite G] in
theorem D1D2_commute (h : Canon S P₁ P₂ z t a a₀ b₀ M) {x y : G}
    (hx : x ∈ D1 a₀ (t * a₀ * t⁻¹) t) (hy : y ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t) :
    Commute x y := h.rel.D1_D2_comm x hx y hy

omit [Finite G] in
theorem no_inv_La_rot (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i j : ℤ) :
    ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * (a₀ * (t * a₀ * t⁻¹)) ^ j * a₀) *
      ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * (a₀ * (t * a₀ * t⁻¹)) ^ j * a₀) ≠ 1 := by
  intro hsq
  have hA := h.r_zpow_mem_D1 i
  have hB := h.r2_zpow_mem_D2 j
  rw [sq3_aux (r := a₀ * (t * a₀ * t⁻¹)⁻¹) (r2 := a₀ * (t * a₀ * t⁻¹))
    (h.D1D2_commute hA hB) ((h.rel.commute_dl1_a.zpow_left i))
    ((h.rel.commute_dl2_a.zpow_left j)) h.a_sq_eq
    (h.D1D2_commute (Rel.dl1_mem_D1 _ _ _) hB).symm] at hsq
  have hu := h.unique_decomp (d₁ := (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i *
      (a₀ * (t * a₀ * t⁻¹)⁻¹)) (d₁' := 1) (d₂ := (a₀ * (t * a₀ * t⁻¹)) ^ j * (a₀ * (t * a₀ * t⁻¹)) ^ j *
      (a₀ * (t * a₀ * t⁻¹))) (d₂' := 1)
    (mul_mem (mul_mem hA hA) (Rel.dl1_mem_D1 _ _ _)) (one_mem _)
    (mul_mem (mul_mem hB hB) (Rel.dl2_mem_D2 _ _ _ _ _)) (one_mem _) (by rw [hsq, mul_one])
  apply h.r_odd_ne_one i
  rw [show 2 * i + 1 = i + i + 1 by ring, zpow_add_one, zpow_add]
  exact hu.1

end Canon

end Fin

theorem sq2_aux {A B : G} (hAB : A * B = B * A) : (A * B) * (A * B) = (A * A) * (B * B) := by
  calc (A * B) * (A * B) = A * (B * A) * B := by simp only [mul_assoc]
    _ = A * (A * B) * B := by rw [← hAB]
    _ = (A * A) * (B * B) := by simp only [mul_assoc]

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem no_inv_La_ref (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i j : ℤ) :
    ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) * a₀) *
      ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) * a₀)
      ≠ 1 := by
  intro hsq
  rw [sq4_aux (φe := (a₀ * (t * a₀ * t⁻¹)) ^ (j + 1) * (b₀ * (t * b₀ * t⁻¹) * t))
    (r := a₀ * (t * a₀ * t⁻¹)⁻¹) (r2 := a₀ * (t * a₀ * t⁻¹))
    (h.D1D2_commute (h.r_zpow_mem_D1 i) (h.dih2.refl_mem_D j)).eq
    (h.r_zpow_comm_a i) (mul_inv_eq_iff_eq_mul.1 (h.a_conj_refl2 j)) h.a_sq_eq
    (by rw [h.dih2.refl_mul_refl, show j - (j + 1) = -1 by ring, zpow_neg_one])
    h.rel.commute_dl1_dl2.eq] at hsq
  apply h.r_odd_ne_one i
  rw [show 2 * i + 1 = i + i + 1 by ring, zpow_add_one, zpow_add]
  exact hsq

omit [Finite G] in
theorem L_rot_inv (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i j : ℤ)
    (hsq : ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * (a₀ * (t * a₀ * t⁻¹)) ^ j) *
      ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * (a₀ * (t * a₀ * t⁻¹)) ^ j) = 1) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i = 1 ∧ (a₀ * (t * a₀ * t⁻¹)) ^ j = 1 ∨
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i = xx t a₀ M ∧ (a₀ * (t * a₀ * t⁻¹)) ^ j = 1 ∨
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i = 1 ∧ (a₀ * (t * a₀ * t⁻¹)) ^ j = xx t a₀ M * z ∨
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i = xx t a₀ M ∧ (a₀ * (t * a₀ * t⁻¹)) ^ j = xx t a₀ M * z := by
  have hA := h.r_zpow_mem_D1 i
  have hB := h.r2_zpow_mem_D2 j
  rw [sq2_aux (h.D1D2_commute hA hB).eq] at hsq
  have hu := h.unique_decomp (d₁ := (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i)
    (d₁' := 1) (d₂ := (a₀ * (t * a₀ * t⁻¹)) ^ j * (a₀ * (t * a₀ * t⁻¹)) ^ j) (d₂' := 1)
    (mul_mem hA hA) (one_mem _) (mul_mem hB hB) (one_mem _) (by rw [hsq, mul_one])
  have h1 := h.dih1.zpow_half hu.1
  have h2 := h.dih2.zpow_half hu.2
  rw [h.dl2_M_eq] at h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))

omit [Finite G] in
theorem L_ref_inv (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i j : ℤ)
    (hsq : ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t))) *
      ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t))) = 1) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i = 1 ∨ (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i = xx t a₀ M := by
  have hA := h.r_zpow_mem_D1 i
  have heD := h.dih2.refl_mem_D j
  rw [sq2_aux (h.D1D2_commute hA heD).eq, h.dih2.refl_sq j, mul_one] at hsq
  exact h.dih1.zpow_half hsq

end Canon

end Fin

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

theorem xz_not_mem_Z (h : Canon S P₁ P₂ z t a a₀ b₀ M) : xx t a₀ M * z ∉ Zc (P₁ ⊔ P₂) z t := by
  intro hZ
  have hR : xx t a₀ M * z ∈ P₁ ⊔ P₂ := mul_mem h.xx_mem_R (mem_sup_left h.data.z_mem₁)
  have := (h.data.mem_Zc_of_mem_R hR).1 hZ
  exact h.rel.dl1_M_ne_one (mul_right_cancel (this.trans (one_mul z).symm))

omit [Finite G] in
theorem xz_mem_D2 (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    xx t a₀ M * z ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := by
  rw [← h.dl2_M_eq]
  exact mem_sup_left (pow_mem (mem_zpowers _) M)

omit [Finite G] in
theorem z_eq_x_xz (h : Canon S P₁ P₂ z t a a₀ b₀ M) : xx t a₀ M * (xx t a₀ M * z) = z := by
  rw [← mul_assoc, h.xx_sq, one_mul]

omit [Finite G] in
theorem z_mem_K (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    z ∈ D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := by
  rw [← h.z_eq_x_xz]
  exact mul_mem (mem_sup_left h.xx_mem_D1) (mem_sup_right h.xz_mem_D2)

omit [Finite G] in
theorem a_mul_not_K (h : Canon S P₁ P₂ z t a a₀ b₀ M) {k κ : G}
    (hk : k ∈ D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t)
    (hκ : κ ∈ D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t)
    (e : k * a₀ = κ) : False := by
  apply h.rel.a_not_mem_sup
  have h' := mul_mem (Subgroup.inv_mem _ hk) hκ
  rw [← e, inv_mul_cancel_left] at h'
  exact h'

theorem M_class_xor (h : Canon S P₁ P₂ z t a a₀ b₀ M) {m : G} (hm : m ∈ Mm t a₀ b₀)
    (hsq : m * m = 1) (h1 : m ≠ 1) (hx : m ≠ xx t a₀ M) :
    ¬ (m ∈ Zc (P₁ ⊔ P₂) z t ↔ xx t a₀ M * m ∈ Zc (P₁ ⊔ P₂) z t) := by
  have hzZ : z ∈ Zc (P₁ ⊔ P₂) z t := Or.inl rfl
  have hxz := h.xz_not_mem_Z
  rcases h.mem_Mm_iff.1 hm with hL | ⟨k, hk, rfl⟩
  · obtain ⟨i, d, hd, rfl⟩ := h.mem_L_iff.1 hL
    obtain ⟨j, rfl | rfl⟩ := h.dih2.mem_iff.1 hd
    · rcases h.L_rot_inv i j hsq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact absurd (by rw [e1, e2, one_mul]) h1
      · exact absurd (by rw [e1, e2, mul_one]) hx
      · rw [e1, e2, one_mul]
        intro hiff
        exact hxz (hiff.2 (by rw [h.z_eq_x_xz]; exact hzZ))
      · rw [e1, e2, h.z_eq_x_xz]
        intro hiff
        exact hxz (hiff.1 hzZ)
    · rcases h.L_ref_inv i j hsq with e1 | e1
      · rw [e1, one_mul]
        intro hiff
        exact h.refl2_not_mem_Z j (hiff.2 (h.x_refl2_mem_Z j))
      · rw [e1]
        intro hiff
        have hxe := h.x_refl2_mem_Z j
        apply h.refl2_not_mem_Z j
        have := hiff.1 hxe
        rwa [← mul_assoc, h.xx_sq, one_mul] at this
  · obtain ⟨i, d, hd, rfl⟩ := h.mem_L_iff.1 hk
    obtain ⟨j, rfl | rfl⟩ := h.dih2.mem_iff.1 hd
    · exact absurd hsq (h.no_inv_La_rot i j)
    · exact absurd hsq (h.no_inv_La_ref i j)

end Canon

end Fin

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem xrefl_eq (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    xx t a₀ M * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ ((M : ℤ) + k) * t := by
  rw [h.xx_eq_pow, ← zpow_natCast, h.dih1.rot_mul_refl]

omit [Finite G] in
theorem refl1_ne_z (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t ≠ z := by
  intro e
  exact h.refl1_not_mem_R k (by rw [e]; exact mem_sup_left h.data.z_mem₁)

omit [Finite G] in
theorem no_inv_E3_rot (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i j : ℤ) :
    ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t * (a₀ * (t * a₀ * t⁻¹)) ^ j * a₀) *
      ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t * (a₀ * (t * a₀ * t⁻¹)) ^ j * a₀) ≠ 1 := by
  intro hsq
  have hB := h.r2_zpow_mem_D2 j
  rw [sq5_aux (ρ' := (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (i + 1) * t) (r := a₀ * (t * a₀ * t⁻¹)⁻¹)
    (r2 := a₀ * (t * a₀ * t⁻¹))
    (h.D1D2_commute (h.refl_mem_D1 (i + 1)) hB).eq.symm
    (h.r2_zpow_comm_a j) (mul_inv_eq_iff_eq_mul.1 (h.a_conj_refl i)) h.a_sq_eq
    (by rw [h.dih1.refl_mul_refl, show i - (i + 1) = -1 by ring, zpow_neg_one])
    (h.D1D2_commute (Rel.dl1_mem_D1 _ _ _) hB).eq.symm] at hsq
  apply h.r2_odd_ne_one j
  rw [show 2 * j + 1 = j + j + 1 by ring, zpow_add_one, zpow_add]
  exact hsq

theorem N_class_eq (h : Canon S P₁ P₂ z t a a₀ b₀ M) {s : G} (hs : s ∈ HH t a₀ b₀)
    (hsM : s ∉ Mm t a₀ b₀) (hsq : s * s = 1) :
    (s ∈ Zc (P₁ ⊔ P₂) z t ↔ xx t a₀ M * s ∈ Zc (P₁ ⊔ P₂) z t) := by
  have hd := h.data
  rcases h.HH_nf hs with ⟨i, d, hd', rfl⟩ | ⟨i, d, hd', rfl⟩ | ⟨i, d, hd', rfl⟩ | ⟨i, d, hd', rfl⟩
  · exact absurd (h.mem_Mm_of_form1 i hd') hsM
  · obtain ⟨j, rfl | rfl⟩ := h.dih2.mem_iff.1 hd'
    ·
      have hBρ : (a₀ * (t * a₀ * t⁻¹)) ^ j * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t) =
          ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t) * (a₀ * (t * a₀ * t⁻¹)) ^ j :=
        (h.D1D2_commute (h.refl_mem_D1 i) (h.r2_zpow_mem_D2 j)).eq.symm
      rw [sq6_aux hBρ (h.dih1.refl_sq i)] at hsq
      have hxρ : xx t a₀ M * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t) =
          ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t) * xx t a₀ M := h.dih1.rM_comm_refl i
      rcases h.dih2.zpow_half hsq with hB | hB
      · rw [hB, mul_one]
        refine iff_of_true (h.refl1_mem_Z i) ?_
        rw [h.xrefl_eq i]
        exact h.refl1_mem_Z _
      · rw [hB, h.dl2_M_eq]
        have e1 : ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t) * (xx t a₀ M * z) =
            (xx t a₀ M * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t)) * z := by
          calc ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t) * (xx t a₀ M * z)
              = (((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t) * xx t a₀ M) * z := (mul_assoc _ _ _).symm
            _ = _ := by rw [hxρ]
        have e2 : xx t a₀ M * (((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t) * (xx t a₀ M * z)) =
            ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t) * z := by
          calc xx t a₀ M * (((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t) * (xx t a₀ M * z))
              = (xx t a₀ M * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t)) * (xx t a₀ M * z) := by
                simp only [mul_assoc]
            _ = (((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t) * xx t a₀ M) * (xx t a₀ M * z) := by rw [hxρ]
            _ = ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t) * ((xx t a₀ M * xx t a₀ M) * z) := by
                simp only [mul_assoc]
            _ = _ := by rw [h.xx_sq, one_mul]
        refine iff_of_false ?_ ?_
        · rw [e1, h.xrefl_eq i]
          exact hd.Zc_mul_z_not_mem (h.refl1_mem_Z _) (h.refl1_ne_z _)
        · rw [e2]
          exact hd.Zc_mul_z_not_mem (h.refl1_mem_Z i) (h.refl1_ne_z i)
    ·
      have hρS : (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t ∈ S := h.D1_le_S (h.refl_mem_D1 i)
      have heS : (a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t) ∈ S :=
        h.D2_le_S (h.dih2.refl_mem_D j)
      have hsR := hd.mul_mem_R_of_not_mem hρS heS (h.refl1_not_mem_R i) (h.refl2_not_mem_R j)
      have hxsR := mul_mem h.xx_mem_R hsR
      have hne1 : (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t *
          ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) ≠ z := by
        intro e
        have hu := h.unique_decomp (h.refl_mem_D1 i) h.xx_mem_D1 (h.dih2.refl_mem_D j)
          h.xz_mem_D2 (by rw [e, h.z_eq_x_xz])
        exact h.w_ne_x i hu.1
      have hne2 : xx t a₀ M * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t *
          ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t))) ≠ z := by
        intro e
        have e' : (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t *
            ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) = xx t a₀ M * z := by
          calc _ = xx t a₀ M * (xx t a₀ M * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t *
              ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)))) := by
                rw [← mul_assoc (xx t a₀ M) (xx t a₀ M), h.xx_sq, one_mul]
            _ = xx t a₀ M * z := by rw [e]
        have hu := h.unique_decomp (h.refl_mem_D1 i) (one_mem _) (h.dih2.refl_mem_D j)
          h.xz_mem_D2 (by rw [e', one_mul])
        exact h.w_ne_one i hu.1
      exact iff_of_false (fun hZ => hne1 ((hd.mem_Zc_of_mem_R hsR).1 hZ))
        (fun hZ => hne2 ((hd.mem_Zc_of_mem_R hxsR).1 hZ))
  · exact absurd (h.mem_Mm_of_form3 i hd') hsM
  · obtain ⟨j, rfl | rfl⟩ := h.dih2.mem_iff.1 hd'
    · exact absurd hsq (h.no_inv_E3_rot i j)
    ·
      have hρS : (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t ∈ S := h.D1_le_S (h.refl_mem_D1 i)
      have heS : (a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t) ∈ S :=
        h.D2_le_S (h.dih2.refl_mem_D j)
      have hρe := hd.mul_mem_R_of_not_mem hρS heS (h.refl1_not_mem_R i) (h.refl2_not_mem_R j)
      have hsR := mul_mem hρe (mem_sup_left h.ha)
      have hxsR := mul_mem h.xx_mem_R hsR
      have hK : (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t *
          ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) ∈
          D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t :=
        mul_mem (mem_sup_left (h.refl_mem_D1 i)) (mem_sup_right (h.dih2.refl_mem_D j))
      have hne1 : (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t *
          ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) * a₀ ≠ z :=
        fun e => h.a_mul_not_K hK h.z_mem_K e
      have hne2 : xx t a₀ M * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t *
          ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) * a₀) ≠ z := by
        intro e
        refine h.a_mul_not_K (mul_mem (mem_sup_left h.xx_mem_D1) hK) h.z_mem_K ?_
        rw [mul_assoc]
        exact e
      exact iff_of_false (fun hZ => hne1 ((hd.mem_Zc_of_mem_R hsR).1 hZ))
        (fun hZ => hne2 ((hd.mem_Zc_of_mem_R hxsR).1 hZ))

end Canon

end Fin

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem refl_not_mem_zpowers (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t ∉ zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) := by
  intro hmem
  apply h.rel.t_not_mem_dl1
  have h' := mul_mem (Subgroup.inv_mem _ (zpow_mem (mem_zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹)) i)) hmem
  rwa [inv_mul_cancel_left] at h'

omit [Finite G] in
theorem relIndex_T1 (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    (zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹)).relIndex (D1 a₀ (t * a₀ * t⁻¹) t) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨t, Rel.t_mem_D1 _ _ _, fun g hg => ?_⟩
  obtain ⟨i, e | e⟩ := h.dih1.mem_iff.1 hg
  · right
    refine ⟨by rw [e]; exact zpow_mem (mem_zpowers _) i, fun hmem => ?_⟩
    rw [e] at hmem
    exact h.refl_not_mem_zpowers i hmem
  · left
    refine ⟨?_, ?_⟩
    · have e1 : g * t = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i := by
        rw [e, mul_assoc _ t t, h.rel.t_sq, mul_one]
      rw [e1]
      exact zpow_mem (mem_zpowers _) i
    · rw [e]
      exact h.refl_not_mem_zpowers i

omit [Finite G] in
theorem T1_refl (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    ∀ d ∈ D1 a₀ (t * a₀ * t⁻¹) t, d ∉ zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) → d * d = 1 := by
  intro d hd hnot
  obtain ⟨i, e | e⟩ := h.dih1.mem_iff.1 hd
  · exact absurd (by rw [e]; exact zpow_mem (mem_zpowers _) i) hnot
  · rw [e]
    exact h.dih1.refl_sq i

omit [Finite G] in
theorem center_D1 (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    a = 3 ∨ (center ↥(D1 a₀ (t * a₀ * t⁻¹) t)).map (D1 a₀ (t * a₀ * t⁻¹) t).subtype =
      zpowers (xx t a₀ M) := by
  by_cases ha : a = 3
  · exact Or.inl ha
  · right
    have h3 := h.three_le
    have hM : 2 ≤ M := by
      have h4 : 4 ≤ 2 ^ (a - 2) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (a - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := h.hN
      omega
    refine center_map_eq_of_forall (Z := zpowers (xx t a₀ M)) ?_ ?_ ?_
    · rw [zpowers_le]
      exact h.xx_mem_D1
    · intro g hg hc
      rcases (h.dih1.central_iff hM hg).1 hc with e | e
      · rw [e]; exact one_mem _
      · rw [e]; exact mem_zpowers _
    · intro g hg d hd
      have hgD : g ∈ D1 a₀ (t * a₀ * t⁻¹) t := by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
        exact zpow_mem h.xx_mem_D1 k
      have := (h.dih1.central_iff hM hgD).2
      rcases (mem_zpowers_of_sq h.xx_sq).1 hg with e | e
      · exact (this (Or.inl e)) d hd
      · exact (this (Or.inr e)) d hd

theorem Mm_sep (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    ∀ s ∈ HH t a₀ b₀, s ∉ Mm t a₀ b₀ → s * s = 1 → ∀ m ∈ Mm t a₀ b₀, m * m = 1 → m ≠ 1 →
      m ≠ xx t a₀ M →
      ¬ ((s ∈ Zc (P₁ ⊔ P₂) z t ↔ m ∈ Zc (P₁ ⊔ P₂) z t) ∧
        (xx t a₀ M * s ∈ Zc (P₁ ⊔ P₂) z t ↔ xx t a₀ M * m ∈ Zc (P₁ ⊔ P₂) z t)) := by
  rintro s hs hsM hss m hm hmm hm1 hmx ⟨h1, h2⟩
  exact h.M_class_xor hm hmm hm1 hmx (h1.symm.trans ((h.N_class_eq hs hsM hss).trans h2))

theorem ps4_decomp (h : Canon S P₁ P₂ z t a a₀ b₀ M) {w0 : G}
    (hw0 : w0 ∈ Vset S (P₁ ⊔ P₂) z t (xx t a₀ M)) {U : Subgroup G}
    (hU : U ≤ Tc S t a₀ M ⊓ centralizer ({w0} : Set G)) (hcard : Nat.card ↥U = 2 ^ (a - 1))
    (hinf : ∀ y ∈ U, y ∈ zpowers (xx t a₀ M) ⊔ zpowers w0 → y = 1)
    (hcls : ∀ d ∈ U, d * d = 1 → d ≠ 1 → d ∈ Xc (P₁ ⊔ P₂) z t ∧ w0 * d ∈ Xc (P₁ ⊔ P₂) z t ∧
      xx t a₀ M * w0 * d ∈ Xc (P₁ ⊔ P₂) z t ∧ xx t a₀ M * d ∈ Zc (P₁ ⊔ P₂) z t) :
    ∃ D₁ T₁ M' : Subgroup G, Ps4Decomp (Tc S t a₀ M) D₁ U T₁ M' z (xx t a₀ M) w0 a
      (Zc (P₁ ⊔ P₂) z t) (Xc (P₁ ⊔ P₂) z t) := by
  obtain ⟨k, hk⟩ := h.V_form hw0
  have hw : w0 = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (k : ℤ) * t := by rw [zpow_natCast]; exact hk
  have hUD : U = D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := h.rigid hw hU hcard hinf hcls
  subst hUD
  refine ⟨D1 a₀ (t * a₀ * t⁻¹) t, zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹), Mm t a₀ b₀, ?_⟩
  have hTH : Tc S t a₀ M = HH t a₀ b₀ := h.Tc_eq_HH
  exact
    { D₁_dih := h.D1_dihedral
      D₂_dih := h.D2_dihedral
      D₁_le := (D1_le_HH t a₀ b₀).trans h.HH_le_Tc
      D₂_le := (D2_le_HH t a₀ b₀).trans h.HH_le_Tc
      comm := h.rel.D1_D2_comm
      inter := h.rel.D1_inf_D2
      index := by rw [hTH]; exact h.relIndex_K
      D₁_normal := fun s hs d hd => h.D1_normal s (hTH ▸ hs) d hd
      u_mem := h.xx_mem_D1
      center_D₁ := h.center_D1
      w0_mem := by rw [hw]; exact h.refl_mem_D1 _
      uz_mem := h.xz_mem_D2
      CTw0 := by
        intro g hg hgc
        have hmem : g ∈ Tc S t a₀ M ⊓ centralizer ({w0} : Set G) :=
          ⟨hg, mem_centralizer_singleton_iff.2 hgc⟩
        have hC := (h.Cw_eq (k : ℤ))
        rw [← hw] at hC
        rw [hC] at hmem
        have hV := h.V4_le_D1 (k : ℤ)
        rw [← hw] at hV
        have hle : (zpowers (xx t a₀ M) ⊔ zpowers w0) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ≤
            D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t :=
          sup_le (hV.trans le_sup_left) le_sup_right
        exact hle hmem
      T₁_le := h.zpowers_r_le_D1
      T₁_cyc := inferInstance
      u_T₁ := by rw [h.xx_eq_pow]; exact pow_mem (mem_zpowers _) M
      T₁_idx := h.relIndex_T1
      T₁_refl := h.T1_refl
      M_le := h.Mm_le_HH.trans h.HH_le_Tc
      M_idx := by rw [hTH]; exact h.relIndex_Mm
      R_le := h.L_le_Mm
      M_inter := fun g hg => h.Mm_inter_K g hg.1 hg.2
      M_der := h.Mm_der
      M_cos := fun w hw' hwM => h.Mm_cos (hTH ▸ hw') hwM
      M_sep := fun s hs hsM hss m hm hmm hm1 hmu => h.Mm_sep s (hTH ▸ hs) hsM hss m hm hmm hm1 hmu }

end Canon

end Fin

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
