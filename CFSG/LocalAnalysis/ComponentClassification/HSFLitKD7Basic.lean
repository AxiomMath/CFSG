module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKDBase
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KDBase

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv

namespace KD7

theorem aff8_sq_ne_one : ∀ c : ZMod 8, aff8 1 (2 * c) ^ 2 ≠ 1 → 2 * c = 2 ∨ 2 * c = 6 := by
  decide

theorem aff8_neg_sq : ∀ c : ZMod 8, aff8 (-1) (2 * c) ^ 2 = 1 := by decide

theorem aff8_sq_z8 : ∀ b : ZMod 8, (b = 2 ∨ b = 6) → aff8 1 b ^ 2 = z8 := by decide

theorem d8_refl : ∀ b e : ZMod 8, (b = 2 ∨ b = 6) → dbit8 e = 0 →
    d8 * aff8 (-1) e * d8⁻¹ = aff8 1 b * aff8 (-1) e ∨
      d8 * aff8 (-1) e * d8⁻¹ = (aff8 1 b)⁻¹ * aff8 (-1) e := by
  decide

theorem d8_inv : d8⁻¹ = d8 := by decide

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD}

include A in
theorem t_not_mem_L : t ∉ L := by
  intro h
  have : t ∈ A.K ⊓ L := ⟨A.t_mem_K, h⟩
  rw [A.K_inf_L, mem_bot] at this
  exact L2K.t_ne_one (A := A) this

omit [Finite X] in
include A in
theorem tt : t * t = 1 := by rw [← pow_two, L2K.t_sq (A := A)]

omit [Finite X] in
theorem k_not_mem_L : C.k ∉ L := by
  intro h
  have := L2K.ψX_mem_R8 (A := A) ⟨C.k_mem, h⟩
  rw [L2KD.ψX_k C] at this
  exact L2K.k8_not_mem_R8 this

omit [Finite X] in
theorem ψX_d_inv : L2K.ψX A C.d⁻¹ = d8 := by
  rw [L2K.ψX_inv C.d_mem, L2KD.ψX_d C, d8_inv]

variable (S : KDBase A C)

theorem x_mem_T : S.x ∈ A.T := S.x_mem.1

theorem y_mem_T : S.y ∈ A.T := S.y_mem.1

theorem z_mem_R : S.z ∈ A.R := pow_mem S.x_mem 2

theorem z_mem_L : S.z ∈ L := (z_mem_R S).2

theorem z_mem_T : S.z ∈ A.T := (z_mem_R S).1

theorem x_pow_four : S.x ^ 4 = 1 := by rw [← S.orderOf_x]; exact pow_orderOf_eq_one _

theorem z_sq : S.z ^ 2 = 1 := by
  show (S.x ^ 2) ^ 2 = 1
  rw [← pow_mul]
  exact (x_pow_four S)

theorem zz : S.z * S.z = 1 := by rw [← pow_two, z_sq]

theorem z_inv : S.z⁻¹ = S.z := inv_eq_of_mul_eq_one_right (zz S)

theorem z_ne_one : S.z ≠ 1 := by
  intro h
  have : orderOf S.x ∣ 2 := orderOf_dvd_of_pow_eq_one h
  rw [S.orderOf_x] at this
  norm_num at this

theorem x_ne_inv : S.x ≠ S.x⁻¹ := by
  intro h
  apply z_ne_one S
  show S.x ^ 2 = 1
  rw [pow_two]
  nth_rewrite 2 [h]
  exact mul_inv_cancel _

theorem ψX_x : ∃ b : ZMod 8, (b = 2 ∨ b = 6) ∧ L2K.ψX A S.x = aff8 1 b := by
  obtain ⟨u, c, hu, h⟩ := L2K.ψX_mem_R8 (A := A) S.x_mem
  have hsq : aff8 u (2 * c) ^ 2 ≠ 1 := by
    rw [h, ← L2K.ψX_pow S.x_mem.1]
    intro h1
    exact (z_ne_one S) (L2K.eq_one_of_ψX (z_mem_R S) h1)
  rcases hu with rfl | rfl
  · exact ⟨2 * c, aff8_sq_ne_one c hsq, h.symm⟩
  · exact absurd (aff8_neg_sq c) hsq

theorem ψX_z : L2K.ψX A S.z = z8 := by
  obtain ⟨b, hb, h⟩ := (ψX_x S)
  show L2K.ψX A (S.x ^ 2) = z8
  rw [L2K.ψX_pow S.x_mem.1, h, aff8_sq_z8 b hb]

theorem z_comm_T {g : X} (hg : g ∈ A.T) : g * S.z = S.z * g := by
  have hgz : g * S.z * g⁻¹ ∈ A.R :=
    Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg (z_mem_T S)) (inv_mem hg),
      L2K.conj_mem_L (A := A) (A.T_le_centralizer hg) (z_mem_L S)⟩
  have hψ : L2K.ψX A (g * S.z * g⁻¹) = L2K.ψX A S.z := by
    rw [L2K.ψX_conj hg (z_mem_T S), (ψX_z S)]
    obtain ⟨u, b, hub⟩ := L2KD.ψX_mem_H8 (A := A) hg
    rw [← hub, L2K.z8_comm_aff8', mul_inv_cancel_right]
  have := L2K.eq_of_ψX_eq hgz (z_mem_R S) hψ
  calc g * S.z = g * S.z * g⁻¹ * g := by group
    _ = S.z * g := by rw [this]

theorem conj_z {g : X} (hg : g ∈ A.T) : g * S.z * g⁻¹ = S.z := by
  rw [(z_comm_T S) hg, mul_inv_cancel_right]

structure IsRefl (r : X) : Prop where
  mem : r ∈ A.R
  sq : r ^ 2 = 1
  inv : r * S.x * r⁻¹ = S.x⁻¹

theorem isRefl_y : IsRefl S S.y := ⟨S.y_mem, S.y_sq, S.y_inv⟩

theorem isRefl_xy : IsRefl S (S.x * S.y) := by
  refine ⟨mul_mem S.x_mem S.y_mem, ?_, ?_⟩
  · rw [pow_two, show S.x * S.y * (S.x * S.y) = S.x * (S.y * S.x * S.y⁻¹) * (S.y * S.y) by
      group, S.y_inv, ← pow_two, S.y_sq, mul_one, mul_inv_cancel]
  · calc S.x * S.y * S.x * (S.x * S.y)⁻¹ = S.x * (S.y * S.x * S.y⁻¹) * S.x⁻¹ := by group
      _ = S.x⁻¹ := by rw [S.y_inv]; group

variable {S}

theorem IsRefl.ne_one {r : X} (h : IsRefl S r) : r ≠ 1 := by
  rintro rfl
  apply (x_ne_inv S)
  rw [← h.inv]
  group

theorem IsRefl.ne_z {r : X} (h : IsRefl S r) : r ≠ S.z := by
  rintro rfl
  apply (x_ne_inv S)
  rw [← h.inv, ← z_comm_T S (x_mem_T S), mul_inv_cancel_right]

theorem IsRefl.ψX {r : X} (h : IsRefl S r) :
    ∃ e : ZMod 8, dbit8 e = 0 ∧ L2K.ψX A r = aff8 (-1) e := by
  refine L2KD.refl_of_mem_R8 (L2K.ψX_mem_R8 h.mem) ?_ ?_ ?_
  · rw [← L2K.ψX_pow h.mem.1, h.sq, L2K.ψX_one]
  · exact fun h1 => h.ne_one (L2K.eq_one_of_ψX h.mem h1)
  · intro h1
    rw [← (ψX_z S)] at h1
    exact h.ne_z (L2K.eq_of_ψX_eq h.mem (z_mem_R S) h1)

theorem conj_refl_of_ψ {g : X} (hg : g ∈ A.T) (hψ : L2K.ψX A g = d8) {r : X}
    (h : IsRefl S r) : g * r * g⁻¹ = S.x * r ∨ g * r * g⁻¹ = S.x⁻¹ * r := by
  obtain ⟨b, hb, hx⟩ := (ψX_x S)
  obtain ⟨e, he, hr⟩ := h.ψX
  have hgr : g * r * g⁻¹ ∈ A.R :=
    Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg h.mem.1) (inv_mem hg),
      L2K.conj_mem_L (A := A) (A.T_le_centralizer hg) h.mem.2⟩
  have h1 : L2K.ψX A (g * r * g⁻¹) = d8 * aff8 (-1) e * d8⁻¹ := by
    rw [L2K.ψX_conj hg h.mem.1, hψ, hr]
  have h2 : L2K.ψX A (S.x * r) = aff8 1 b * aff8 (-1) e := by
    rw [L2K.ψX_mul (x_mem_T S) h.mem.1, hx, hr]
  have h3 : L2K.ψX A (S.x⁻¹ * r) = (aff8 1 b)⁻¹ * aff8 (-1) e := by
    rw [L2K.ψX_mul (inv_mem (x_mem_T S)) h.mem.1, L2K.ψX_inv (x_mem_T S), hx, hr]
  rcases d8_refl b e hb he with h4 | h4
  · left
    exact L2K.eq_of_ψX_eq hgr (mul_mem S.x_mem h.mem) (by rw [h1, h2, h4])
  · right
    exact L2K.eq_of_ψX_eq hgr (mul_mem (inv_mem S.x_mem) h.mem) (by rw [h1, h3, h4])

variable (S)

theorem conj_k_of_ψ {g : X} (hg : g ∈ A.T) (hψ : L2K.ψX A g = d8) :
    g * C.k * g⁻¹ = S.z * C.k ∨ g * C.k * g⁻¹ = S.z * C.k * t := by
  have hzk : S.z * C.k ∈ A.T := mul_mem (z_mem_T S) C.k_mem
  have hgk : g * C.k * g⁻¹ ∈ A.T := mul_mem (mul_mem hg C.k_mem) (inv_mem hg)
  have hm : (S.z * C.k)⁻¹ * (g * C.k * g⁻¹) ∈ A.T := mul_mem (inv_mem hzk) hgk
  have hK : (S.z * C.k)⁻¹ * (g * C.k * g⁻¹) ∈ A.K := by
    rw [← L2K.ψX_eq_one_iff hm, L2K.ψX_mul (inv_mem hzk) hgk, L2K.ψX_inv hzk,
      L2K.ψX_mul (z_mem_T S) C.k_mem, L2K.ψX_conj hg C.k_mem, (ψX_z S), L2KD.ψX_k C, hψ,
      L2KD.d8_k8, inv_mul_cancel]
  rcases L2KD.eq_one_or_eq_t_of_mem_K C hK with h | h
  · left
    calc g * C.k * g⁻¹ = S.z * C.k * ((S.z * C.k)⁻¹ * (g * C.k * g⁻¹)) := by group
      _ = S.z * C.k := by rw [h, mul_one]
  · right
    calc g * C.k * g⁻¹ = S.z * C.k * ((S.z * C.k)⁻¹ * (g * C.k * g⁻¹)) := by group
      _ = S.z * C.k * t := by rw [h]

theorem zk_not_mem_L : S.z * C.k ∉ L := fun h =>
  k_not_mem_L (C := C) (by simpa using mul_mem (inv_mem (z_mem_L S)) h)

theorem t_mul_not_mem_L {a : X} (ha : a = C.k ∨ a = S.z * C.k) : t * a ∉ L := by
  have haT : a ∈ A.T := by
    rcases ha with rfl | rfl
    · exact C.k_mem
    · exact mul_mem (z_mem_T S) C.k_mem
  intro h
  have := L2K.ψX_mem_R8 (A := A) ⟨mul_mem A.t_mem_T haT, h⟩
  rw [L2K.ψX_mul A.t_mem_T haT, L2K.ψX_t, one_mul] at this
  rcases ha with rfl | rfl
  · rw [L2KD.ψX_k C] at this
    exact L2K.k8_not_mem_R8 this
  · rw [L2K.ψX_mul (z_mem_T S) C.k_mem, (ψX_z S), L2KD.ψX_k C] at this
    exact L2K.z8_mul_k8_not_mem_R8 this

end KD7

end CFSG.ComponentClassification.HSFLit
