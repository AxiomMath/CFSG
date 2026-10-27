module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS

variable {G : Type} [Group G] {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ}

section PartNoFin

namespace Data

theorem part_z_comm₁ (h : Data S P₁ P₂ z t a) {p : G} (hp : p ∈ P₁) : z * p = p * z :=
  h.z_cent' (h.P₁_le hp)

theorem part_z_comm_t (h : Data S P₁ P₂ z t a) : z * t = t * z := h.z_cent' h.t_mem

theorem part_mul_rr (s w p q : G) : w * rr s p q = rr s (w * p) q := by
  unfold rr
  simp only [mul_assoc]

theorem part_mul_eq_z_comm (h : Data S P₁ P₂ z t a) {p q : G} (hp : p ∈ P₁) (hpq : p * q = z) :
    q * p = z := by
  calc q * p = p⁻¹ * (p * q) * p := by group
    _ = p⁻¹ * (z * p) := by rw [hpq, mul_assoc]
    _ = p⁻¹ * (p * z) := by rw [h.part_z_comm₁ hp]
    _ = z := by group

theorem part_rrt_sq (h : Data S P₁ P₂ z t a) {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    (rr t p q * t) * (rr t p q * t) = rr t (p * q) (q * p) := by
  calc (rr t p q * t) * (rr t p q * t) = rr t p q * (t * rr t p q) * t := by simp only [mul_assoc]
    _ = rr t p q * (rr t q p * t) * t := by rw [h.rr_mul_t hp hq]
    _ = (rr t p q * rr t q p) * (t * t) := by simp only [mul_assoc]
    _ = rr t p q * rr t q p := by rw [h.t_inv, mul_one]
    _ = rr t (p * q) (q * p) := h.rr_mul hq hq

theorem part_conj_t (h : Data S P₁ P₂ z t a) {g₁ g₂ : G} (h1 : g₁ ∈ P₁) (h2 : g₂ ∈ P₁) :
    rr t g₁ g₂ * t * (rr t g₁ g₂)⁻¹ = rr t (g₁ * g₂⁻¹) (g₂ * g₁⁻¹) * t := by
  calc rr t g₁ g₂ * t * (rr t g₁ g₂)⁻¹ = rr t g₁ g₂ * (t * rr t g₁⁻¹ g₂⁻¹) := by
        rw [h.rr_inv h1 h2, mul_assoc]
    _ = rr t g₁ g₂ * (rr t g₂⁻¹ g₁⁻¹ * t) := by rw [h.rr_mul_t (inv_mem h1) (inv_mem h2)]
    _ = (rr t g₁ g₂ * rr t g₂⁻¹ g₁⁻¹) * t := by rw [mul_assoc]
    _ = rr t (g₁ * g₂⁻¹) (g₂ * g₁⁻¹) * t := by rw [h.rr_mul h2 (inv_mem h2)]

theorem rrt_sq_iff (h : Data S P₁ P₂ z t a) {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    (rr t p q * t) * (rr t p q * t) = 1 ↔ p * q = 1 ∨ p * q = z := by
  have e : (rr t p q * t) * (rr t p q * t) = 1 ↔ rr t (p * q) (q * p) = rr t 1 1 := by
    rw [h.part_rrt_sq hp hq, rr_one]
  rw [e, h.rr_eq_iff (mul_mem hp hq) (mul_mem hq hp) (one_mem _) (one_mem _)]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact Or.inl h1.symm
    · refine Or.inr ?_
      calc p * q = z⁻¹ * (z * (p * q)) := by group
        _ = z := by rw [← h1, mul_one, h.z_inv]
  · rintro (h1 | h1)
    · exact Or.inl ⟨h1.symm, (mul_eq_one_comm.1 h1).symm⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [h1, h.z_sq]
      · rw [h.part_mul_eq_z_comm hp h1, h.z_sq]

theorem mem_Zc_of_mem_R (h : Data S P₁ P₂ z t a) {y : G} (hy : y ∈ P₁ ⊔ P₂) :
    y ∈ Zc (P₁ ⊔ P₂) z t ↔ y = z := by
  constructor
  · rintro (hz | ⟨r, hr, hyr⟩)
    · exact hz
    · exfalso
      apply h.t_not
      have e : t = r⁻¹ * y * r := by rw [hyr]; group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hr) hy) hr
  · intro hyz
    rw [hyz]
    exact Or.inl (Set.mem_singleton z)

theorem mem_Xc_of_mem_R (h : Data S P₁ P₂ z t a) {y : G} (hy : y ∈ P₁ ⊔ P₂) :
    y ∈ Xc (P₁ ⊔ P₂) z t ↔ (y * y = 1 ∧ y ≠ 1 ∧ y ≠ z) := by
  constructor
  · rintro (⟨-, h2⟩ | ⟨r, hr, hyr⟩)
    · exact h2
    · exfalso
      apply h.t_not
      have e : t * z = r⁻¹ * y * r := by rw [hyr]; group
      have e' : t = (r⁻¹ * y * r) * z⁻¹ := by
        calc t = (t * z) * z⁻¹ := by group
          _ = (r⁻¹ * y * r) * z⁻¹ := by rw [e]
      rw [e']
      exact mul_mem (mul_mem (mul_mem (inv_mem hr) hy) hr) (inv_mem (mem_sup_left h.z_mem₁))
  · intro hy'
    exact Or.inl ⟨hy, hy'⟩

end Data

end PartNoFin

section PartFin

variable [Finite G]

namespace Data

theorem part_conj_tz (h : Data S P₁ P₂ z t a) {g₁ g₂ : G} (h1 : g₁ ∈ P₁) (h2 : g₂ ∈ P₁) :
    rr t g₁ g₂ * (t * z) * (rr t g₁ g₂)⁻¹ = rr t (z * (g₁ * g₂⁻¹)) (g₂ * g₁⁻¹) * t := by
  have hρ : rr t g₁ g₂ ∈ S := h.R_le_S (h.rr_mem_R h1 h2)
  calc rr t g₁ g₂ * (t * z) * (rr t g₁ g₂)⁻¹
      = rr t g₁ g₂ * (z * t) * (rr t g₁ g₂)⁻¹ := by rw [h.part_z_comm_t]
    _ = (rr t g₁ g₂ * z) * t * (rr t g₁ g₂)⁻¹ := by simp only [mul_assoc]
    _ = (z * rr t g₁ g₂) * t * (rr t g₁ g₂)⁻¹ := by rw [h.z_cent' hρ]
    _ = z * (rr t g₁ g₂ * t * (rr t g₁ g₂)⁻¹) := by simp only [mul_assoc]
    _ = z * (rr t (g₁ * g₂⁻¹) (g₂ * g₁⁻¹) * t) := by rw [h.part_conj_t h1 h2]
    _ = (z * rr t (g₁ * g₂⁻¹) (g₂ * g₁⁻¹)) * t := by rw [mul_assoc]
    _ = rr t (z * (g₁ * g₂⁻¹)) (g₂ * g₁⁻¹) * t := by rw [part_mul_rr]

theorem rrt_mem_Zc_iff (h : Data S P₁ P₂ z t a) {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    rr t p q * t ∈ Zc (P₁ ⊔ P₂) z t ↔ p * q = 1 := by
  constructor
  · rintro (hz | ⟨r, hr, hy⟩)
    · exfalso
      have hz' : rr t p q * t = z := hz
      apply h.t_not
      have e : t = (rr t p q)⁻¹ * z := by rw [← hz']; group
      rw [e]
      exact mul_mem (inv_mem (h.rr_mem_R hp hq)) (mem_sup_left h.z_mem₁)
    · obtain ⟨g₁, h1, g₂, h2, rfl⟩ := h.mem_R_iff.1 hr
      rw [h.part_conj_t h1 h2] at hy
      have hrr : rr t p q = rr t (g₁ * g₂⁻¹) (g₂ * g₁⁻¹) := mul_right_cancel hy
      rcases (h.rr_eq_iff hp hq (mul_mem h1 (inv_mem h2)) (mul_mem h2 (inv_mem h1))).1 hrr with
        ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2]
        group
      · have e3 : z * p * (z * q) = 1 := by
          rw [← e1, ← e2]
          group
        have e4 : z * p * (z * q) = p * q := by
          calc z * p * (z * q) = p * z * (z * q) := by rw [h.part_z_comm₁ hp]
            _ = p * (z * z) * q := by simp only [mul_assoc]
            _ = p * q := by rw [h.z_sq, mul_one]
        exact e4.symm.trans e3
  · intro hpq
    refine Or.inr ⟨rr t p 1, h.rr_mem_R hp (one_mem _), ?_⟩
    rw [h.part_conj_t hp (one_mem _), inv_one, mul_one, one_mul,
      ← eq_inv_of_mul_eq_one_right hpq]

theorem rrt_mem_Xc_iff (h : Data S P₁ P₂ z t a) {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    rr t p q * t ∈ Xc (P₁ ⊔ P₂) z t ↔ p * q = z := by
  constructor
  · rintro (⟨hR, -⟩ | ⟨r, hr, hy⟩)
    · exfalso
      apply h.t_not
      have e : t = (rr t p q)⁻¹ * (rr t p q * t) := by group
      rw [e]
      exact mul_mem (inv_mem (h.rr_mem_R hp hq)) hR
    · obtain ⟨g₁, h1, g₂, h2, rfl⟩ := h.mem_R_iff.1 hr
      rw [h.part_conj_tz h1 h2] at hy
      have hrr : rr t p q = rr t (z * (g₁ * g₂⁻¹)) (g₂ * g₁⁻¹) := mul_right_cancel hy
      rcases (h.rr_eq_iff hp hq (mul_mem h.z_mem₁ (mul_mem h1 (inv_mem h2)))
        (mul_mem h2 (inv_mem h1))).1 hrr with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2]
        group
      · have e3 : g₁ * g₂⁻¹ = p := mul_left_cancel e1
        have e4 : p * (z * q) = 1 := by
          rw [← e3, ← e2]
          group
        have e5 : p * (z * q) = z * (p * q) := by
          calc p * (z * q) = p * z * q := by rw [mul_assoc]
            _ = z * p * q := by rw [h.part_z_comm₁ hp]
            _ = z * (p * q) := by rw [mul_assoc]
        have e6 : z * (p * q) = 1 := e5.symm.trans e4
        calc p * q = z⁻¹ * (z * (p * q)) := by group
          _ = z := by rw [e6, mul_one, h.z_inv]
  · intro hpq
    refine Or.inr ⟨rr t p 1, h.rr_mem_R hp (one_mem _), ?_⟩
    rw [h.part_conj_tz hp (one_mem _), inv_one, mul_one, one_mul]
    have hq1 : q = p⁻¹ * z := by
      calc q = p⁻¹ * (p * q) := by group
        _ = p⁻¹ * z := by rw [hpq]
    have hq2 : p⁻¹ = z * q := by
      calc p⁻¹ = p⁻¹ * (z * z) := by rw [h.z_sq, mul_one]
        _ = p⁻¹ * z * z := by rw [mul_assoc]
        _ = z * p⁻¹ * z := by rw [h.part_z_comm₁ (inv_mem hp)]
        _ = z * (p⁻¹ * z) := by rw [mul_assoc]
        _ = z * q := by rw [hq1]
    have hrr : rr t p q = rr t (z * p) p⁻¹ :=
      (h.rr_eq_iff hp hq (mul_mem h.z_mem₁ hp) (inv_mem hp)).2 (Or.inr ⟨rfl, hq2⟩)
    rw [hrr]

theorem partition (h : Data S P₁ P₂ z t a) :
    ∀ y ∈ S, y * y = 1 → y ≠ 1 →
      (y ∈ Zc (P₁ ⊔ P₂) z t ∨ y ∈ Xc (P₁ ⊔ P₂) z t) ∧
        ¬ (y ∈ Zc (P₁ ⊔ P₂) z t ∧ y ∈ Xc (P₁ ⊔ P₂) z t) := by
  intro y hy hy2 hy1
  obtain ⟨p, hp, q, hq, hyy | hyy⟩ := h.mem_S_iff.1 hy
  · have hyR : y ∈ P₁ ⊔ P₂ := hyy ▸ h.rr_mem_R hp hq
    by_cases hyz : y = z
    · refine ⟨Or.inl ((h.mem_Zc_of_mem_R hyR).2 hyz), ?_⟩
      rintro ⟨-, hX⟩
      exact ((h.mem_Xc_of_mem_R hyR).1 hX).2.2 hyz
    · refine ⟨Or.inr ((h.mem_Xc_of_mem_R hyR).2 ⟨hy2, hy1, hyz⟩), ?_⟩
      rintro ⟨hZ, -⟩
      exact hyz ((h.mem_Zc_of_mem_R hyR).1 hZ)
  · subst hyy
    rcases (h.rrt_sq_iff hp hq).1 hy2 with h1 | h1
    · refine ⟨Or.inl ((h.rrt_mem_Zc_iff hp hq).2 h1), ?_⟩
      rintro ⟨-, hX⟩
      exact h.z_ne_one (((h.rrt_mem_Xc_iff hp hq).1 hX).symm.trans h1)
    · refine ⟨Or.inr ((h.rrt_mem_Xc_iff hp hq).2 h1), ?_⟩
      rintro ⟨hZ, -⟩
      exact h.z_ne_one (h1.symm.trans ((h.rrt_mem_Zc_iff hp hq).1 hZ))

end Data

end PartFin

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
