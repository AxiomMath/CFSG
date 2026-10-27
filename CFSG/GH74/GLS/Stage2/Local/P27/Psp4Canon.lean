module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Grp

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

structure Canon (S P₁ P₂ : Subgroup G) (z t : G) (a : ℕ) (a₀ b₀ : G) (M : ℕ) : Prop where
  data : Data S P₁ P₂ z t a
  ha : a₀ ∈ P₁
  hb : b₀ ∈ P₁
  one_le : 1 ≤ M
  hN : 2 * M = 2 ^ (a - 2)
  qg : QG a₀ b₀ (2 * M)
  span : ∀ x ∈ P₁, ∃ k : ℕ, x = a₀ ^ k ∨ x = a₀ ^ k * b₀

@[expose] def xx (t a₀ : G) (M : ℕ) : G := (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ M

namespace Data

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ}

theorem conj_rr (h : Data S P₁ P₂ z t a) {p q c d : G} (hp : p ∈ P₁) (hq : q ∈ P₁) (hc : c ∈ P₁)
    (hd : d ∈ P₁) : rr t p q * rr t c d * (rr t p q)⁻¹ = rr t (p * c * p⁻¹) (q * d * q⁻¹) := by
  rw [h.rr_inv hp hq, h.rr_mul hq hc, h.rr_mul (mul_mem hq hd) (inv_mem hp)]

theorem rr_p_one (t p : G) : rr t p 1 = p := by simp [rr]

theorem z_mul_rr_left (z t p q : G) : z * rr t p q = rr t (z * p) q := by
  simp only [rr, mul_assoc]

theorem z_mul_rr_right (h : Data S P₁ P₂ z t a) {p q : G} (hp : p ∈ P₁) :
    z * rr t p q = rr t p (z * q) := by
  unfold rr
  rw [Data.σ_mul, h.σ_z, ← mul_assoc, h.z_cent' (h.P₁_le hp), mul_assoc]

end Data

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

theorem hz (h : Canon S P₁ P₂ z t a a₀ b₀ M) : z = a₀ ^ (2 * M) :=
  (h.data.rel_of_gens h.ha h.hb h.one_le h.qg h.span).1

theorem rel (h : Canon S P₁ P₂ z t a a₀ b₀ M) : Rel a₀ b₀ (t * a₀ * t⁻¹) (t * b₀ * t⁻¹) t M :=
  (h.data.rel_of_gens h.ha h.hb h.one_le h.qg h.span).2

theorem a'_mem (h : Canon S P₁ P₂ z t a a₀ b₀ M) : t * a₀ * t⁻¹ ∈ P₂ := h.data.σ_mem₁ h.ha

theorem b'_mem (h : Canon S P₁ P₂ z t a a₀ b₀ M) : t * b₀ * t⁻¹ ∈ P₂ := h.data.σ_mem₁ h.hb

theorem c_mem (h : Canon S P₁ P₂ z t a a₀ b₀ M) : a₀ ^ M ∈ P₁ := pow_mem h.ha M

theorem c_sq (h : Canon S P₁ P₂ z t a a₀ b₀ M) : a₀ ^ M * a₀ ^ M = z := by
  rw [← pow_add, ← two_mul, h.hz]

theorem c_inv (h : Canon S P₁ P₂ z t a a₀ b₀ M) : (a₀ ^ M)⁻¹ = z * a₀ ^ M := by
  symm
  apply eq_inv_of_mul_eq_one_left
  calc z * a₀ ^ M * a₀ ^ M = z * (a₀ ^ M * a₀ ^ M) := by rw [mul_assoc]
    _ = 1 := by rw [h.c_sq, h.data.z_sq]

theorem P₁_conj_c (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    ∀ g ∈ P₁, g * a₀ ^ M * g⁻¹ = a₀ ^ M ∨ g * a₀ ^ M * g⁻¹ = z * a₀ ^ M := by
  intro g hg
  obtain ⟨k, hk | hk⟩ := h.span g hg
  · left
    rw [hk]
    have : Commute (a₀ ^ k) (a₀ ^ M) := (Commute.refl a₀).pow_pow k M
    exact mul_inv_eq_iff_eq_mul.2 this.eq
  · right
    rw [hk]
    have h1 : b₀ * a₀ ^ M * b₀⁻¹ = (a₀ ^ M)⁻¹ := by rw [h.qg.b_conj M]
    have h2 : Commute (a₀ ^ k) (a₀ ^ M) := (Commute.refl a₀).pow_pow k M
    calc a₀ ^ k * b₀ * a₀ ^ M * (a₀ ^ k * b₀)⁻¹
        = a₀ ^ k * (b₀ * a₀ ^ M * b₀⁻¹) * (a₀ ^ k)⁻¹ := by group
      _ = a₀ ^ k * (a₀ ^ M)⁻¹ * (a₀ ^ k)⁻¹ := by rw [h1]
      _ = (a₀ ^ M)⁻¹ := by
        have := mul_inv_eq_iff_eq_mul.2 (h2.inv_right.eq)
        rw [this]
      _ = z * a₀ ^ M := h.c_inv

theorem xx_eq_rr (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    xx t a₀ M = rr t (a₀ ^ M) (a₀ ^ M)⁻¹ := by
  have hc : Commute a₀ (t * a₀ * t⁻¹)⁻¹ := h.rel.commute_a_a'.inv_right
  unfold xx rr
  rw [Commute.mul_pow hc, inv_pow, conj_pow, Data.σ_inv]

end Canon

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

theorem rr_conj_xx (h : Canon S P₁ P₂ z t a a₀ b₀ M) {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    rr t p q * xx t a₀ M * (rr t p q)⁻¹ = xx t a₀ M ∨
      rr t p q * xx t a₀ M * (rr t p q)⁻¹ = xx t a₀ M * z := by
  have hc : a₀ ^ M ∈ P₁ := h.c_mem
  have hci : (a₀ ^ M)⁻¹ ∈ P₁ := inv_mem hc
  have hd := h.data
  have hzP : ∀ g ∈ P₁, z * g = g * z := fun g hg => hd.z_cent' (hd.P₁_le hg)
  have hzr : z * rr t (a₀ ^ M) (a₀ ^ M)⁻¹ = rr t (a₀ ^ M) (a₀ ^ M)⁻¹ * z :=
    hd.z_cent' (hd.R_le_S (hd.rr_mem_R hc hci))
  have hf : ∀ g ∈ P₁, (g * a₀ ^ M * g⁻¹ = a₀ ^ M → g * (a₀ ^ M)⁻¹ * g⁻¹ = (a₀ ^ M)⁻¹) ∧
      (g * a₀ ^ M * g⁻¹ = z * a₀ ^ M → g * (a₀ ^ M)⁻¹ * g⁻¹ = z * (a₀ ^ M)⁻¹) := by
    intro g hg
    have e : g * (a₀ ^ M)⁻¹ * g⁻¹ = (g * a₀ ^ M * g⁻¹)⁻¹ := by group
    refine ⟨fun h1 => by rw [e, h1], fun h1 => ?_⟩
    rw [e, h1, mul_inv_rev, hd.z_inv, ← hzP _ hci]
  rw [h.xx_eq_rr, hd.conj_rr hp hq hc hci]
  rcases h.P₁_conj_c p hp with e1 | e1 <;> rcases h.P₁_conj_c q hq with f1 | f1
  · left
    rw [e1, (hf q hq).1 f1]
  · right
    rw [e1, (hf q hq).2 f1, ← hd.z_mul_rr_right hc, hzr]
  · right
    rw [e1, (hf q hq).1 f1, ← Data.z_mul_rr_left, hzr]
  · left
    rw [e1, (hf q hq).2 f1]
    exact ((hd.rr_eq_iff hc hci (mul_mem hd.z_mem₁ hc) (mul_mem hd.z_mem₁ hci)).2
      (Or.inr ⟨rfl, rfl⟩)).symm

theorem xx_mem_R (h : Canon S P₁ P₂ z t a a₀ b₀ M) : xx t a₀ M ∈ P₁ ⊔ P₂ := by
  rw [h.xx_eq_rr]
  exact h.data.rr_mem_R h.c_mem (inv_mem h.c_mem)

omit [Finite G] in
theorem t_xx (h : Canon S P₁ P₂ z t a a₀ b₀ M) : t * xx t a₀ M * t⁻¹ = xx t a₀ M := by
  unfold xx
  rw [h.rel.t_dl1_pow M]
  exact inv_eq_of_mul_eq_one_right h.rel.dl1_M_sq

theorem uhyp (h : Canon S P₁ P₂ z t a a₀ b₀ M) : UHyp S P₁ P₂ z (xx t a₀ M) where
  mem := h.xx_mem_R
  sq := h.rel.dl1_M_sq
  ne_one := h.rel.dl1_M_ne_one
  ne_z := by rw [h.hz]; exact h.rel.dl1_M_ne_z
  norm := by
    intro s hs
    obtain ⟨p, hp, q, hq, hs'⟩ := (h.data.mem_S_iff).1 hs
    rcases hs' with rfl | rfl
    · exact h.rr_conj_xx hp hq
    · have e : (rr t p q * t) * xx t a₀ M * (rr t p q * t)⁻¹ =
          rr t p q * xx t a₀ M * (rr t p q)⁻¹ := by
        calc (rr t p q * t) * xx t a₀ M * (rr t p q * t)⁻¹
            = rr t p q * (t * xx t a₀ M * t⁻¹) * (rr t p q)⁻¹ := by group
          _ = rr t p q * xx t a₀ M * (rr t p q)⁻¹ := by rw [h.t_xx]
      rw [e]
      exact h.rr_conj_xx hp hq

theorem b₀_xx (h : Canon S P₁ P₂ z t a a₀ b₀ M) : b₀ * xx t a₀ M * b₀⁻¹ = xx t a₀ M * z := by
  have hc : a₀ ^ M ∈ P₁ := h.c_mem
  have hci : (a₀ ^ M)⁻¹ ∈ P₁ := inv_mem hc
  have hd := h.data
  have hzr : z * rr t (a₀ ^ M) (a₀ ^ M)⁻¹ = rr t (a₀ ^ M) (a₀ ^ M)⁻¹ * z :=
    hd.z_cent' (hd.R_le_S (hd.rr_mem_R hc hci))
  have e1 : b₀ * a₀ ^ M * b₀⁻¹ = z * a₀ ^ M := by rw [h.qg.b_conj M, h.c_inv]
  have e := hd.conj_rr h.hb (one_mem P₁) hc hci
  rw [Data.rr_p_one, inv_one, mul_one, one_mul, e1] at e
  rw [h.xx_eq_rr, e, ← Data.z_mul_rr_left, hzr]

end Canon

end Fin

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
