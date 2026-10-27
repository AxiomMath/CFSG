module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Canon

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

@[expose] def HH (t a₀ b₀ : G) : Subgroup G :=
  D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ⊔ zpowers a₀

@[expose] def Tc (S : Subgroup G) (t a₀ : G) (M : ℕ) : Subgroup G :=
  S ⊓ centralizer ({xx t a₀ M} : Set G)

theorem conj_le_of_gens {r s : G} {H : Subgroup G} (g : G) (hr : g * r * g⁻¹ ∈ H)
    (hs : g * s * g⁻¹ ∈ H) : ∀ x ∈ zpowers r ⊔ zpowers s, g * x * g⁻¹ ∈ H := by
  have : zpowers r ⊔ zpowers s ≤ H.comap (MulAut.conj g).toMonoidHom := by
    refine sup_le ?_ ?_ <;> rw [zpowers_le]
    · exact hr
    · exact hs
  exact fun x hx => this hx

theorem mem_Tc_iff (S : Subgroup G) (t a₀ : G) (M : ℕ) {g : G} :
    g ∈ Tc S t a₀ M ↔ g ∈ S ∧ g * xx t a₀ M * g⁻¹ = xx t a₀ M := by
  unfold Tc
  rw [mem_inf, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

theorem D1_le_HH (t a₀ b₀ : G) : D1 a₀ (t * a₀ * t⁻¹) t ≤ HH t a₀ b₀ :=
  le_sup_of_le_left le_sup_left

theorem D2_le_HH (t a₀ b₀ : G) : D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ≤ HH t a₀ b₀ :=
  le_sup_of_le_left le_sup_right

theorem a_le_HH (t a₀ b₀ : G) : zpowers a₀ ≤ HH t a₀ b₀ := le_sup_right

namespace Rel

variable {a b a' b' t : G} {M : ℕ}

theorem b_conj_a (h : Rel a b a' b' t M) : b * a * b⁻¹ = a⁻¹ := by
  simpa using h.qg.b_conj 1

theorem b_conj_a' (h : Rel a b a' b' t M) : b * a' * b⁻¹ = a' :=
  mul_inv_eq_iff_eq_mul.2 h.c_ba

theorem b_conj_dl1 (h : Rel a b a' b' t M) : b * (a * a'⁻¹) * b⁻¹ = (a * a')⁻¹ := by
  have e1 := h.b_conj_a
  have e2 := h.b_conj_a'
  have hc := h.commute_a_a'
  calc b * (a * a'⁻¹) * b⁻¹ = (b * a * b⁻¹) * (b * a' * b⁻¹)⁻¹ := by group
    _ = a⁻¹ * a'⁻¹ := by rw [e1, e2]
    _ = (a * a')⁻¹ := by rw [mul_inv_rev]; exact hc.inv_inv.eq

theorem b_conj_dl2 (h : Rel a b a' b' t M) : b * (a * a') * b⁻¹ = (a * a'⁻¹)⁻¹ := by
  have e1 := h.b_conj_a
  have e2 := h.b_conj_a'
  have hc := h.commute_a_a'
  calc b * (a * a') * b⁻¹ = (b * a * b⁻¹) * (b * a' * b⁻¹) := by group
    _ = a⁻¹ * a' := by rw [e1, e2]
    _ = (a * a'⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]; exact hc.inv_left.eq

theorem t_binv (h : Rel a b a' b' t M) : t * b⁻¹ = b'⁻¹ * t := by
  calc t * b⁻¹ = b'⁻¹ * (b' * t) * b⁻¹ := by group
    _ = b'⁻¹ * (t * b) * b⁻¹ := by rw [h.tb]
    _ = b'⁻¹ * t := by group

theorem b_conj_s2 (h : Rel a b a' b' t M) : b * (b * b' * t) * b⁻¹ = a ^ (2 * M) * t := by
  calc b * (b * b' * t) * b⁻¹ = (b * b) * b' * (t * b⁻¹) := by group
    _ = (b * b) * b' * (b'⁻¹ * t) := by rw [h.t_binv]
    _ = (b * b) * t := by group
    _ = a ^ (2 * M) * t := by rw [h.b_sq]

theorem b_conj_t (h : Rel a b a' b' t M) : b * t * b⁻¹ = a ^ (2 * M) * (b * b' * t) := by
  have hz : a ^ (2 * M) = b * b := h.b_sq.symm
  have hz' : a ^ (2 * M) = b' * b' := h.b'_sq.symm
  have hzb : a ^ (2 * M) * b = b * a ^ (2 * M) := by rw [hz]; group
  have hb' : b' * (a ^ (2 * M) * b') = 1 := by
    calc b' * (a ^ (2 * M) * b') = a ^ (2 * M) * (b' * b') := by rw [hz']; group
      _ = 1 := by rw [h.b'_sq]; exact h.aN_sq
  have e : b'⁻¹ = a ^ (2 * M) * b' := inv_eq_of_mul_eq_one_right hb'
  calc b * t * b⁻¹ = b * (t * b⁻¹) := by rw [mul_assoc]
    _ = b * (b'⁻¹ * t) := by rw [h.t_binv]
    _ = b * (a ^ (2 * M) * b') * t := by rw [e]; group
    _ = (b * a ^ (2 * M)) * b' * t := by group
    _ = (a ^ (2 * M) * b) * b' * t := by rw [hzb]
    _ = a ^ (2 * M) * (b * b' * t) := by group

end Rel

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

theorem a'_mem_S (h : Canon S P₁ P₂ z t a a₀ b₀ M) : t * a₀ * t⁻¹ ∈ S := h.data.P₂_le h.a'_mem

theorem b'_mem_S (h : Canon S P₁ P₂ z t a a₀ b₀ M) : t * b₀ * t⁻¹ ∈ S := h.data.P₂_le h.b'_mem

theorem a_mem_S (h : Canon S P₁ P₂ z t a a₀ b₀ M) : a₀ ∈ S := h.data.P₁_le h.ha

theorem b_mem_S (h : Canon S P₁ P₂ z t a a₀ b₀ M) : b₀ ∈ S := h.data.P₁_le h.hb

theorem D1_le_S (h : Canon S P₁ P₂ z t a a₀ b₀ M) : D1 a₀ (t * a₀ * t⁻¹) t ≤ S := by
  refine sup_le ?_ ?_ <;> rw [zpowers_le]
  · exact mul_mem h.a_mem_S (inv_mem h.a'_mem_S)
  · exact h.data.t_mem

theorem D2_le_S (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ≤ S := by
  refine sup_le ?_ ?_ <;> rw [zpowers_le]
  · exact mul_mem h.a_mem_S h.a'_mem_S
  · exact mul_mem (mul_mem h.b_mem_S h.b'_mem_S) h.data.t_mem

theorem HH_le_S (h : Canon S P₁ P₂ z t a a₀ b₀ M) : HH t a₀ b₀ ≤ S :=
  sup_le (sup_le h.D1_le_S h.D2_le_S) (by rw [zpowers_le]; exact h.a_mem_S)

theorem D1_le_cent (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    D1 a₀ (t * a₀ * t⁻¹) t ≤ centralizer ({xx t a₀ M} : Set G) := by
  refine sup_le ?_ ?_ <;> rw [zpowers_le] <;> rw [mem_centralizer_singleton_iff]
  · exact ((Commute.refl (a₀ * (t * a₀ * t⁻¹)⁻¹)).pow_right M).eq
  · exact commute_of_conj h.t_xx

theorem D2_le_cent (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ≤ centralizer ({xx t a₀ M} : Set G) := by
  refine sup_le ?_ ?_ <;> rw [zpowers_le] <;> rw [mem_centralizer_singleton_iff]
  · exact (h.rel.commute_dl1_dl2.symm.pow_right M).eq
  · exact (h.rel.commute_s2_dl1.pow_right M).eq

theorem a_le_cent (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    zpowers a₀ ≤ centralizer ({xx t a₀ M} : Set G) := by
  rw [zpowers_le, mem_centralizer_singleton_iff]
  exact (h.rel.commute_dl1_a.symm.pow_right M).eq

theorem HH_le_Tc (h : Canon S P₁ P₂ z t a a₀ b₀ M) : HH t a₀ b₀ ≤ Tc S t a₀ M :=
  le_inf h.HH_le_S (sup_le (sup_le h.D1_le_cent h.D2_le_cent) h.a_le_cent)

theorem xx_mul_z_ne (h : Canon S P₁ P₂ z t a a₀ b₀ M) : xx t a₀ M * z ≠ xx t a₀ M := by
  intro e
  have : z = 1 := mul_left_cancel (e.trans (mul_one _).symm)
  exact h.data.z_ne_one this

theorem b_conj_HH (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    ∀ x ∈ HH t a₀ b₀, b₀ * x * b₀⁻¹ ∈ HH t a₀ b₀ := by
  have hz : a₀ ^ (2 * M) ∈ HH t a₀ b₀ := a_le_HH t a₀ b₀ (pow_mem (mem_zpowers a₀) _)
  have hle : HH t a₀ b₀ ≤ (HH t a₀ b₀).comap (MulAut.conj b₀).toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact fun x hx => conj_le_of_gens (H := HH t a₀ b₀) (r := a₀ * (t * a₀ * t⁻¹)⁻¹) (s := t) b₀
        (by rw [h.rel.b_conj_dl1]; exact inv_mem (D2_le_HH t a₀ b₀ (Rel.dl2_mem_D2 _ _ _ _ _)))
        (by rw [h.rel.b_conj_t]; exact mul_mem hz (D2_le_HH t a₀ b₀ (Rel.s2_mem_D2 _ _ _ _ _))) x hx
    · exact fun x hx => conj_le_of_gens (H := HH t a₀ b₀) (r := a₀ * (t * a₀ * t⁻¹))
        (s := b₀ * (t * b₀ * t⁻¹) * t) b₀
        (by rw [h.rel.b_conj_dl2]; exact inv_mem (D1_le_HH t a₀ b₀ (Rel.dl1_mem_D1 _ _ _)))
        (by rw [h.rel.b_conj_s2]; exact mul_mem hz (D1_le_HH t a₀ b₀ (Rel.t_mem_D1 _ _ _))) x hx
    · rw [zpowers_le]
      show b₀ * a₀ * b₀⁻¹ ∈ HH t a₀ b₀
      rw [h.rel.b_conj_a]
      exact inv_mem (a_le_HH t a₀ b₀ (mem_zpowers a₀))
  exact fun x hx => hle hx

theorem b_sq_mem (h : Canon S P₁ P₂ z t a a₀ b₀ M) : b₀ * b₀ ∈ HH t a₀ b₀ := by
  rw [h.rel.b_sq]
  exact a_le_HH t a₀ b₀ (pow_mem (mem_zpowers a₀) _)

end Canon

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

theorem relIndex_Tc (h : Canon S P₁ P₂ z t a a₀ b₀ M) : (Tc S t a₀ M).relIndex S = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨b₀, h.b_mem_S, fun s hs => ?_⟩
  have hd := h.data
  have hzs : ∀ g ∈ S, z * g = g * z := fun g hg => hd.z_cent' hg
  have hxne : xx t a₀ M * z ≠ xx t a₀ M := by
    intro e
    have : z = 1 := mul_left_cancel (e.trans (mul_one _).symm)
    exact hd.z_ne_one this
  have hsz : s * z * s⁻¹ = z := by
    rw [hd.z_cent s hs, mul_assoc, mul_inv_cancel, mul_one]
  have hb := h.b₀_xx
  have e1 : ∀ y : G, s * b₀ * y * (s * b₀)⁻¹ = s * (b₀ * y * b₀⁻¹) * s⁻¹ := fun y => by group
  rcases h.uhyp.norm s hs with hn | hn
  ·
    right
    refine ⟨(mem_Tc_iff S t a₀ M).2 ⟨hs, hn⟩, fun hmem => ?_⟩
    have := ((mem_Tc_iff S t a₀ M).1 hmem).2
    rw [e1, hb] at this
    have e2 : s * (xx t a₀ M * z) * s⁻¹ = xx t a₀ M * z := by
      calc s * (xx t a₀ M * z) * s⁻¹ = (s * xx t a₀ M * s⁻¹) * (s * z * s⁻¹) := by group
        _ = xx t a₀ M * z := by rw [hn, hsz]
    exact hxne (e2.symm.trans this)
  · left
    refine ⟨(mem_Tc_iff S t a₀ M).2 ⟨mul_mem hs h.b_mem_S, ?_⟩, fun hmem => ?_⟩
    · rw [e1, hb]
      calc s * (xx t a₀ M * z) * s⁻¹ = (s * xx t a₀ M * s⁻¹) * (s * z * s⁻¹) := by group
        _ = (xx t a₀ M * z) * z := by rw [hn, hsz]
        _ = xx t a₀ M := by rw [mul_assoc, hd.z_sq, mul_one]
    · have := ((mem_Tc_iff S t a₀ M).1 hmem).2
      rw [hn] at this
      exact hxne this

theorem S_le_sup (h : Canon S P₁ P₂ z t a a₀ b₀ M) : S ≤ HH t a₀ b₀ ⊔ zpowers b₀ := by
  intro s hs
  have hP₁ : ∀ p ∈ P₁, p ∈ HH t a₀ b₀ ⊔ zpowers b₀ := by
    intro p hp
    obtain ⟨k, rfl | rfl⟩ := h.span p hp
    · exact mem_sup_left (a_le_HH t a₀ b₀ (pow_mem (mem_zpowers a₀) k))
    · exact mul_mem (mem_sup_left (a_le_HH t a₀ b₀ (pow_mem (mem_zpowers a₀) k)))
        (mem_sup_right (mem_zpowers b₀))
  have ht : t ∈ HH t a₀ b₀ ⊔ zpowers b₀ := mem_sup_left (D1_le_HH t a₀ b₀ (Rel.t_mem_D1 _ _ _))
  obtain ⟨p, hp, q, hq, hs' | hs'⟩ := h.data.mem_S_iff.1 hs
  · rw [hs']
    exact mul_mem (hP₁ p hp) (mul_mem (mul_mem ht (hP₁ q hq)) (inv_mem ht))
  · rw [hs']
    exact mul_mem (mul_mem (hP₁ p hp) (mul_mem (mul_mem ht (hP₁ q hq)) (inv_mem ht))) ht

theorem b_not_mem_Tc (h : Canon S P₁ P₂ z t a a₀ b₀ M) : b₀ ∉ Tc S t a₀ M := by
  intro hb
  have := ((mem_Tc_iff S t a₀ M).1 hb).2
  rw [h.b₀_xx] at this
  exact h.xx_mul_z_ne this

theorem Tc_eq_HH (h : Canon S P₁ P₂ z t a a₀ b₀ M) : Tc S t a₀ M = HH t a₀ b₀ := by
  refine le_antisymm (fun g hg => ?_) h.HH_le_Tc
  have hmem := h.S_le_sup ((mem_Tc_iff S t a₀ M).1 hg).1
  rw [mem_sup_zpowers_iff h.b_conj_HH h.b_sq_mem] at hmem
  rcases hmem with hH | ⟨k, hk, rfl⟩
  · exact hH
  · exfalso
    apply h.b_not_mem_Tc
    have : b₀ = k⁻¹ * (k * b₀) := by group
    rw [this]
    exact mul_mem (inv_mem (h.HH_le_Tc hk)) hg

end Canon

omit [Finite G] in
theorem Data.exists_canon {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} (h : Data S P₁ P₂ z t a) :
    ∃ (a₀ b₀ : G) (M : ℕ), Canon S P₁ P₂ z t a a₀ b₀ M := by
  obtain ⟨a₀, b₀, M, ha, hb, hM, hN, hqg, hspan⟩ := h.exists_gens
  exact ⟨a₀, b₀, M, ⟨h, ha, hb, hM, hN, hqg, hspan⟩⟩

end Fin

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
