module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Std
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Dih1
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Part

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

theorem three_le (h : Canon S P₁ P₂ z t a a₀ b₀ M) : 3 ≤ a := by
  obtain ⟨h3, -⟩ := h.data.P₁_quat
  exact h3

theorem dih1 (h : Canon S P₁ P₂ z t a a₀ b₀ M) : DihPair (a₀ * (t * a₀ * t⁻¹)⁻¹) t M :=
  ⟨h.one_le, h.rel.orderOf_dl1, h.rel.t_sq, h.rel.t_dl1⟩

theorem dih2 (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    DihPair (a₀ * (t * a₀ * t⁻¹)) (b₀ * (t * b₀ * t⁻¹) * t) M :=
  ⟨h.one_le, h.rel.orderOf_dl2, h.rel.s2_sq, h.rel.s2_dl2⟩

theorem D1_dihedral (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    IVK.IsDihedralTwoGroup ↥(D1 a₀ (t * a₀ * t⁻¹) t) (a - 1) := by
  have h3 := h.three_le
  have := isDihedralTwoGroup_sup (a - 2) (by omega) (a₀ * (t * a₀ * t⁻¹)⁻¹) t
    (by rw [h.rel.orderOf_dl1, h.hN]) h.rel.t_sq h.rel.t_dl1 h.rel.t_not_mem_dl1
  rwa [show a - 2 + 1 = a - 1 by omega] at this

theorem D2_dihedral (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    IVK.IsDihedralTwoGroup ↥(D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t) (a - 1) := by
  have h3 := h.three_le
  have := isDihedralTwoGroup_sup (a - 2) (by omega) (a₀ * (t * a₀ * t⁻¹)) (b₀ * (t * b₀ * t⁻¹) * t)
    (by rw [h.rel.orderOf_dl2, h.hN]) h.rel.s2_sq h.rel.s2_dl2 h.rel.s2_not_mem_dl2
  rwa [show a - 2 + 1 = a - 1 by omega] at this

theorem mem_K_iff (h : Canon S P₁ P₂ z t a a₀ b₀ M) {g : G} :
    g ∈ D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ↔
      ∃ d₁ ∈ D1 a₀ (t * a₀ * t⁻¹) t, ∃ d₂ ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t, g = d₁ * d₂ :=
  mem_sup_iff_of_commute h.rel.D1_D2_comm

theorem mem_HH_iff (h : Canon S P₁ P₂ z t a a₀ b₀ M) {g : G} :
    g ∈ HH t a₀ b₀ ↔ g ∈ D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ∨
      ∃ k ∈ D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t, g = k * a₀ :=
  mem_sup_zpowers_iff h.rel.a_conj_sup h.rel.a_sq_mem

theorem relIndex_K (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    (D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t).relIndex (HH t a₀ b₀) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨a₀, a_le_HH t a₀ b₀ (mem_zpowers a₀), fun g hg => ?_⟩
  by_cases hK : g ∈ D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t
  · right
    refine ⟨hK, fun hga => ?_⟩
    apply h.rel.a_not_mem_sup
    have h' := mul_mem (Subgroup.inv_mem _ hK) hga
    rwa [show g⁻¹ * (g * a₀) = a₀ by group] at h'
  · left
    refine ⟨?_, hK⟩
    rcases (h.mem_HH_iff).1 hg with hg' | ⟨k, hk, rfl⟩
    · exact absurd hg' hK
    · have e : k * a₀ * a₀ = k * (a₀ * a₀) := mul_assoc _ _ _
      rw [e]
      exact mul_mem hk h.rel.a_sq_mem

theorem D1_normal (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    ∀ s ∈ HH t a₀ b₀, ∀ d ∈ D1 a₀ (t * a₀ * t⁻¹) t, s * d * s⁻¹ ∈ D1 a₀ (t * a₀ * t⁻¹) t := by
  have hK : ∀ k ∈ D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t,
      ∀ d ∈ D1 a₀ (t * a₀ * t⁻¹) t, k * d * k⁻¹ ∈ D1 a₀ (t * a₀ * t⁻¹) t := by
    intro k hk d hd
    obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := (h.mem_K_iff).1 hk
    have c1 : d₂ * d = d * d₂ := (h.rel.D1_D2_comm d hd d₂ hd₂).symm
    have e : d₁ * d₂ * d * (d₁ * d₂)⁻¹ = d₁ * d * d₁⁻¹ := by
      calc d₁ * d₂ * d * (d₁ * d₂)⁻¹ = d₁ * (d₂ * d) * d₂⁻¹ * d₁⁻¹ := by group
        _ = d₁ * (d * d₂) * d₂⁻¹ * d₁⁻¹ := by rw [c1]
        _ = d₁ * d * d₁⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hd₁ hd) (inv_mem hd₁)
  intro s hs d hd
  rcases (h.mem_HH_iff).1 hs with hs' | ⟨k, hk, rfl⟩
  · exact hK s hs' d hd
  · have e : k * a₀ * d * (k * a₀)⁻¹ = k * (a₀ * d * a₀⁻¹) * k⁻¹ := by group
    rw [e]
    exact hK k hk _ (h.rel.a_conj_D1 d hd)

theorem unique_decomp (h : Canon S P₁ P₂ z t a a₀ b₀ M) {d₁ d₁' d₂ d₂' : G}
    (h1 : d₁ ∈ D1 a₀ (t * a₀ * t⁻¹) t) (h1' : d₁' ∈ D1 a₀ (t * a₀ * t⁻¹) t)
    (h2 : d₂ ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t)
    (h2' : d₂' ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t) (e : d₁ * d₂ = d₁' * d₂') :
    d₁ = d₁' ∧ d₂ = d₂' := by
  have e1 : d₁'⁻¹ * d₁ = d₂' * d₂⁻¹ := by
    calc d₁'⁻¹ * d₁ = d₁'⁻¹ * (d₁ * d₂) * d₂⁻¹ := by group
      _ = d₁'⁻¹ * (d₁' * d₂') * d₂⁻¹ := by rw [e]
      _ = d₂' * d₂⁻¹ := by group
  have hmem : d₁'⁻¹ * d₁ ∈ D1 a₀ (t * a₀ * t⁻¹) t ⊓ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t :=
    ⟨mul_mem (Subgroup.inv_mem _ h1') h1, by rw [e1]; exact mul_mem h2' (Subgroup.inv_mem _ h2)⟩
  rw [h.rel.D1_inf_D2, mem_bot] at hmem
  have hd1 : d₁ = d₁' := by
    calc d₁ = d₁' * (d₁'⁻¹ * d₁) := by group
      _ = d₁' := by rw [hmem, mul_one]
  refine ⟨hd1, ?_⟩
  rw [hd1] at e
  exact mul_left_cancel e

end Canon

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem xx_sq (h : Canon S P₁ P₂ z t a a₀ b₀ M) : xx t a₀ M * xx t a₀ M = 1 := h.rel.dl1_M_sq

theorem xx_mem_S (h : Canon S P₁ P₂ z t a a₀ b₀ M) : xx t a₀ M ∈ S := h.data.R_le_S h.xx_mem_R

theorem z_xx_comm (h : Canon S P₁ P₂ z t a a₀ b₀ M) : z * xx t a₀ M = xx t a₀ M * z :=
  h.data.z_cent' h.xx_mem_S

theorem z_mem_Tc (h : Canon S P₁ P₂ z t a a₀ b₀ M) : z ∈ Tc S t a₀ M :=
  (mem_Tc_iff S t a₀ M).2 ⟨h.data.z_mem, mul_inv_eq_iff_eq_mul.2 h.z_xx_comm⟩

theorem xx_mem_Tc (h : Canon S P₁ P₂ z t a a₀ b₀ M) : xx t a₀ M ∈ Tc S t a₀ M :=
  (mem_Tc_iff S t a₀ M).2 ⟨h.xx_mem_S, mul_inv_cancel_right _ _⟩

omit [Finite G] in
theorem dl2_M_eq (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    (a₀ * (t * a₀ * t⁻¹)) ^ M = xx t a₀ M * z := by
  rw [h.rel.dl2_M, ← h.hz]
  rfl

omit [Finite G] in
theorem fix_D1 (h : Canon S P₁ P₂ z t a a₀ b₀ M) {d₁ : G} (hd₁ : d₁ ∈ D1 a₀ (t * a₀ * t⁻¹) t)
    (hct : t * d₁ = d₁ * t) (hca : a₀ * d₁ * a₀⁻¹ = d₁) : d₁ = 1 ∨ d₁ = xx t a₀ M := by
  have hr := h.dih1.r_ne_one
  have e := h.dih1.centralizer_refl 0 hd₁
  rw [zpow_zero, one_mul] at e
  rcases e.1 hct.symm with e1 | e1 | e1 | e1
  · exact Or.inl e1
  · exact Or.inr e1
  · exfalso
    rw [e1, h.rel.a_t_a_inv] at hca
    exact hr (mul_right_cancel (hca.trans (one_mul t).symm))
  · exfalso
    have hx : a₀ * xx t a₀ M * a₀⁻¹ = xx t a₀ M :=
      mul_inv_eq_iff_eq_mul.2 (h.rel.commute_a_dl1_pow M).eq
    have e2 : a₀ * (xx t a₀ M * t) * a₀⁻¹ = xx t a₀ M * ((a₀ * (t * a₀ * t⁻¹)⁻¹) * t) := by
      calc a₀ * (xx t a₀ M * t) * a₀⁻¹ = (a₀ * xx t a₀ M * a₀⁻¹) * (a₀ * t * a₀⁻¹) := by group
        _ = _ := by rw [hx, h.rel.a_t_a_inv]
    rw [e1] at hca
    have e3 : xx t a₀ M * ((a₀ * (t * a₀ * t⁻¹)⁻¹) * t) = xx t a₀ M * t := by
      rw [← e2]; exact hca
    exact hr (mul_right_cancel (mul_left_cancel e3 |>.trans (one_mul t).symm))

omit [Finite G] in
theorem fix_D2 (h : Canon S P₁ P₂ z t a a₀ b₀ M) {d₂ : G}
    (hd₂ : d₂ ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t)
    (hcs : (b₀ * (t * b₀ * t⁻¹) * t) * d₂ = d₂ * (b₀ * (t * b₀ * t⁻¹) * t))
    (hca : a₀ * d₂ * a₀⁻¹ = d₂) : d₂ = 1 ∨ d₂ = xx t a₀ M * z := by
  have hr := h.dih2.r_ne_one
  have e := h.dih2.centralizer_refl 0 hd₂
  rw [zpow_zero, one_mul] at e
  rcases e.1 hcs.symm with e1 | e1 | e1 | e1
  · exact Or.inl e1
  · exact Or.inr (e1.trans h.dl2_M_eq)
  · exfalso
    rw [e1, h.rel.a_s2_a_inv] at hca
    exact hr (mul_right_cancel (hca.trans (one_mul _).symm))
  · exfalso
    have hx : a₀ * (a₀ * (t * a₀ * t⁻¹)) ^ M * a₀⁻¹ = (a₀ * (t * a₀ * t⁻¹)) ^ M :=
      mul_inv_eq_iff_eq_mul.2 (h.rel.commute_a_dl2_pow M).eq
    have e2 : a₀ * ((a₀ * (t * a₀ * t⁻¹)) ^ M * (b₀ * (t * b₀ * t⁻¹) * t)) * a₀⁻¹ =
        (a₀ * (t * a₀ * t⁻¹)) ^ M * ((a₀ * (t * a₀ * t⁻¹)) * (b₀ * (t * b₀ * t⁻¹) * t)) := by
      calc a₀ * ((a₀ * (t * a₀ * t⁻¹)) ^ M * (b₀ * (t * b₀ * t⁻¹) * t)) * a₀⁻¹
          = (a₀ * (a₀ * (t * a₀ * t⁻¹)) ^ M * a₀⁻¹) * (a₀ * (b₀ * (t * b₀ * t⁻¹) * t) * a₀⁻¹) := by
            group
        _ = _ := by rw [hx, h.rel.a_s2_a_inv]
    rw [e1] at hca
    have e3 : (a₀ * (t * a₀ * t⁻¹)) ^ M * ((a₀ * (t * a₀ * t⁻¹)) * (b₀ * (t * b₀ * t⁻¹) * t)) =
        (a₀ * (t * a₀ * t⁻¹)) ^ M * (b₀ * (t * b₀ * t⁻¹) * t) := by
      rw [← e2]; exact hca
    exact hr (mul_right_cancel (mul_left_cancel e3 |>.trans (one_mul _).symm))

theorem center_Tc (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    (center ↥(Tc S t a₀ M)).map (Tc S t a₀ M).subtype = zpowers z ⊔ zpowers (xx t a₀ M) := by
  have hd := h.data
  refine center_map_eq_of_forall ?_ ?_ ?_
  · exact sup_le (by rw [zpowers_le]; exact h.z_mem_Tc) (by rw [zpowers_le]; exact h.xx_mem_Tc)
  · intro g hg hc
    have hgH : g ∈ HH t a₀ b₀ := h.Tc_eq_HH ▸ hg
    have ht : t ∈ Tc S t a₀ M := h.HH_le_Tc (D1_le_HH t a₀ b₀ (Rel.t_mem_D1 _ _ _))
    have hs2 : b₀ * (t * b₀ * t⁻¹) * t ∈ Tc S t a₀ M :=
      h.HH_le_Tc (D2_le_HH t a₀ b₀ (Rel.s2_mem_D2 _ _ _ _ _))
    have ha : a₀ ∈ Tc S t a₀ M := h.HH_le_Tc (a_le_HH t a₀ b₀ (mem_zpowers a₀))
    have hct := hc t ht
    have hcs := hc _ hs2
    have hca := hc a₀ ha
    rcases h.mem_HH_iff.1 hgH with hK | ⟨k, hk, rfl⟩
    · obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := h.mem_K_iff.1 hK
      have hct' : t * d₂ = d₂ * t := h.rel.D1_D2_comm t (Rel.t_mem_D1 _ _ _) d₂ hd₂
      have hs2' : ∀ y ∈ D1 a₀ (t * a₀ * t⁻¹) t, y * (d₂) = d₂ * y :=
        fun y hy => h.rel.D1_D2_comm y hy d₂ hd₂
      have e1 : t * d₁ = d₁ * t := by
        have : t * d₁ * d₂ = d₁ * t * d₂ := by
          calc t * d₁ * d₂ = t * (d₁ * d₂) := mul_assoc _ _ _
            _ = d₁ * d₂ * t := hct
            _ = d₁ * (d₂ * t) := mul_assoc _ _ _
            _ = d₁ * (t * d₂) := by rw [hct']
            _ = d₁ * t * d₂ := (mul_assoc _ _ _).symm
        exact mul_right_cancel this
      have e2 : (b₀ * (t * b₀ * t⁻¹) * t) * d₂ = d₂ * (b₀ * (t * b₀ * t⁻¹) * t) := by
        have hc1 : d₁ * (b₀ * (t * b₀ * t⁻¹) * t) = (b₀ * (t * b₀ * t⁻¹) * t) * d₁ :=
          h.rel.D1_D2_comm d₁ hd₁ _ (Rel.s2_mem_D2 _ _ _ _ _)
        have : d₁ * (b₀ * (t * b₀ * t⁻¹) * t * d₂) = d₁ * (d₂ * (b₀ * (t * b₀ * t⁻¹) * t)) := by
          calc d₁ * (b₀ * (t * b₀ * t⁻¹) * t * d₂)
              = (d₁ * (b₀ * (t * b₀ * t⁻¹) * t)) * d₂ := (mul_assoc _ _ _).symm
            _ = ((b₀ * (t * b₀ * t⁻¹) * t) * d₁) * d₂ := by rw [← hc1]
            _ = (b₀ * (t * b₀ * t⁻¹) * t) * (d₁ * d₂) := mul_assoc _ _ _
            _ = d₁ * d₂ * (b₀ * (t * b₀ * t⁻¹) * t) := hcs
            _ = d₁ * (d₂ * (b₀ * (t * b₀ * t⁻¹) * t)) := mul_assoc _ _ _
        exact mul_left_cancel this
      have e3 : a₀ * d₁ * a₀⁻¹ = d₁ ∧ a₀ * d₂ * a₀⁻¹ = d₂ := by
        refine h.unique_decomp (h.rel.a_conj_D1 d₁ hd₁) hd₁ (h.rel.a_conj_D2 d₂ hd₂) hd₂ ?_
        calc a₀ * d₁ * a₀⁻¹ * (a₀ * d₂ * a₀⁻¹) = a₀ * (d₁ * d₂) * a₀⁻¹ := by group
          _ = d₁ * d₂ := mul_inv_eq_iff_eq_mul.2 hca
      have hx1 := h.fix_D1 hd₁ e1 e3.1
      have hx2 := h.fix_D2 hd₂ e2 e3.2
      have hxm : xx t a₀ M ∈ zpowers z ⊔ zpowers (xx t a₀ M) := mem_sup_right (mem_zpowers _)
      have hzm : z ∈ zpowers z ⊔ zpowers (xx t a₀ M) := mem_sup_left (mem_zpowers _)
      rcases hx1 with rfl | rfl <;> rcases hx2 with rfl | rfl
      · rw [one_mul]; exact one_mem _
      · rw [one_mul]; exact mul_mem hxm hzm
      · rw [mul_one]; exact hxm
      · have : xx t a₀ M * (xx t a₀ M * z) = z := by
          rw [← mul_assoc, h.xx_sq, one_mul]
        rw [this]; exact hzm
    · exfalso
      obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := h.mem_K_iff.1 hk
      have hrt : d₂ * (a₀ * (t * a₀ * t⁻¹)⁻¹ * t) = (a₀ * (t * a₀ * t⁻¹)⁻¹ * t) * d₂ :=
        (h.rel.D1_D2_comm _ (mul_mem (Rel.dl1_mem_D1 _ _ _) (Rel.t_mem_D1 _ _ _)) d₂ hd₂).symm
      have e1 : (d₁ * d₂ * a₀) * t * (d₁ * d₂ * a₀)⁻¹ = t := by
        rw [← hct]; exact mul_inv_cancel_right _ _
      have e2 : (d₁ * d₂ * a₀) * t * (d₁ * d₂ * a₀)⁻¹ =
          d₁ * (d₂ * (a₀ * t * a₀⁻¹) * d₂⁻¹) * d₁⁻¹ := by group
      rw [e2, h.rel.a_t_a_inv] at e1
      have e3 : d₂ * (a₀ * (t * a₀ * t⁻¹)⁻¹ * t) * d₂⁻¹ = a₀ * (t * a₀ * t⁻¹)⁻¹ * t :=
        mul_inv_eq_iff_eq_mul.2 hrt
      rw [e3] at e1
      have := h.dih1.not_conj_rot_refl hd₁ 0
      rw [zero_add, zpow_one, zpow_zero, one_mul] at this
      exact this e1
  · intro g hg d hd'
    have hdS := ((mem_Tc_iff S t a₀ M).1 hd').1
    have hdx : d * xx t a₀ M = xx t a₀ M * d :=
      mul_inv_eq_iff_eq_mul.1 ((mem_Tc_iff S t a₀ M).1 hd').2
    have hdz : d * z = z * d := (h.data.z_cent' hdS).symm
    rcases (mem_sup_of_sq_comm h.data.z_sq h.xx_sq h.z_xx_comm).1 hg with e | e | e | e
    · rw [e, one_mul, mul_one]
    · rw [e]; exact hdz
    · rw [e]; exact hdx
    · rw [e]
      calc d * (z * xx t a₀ M) = (d * z) * xx t a₀ M := (mul_assoc _ _ _).symm
        _ = (z * d) * xx t a₀ M := by rw [hdz]
        _ = z * (d * xx t a₀ M) := mul_assoc _ _ _
        _ = z * (xx t a₀ M * d) := by rw [hdx]
        _ = (z * xx t a₀ M) * d := (mul_assoc _ _ _).symm

end Canon

end Fin

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

theorem V_form (h : Canon S P₁ P₂ z t a a₀ b₀ M) {w : G}
    (hw : w ∈ Vset S (P₁ ⊔ P₂) z t (xx t a₀ M)) :
    ∃ k : ℕ, w = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t := by
  have hd := h.data
  have hc : a₀ ^ M ∈ P₁ := h.c_mem
  have hci : (a₀ ^ M)⁻¹ ∈ P₁ := inv_mem hc
  obtain ⟨-, hwZ, hwz, hxw⟩ := hw
  rcases hwZ with hz | ⟨r, hr, hwr⟩
  · exact absurd hz hwz
  obtain ⟨g₁, h1, g₂, h2, rfl⟩ := hd.mem_R_iff.1 hr
  rw [hd.part_conj_t h1 h2] at hwr
  set p := g₁ * g₂⁻¹ with hp
  have hpP : p ∈ P₁ := mul_mem h1 (inv_mem h2)
  have hpi : g₂ * g₁⁻¹ = p⁻¹ := by rw [hp]; group
  rw [hpi] at hwr
  have hpiP : p⁻¹ ∈ P₁ := inv_mem hpP
  have hxw' : xx t a₀ M * w = rr t (a₀ ^ M * p) ((a₀ ^ M)⁻¹ * p⁻¹) * t := by
    rw [hwr, h.xx_eq_rr, ← mul_assoc, hd.rr_mul hci hpP]
  rw [hxw'] at hxw
  have hcp := (hd.rrt_mem_Zc_iff (mul_mem hc hpP) (mul_mem hci hpiP)).1 hxw
  have hcomm : a₀ ^ M * p = p * a₀ ^ M := by
    have e1 : a₀ ^ M * p * (a₀ ^ M)⁻¹ * p⁻¹ = 1 := by
      calc a₀ ^ M * p * (a₀ ^ M)⁻¹ * p⁻¹ = a₀ ^ M * p * ((a₀ ^ M)⁻¹ * p⁻¹) := by group
        _ = 1 := hcp
    calc a₀ ^ M * p = a₀ ^ M * p * (a₀ ^ M)⁻¹ * p⁻¹ * (p * a₀ ^ M) := by group
      _ = p * a₀ ^ M := by rw [e1, one_mul]
  obtain ⟨k, hk | hk⟩ := h.span p hpP
  · refine ⟨k, ?_⟩
    rw [hwr, hk]
    have hcm : Commute a₀ (t * a₀ * t⁻¹) := h.rel.commute_a_a'
    unfold rr
    have e1 : t * (a₀ ^ k)⁻¹ * t⁻¹ = ((t * a₀ * t⁻¹) ^ k)⁻¹ := by
      calc t * (a₀ ^ k)⁻¹ * t⁻¹ = (t * a₀ ^ k * t⁻¹)⁻¹ := by group
        _ = ((t * a₀ * t⁻¹) ^ k)⁻¹ := by rw [conj_pow]
    rw [e1, Commute.mul_pow hcm.inv_right, inv_pow]
  · exfalso
    rw [hk] at hcomm
    have hcm : a₀ ^ M * a₀ ^ k = a₀ ^ k * a₀ ^ M := ((Commute.refl a₀).pow_pow M k).eq
    have e2 : a₀ ^ M * b₀ = b₀ * a₀ ^ M := by
      have : a₀ ^ k * (a₀ ^ M * b₀) = a₀ ^ k * (b₀ * a₀ ^ M) := by
        calc a₀ ^ k * (a₀ ^ M * b₀) = (a₀ ^ k * a₀ ^ M) * b₀ := (mul_assoc _ _ _).symm
          _ = (a₀ ^ M * a₀ ^ k) * b₀ := by rw [hcm]
          _ = a₀ ^ M * (a₀ ^ k * b₀) := mul_assoc _ _ _
          _ = (a₀ ^ k * b₀) * a₀ ^ M := hcomm
          _ = a₀ ^ k * (b₀ * a₀ ^ M) := mul_assoc _ _ _
      exact mul_left_cancel this
    have e3 : b₀ * a₀ ^ M * b₀⁻¹ = (a₀ ^ M)⁻¹ := h.qg.b_conj M
    rw [← e2, mul_inv_cancel_right] at e3
    have e4 : a₀ ^ M * a₀ ^ M = 1 := by
      calc a₀ ^ M * a₀ ^ M = (a₀ ^ M)⁻¹ * a₀ ^ M := by rw [← e3]
        _ = 1 := inv_mul_cancel _
    rw [h.c_sq] at e4
    exact hd.z_ne_one e4

end Canon

end Fin

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem a_conj_refl (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    a₀ * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) * a₀⁻¹ = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (k + 1) * t := by
  have hc : a₀ * (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * a₀⁻¹ = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k :=
    mul_inv_eq_iff_eq_mul.2 ((h.rel.commute_dl1_a.symm.zpow_right k).eq)
  calc a₀ * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) * a₀⁻¹
      = (a₀ * (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * a₀⁻¹) * (a₀ * t * a₀⁻¹) := by group
    _ = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * ((a₀ * (t * a₀ * t⁻¹)⁻¹) * t) := by
        rw [hc, h.rel.a_t_a_inv]
    _ = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (k + 1) * t := by
        rw [zpow_add_one]; exact (mul_assoc _ _ _).symm

omit [Finite G] in
theorem refl_ne_rot (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k j : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t ≠ (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ j := by
  intro e
  apply h.rel.t_not_mem_dl1
  have : t = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (j - k) := by
    calc t = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (-k) * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) := by
          rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
      _ = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (-k) * (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ j := by rw [e]
      _ = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (j - k) := by
          rw [← zpow_add]; congr 1; ring
  have hmem := zpow_mem (mem_zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹)) (j - k)
  rw [← this] at hmem
  exact hmem

omit [Finite G] in
theorem xx_eq_pow (_h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    xx t a₀ M = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ M := rfl

omit [Finite G] in
theorem xx_mem_D1 (_h : Canon S P₁ P₂ z t a a₀ b₀ M) : xx t a₀ M ∈ D1 a₀ (t * a₀ * t⁻¹) t :=
  mem_sup_left (pow_mem (mem_zpowers _) M)

omit [Finite G] in
theorem refl_mem_D1 (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t ∈ D1 a₀ (t * a₀ * t⁻¹) t := h.dih1.refl_mem_D k

omit [Finite G] in
theorem V4_le_D1 (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    zpowers (xx t a₀ M) ⊔ zpowers ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) ≤ D1 a₀ (t * a₀ * t⁻¹) t := by
  refine sup_le ?_ ?_ <;> rw [zpowers_le]
  · exact h.xx_mem_D1
  · exact h.refl_mem_D1 k

theorem Cw_eq (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    Tc S t a₀ M ⊓ centralizer ({(a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t} : Set G) =
      zpowers (xx t a₀ M) ⊔ zpowers ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) ⊔
        D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := by
  have hwD1 := h.refl_mem_D1 k
  refine le_antisymm ?_ ?_
  · rintro g ⟨hgT, hgC⟩
    have hgC' := mem_centralizer_singleton_iff.1 hgC
    have hgH : g ∈ HH t a₀ b₀ := h.Tc_eq_HH ▸ hgT
    rcases h.mem_HH_iff.1 hgH with hK | ⟨k', hk, rfl⟩
    · obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := h.mem_K_iff.1 hK
      have hd2w : d₂ * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) = ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) * d₂ :=
        (h.rel.D1_D2_comm _ hwD1 d₂ hd₂).symm
      have e1 : d₁ * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) = ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) * d₁ := by
        have : d₁ * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) * d₂ =
            ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) * d₁ * d₂ := by
          calc d₁ * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) * d₂
              = d₁ * (((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) * d₂) := mul_assoc _ _ _
            _ = d₁ * (d₂ * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t)) := by rw [hd2w]
            _ = d₁ * d₂ * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) := (mul_assoc _ _ _).symm
            _ = ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) * (d₁ * d₂) := hgC'
            _ = ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) * d₁ * d₂ := (mul_assoc _ _ _).symm
        exact mul_right_cancel this
      have hV : d₁ ∈ zpowers (xx t a₀ M) ⊔ zpowers ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) := by
        rcases (h.dih1.centralizer_refl k hd₁).1 e1 with e | e | e | e
        · rw [e]; exact one_mem _
        · rw [e]; exact mem_sup_left (mem_zpowers _)
        · rw [e]; exact mem_sup_right (mem_zpowers _)
        · rw [e]; exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
      exact mul_mem (mem_sup_left hV) (mem_sup_right hd₂)
    · exfalso
      obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := h.mem_K_iff.1 hk
      have e1 : (d₁ * d₂ * a₀) * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) * (d₁ * d₂ * a₀)⁻¹ =
          (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t := by
        rw [hgC', mul_inv_cancel_right]
      have e2 : (d₁ * d₂ * a₀) * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) * (d₁ * d₂ * a₀)⁻¹ =
          d₁ * (d₂ * (a₀ * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) * a₀⁻¹) * d₂⁻¹) * d₁⁻¹ := by group
      rw [e2, h.a_conj_refl k] at e1
      have hrt : d₂ * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (k + 1) * t) =
          ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (k + 1) * t) * d₂ :=
        (h.rel.D1_D2_comm _ (h.refl_mem_D1 (k + 1)) d₂ hd₂).symm
      have e3 : d₂ * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (k + 1) * t) * d₂⁻¹ =
          (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (k + 1) * t := mul_inv_eq_iff_eq_mul.2 hrt
      rw [e3] at e1
      exact h.dih1.not_conj_rot_refl hd₁ k e1
  · refine sup_le (sup_le ?_ ?_) ?_
    · rw [zpowers_le]
      exact ⟨h.xx_mem_Tc, mem_centralizer_singleton_iff.2 (h.dih1.rM_comm_refl k)⟩
    · rw [zpowers_le]
      exact ⟨h.HH_le_Tc (D1_le_HH t a₀ b₀ hwD1), mem_centralizer_singleton_iff.2 rfl⟩
    · intro g hg
      exact ⟨h.HH_le_Tc (D2_le_HH t a₀ b₀ hg),
        mem_centralizer_singleton_iff.2 (h.rel.D1_D2_comm _ hwD1 g hg).symm⟩

end Canon

end Fin

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem pow8 (h : Canon S P₁ P₂ z t a a₀ b₀ M) : 2 ^ (a + 1) = 8 * (2 * M) := by
  have h3 := h.three_le
  rw [h.hN, show a + 1 = (a - 2) + 3 by omega, pow_add]
  ring

omit [Finite G] in
theorem pow4 (h : Canon S P₁ P₂ z t a a₀ b₀ M) : 2 ^ (a - 1) * 4 = 2 ^ (a + 1) := by
  have h3 := h.three_le
  rw [show a + 1 = (a - 1) + 2 by omega, pow_add]
  norm_num

omit [Finite G] in
theorem w_ne_x (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t ≠ xx t a₀ M := by
  intro e
  apply h.refl_ne_rot k (M : ℤ)
  rw [zpow_natCast]
  exact e

omit [Finite G] in
theorem w_ne_one (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t ≠ 1 := by
  intro e
  apply h.refl_ne_rot k 0
  rw [zpow_zero]
  exact e

omit [Finite G] in
theorem V4_comm (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    ∀ g ∈ zpowers (xx t a₀ M), ∀ g' ∈ zpowers ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t), g * g' = g' * g := by
  intro g hg g' hg'
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hg
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hg'
  exact ((show Commute (xx t a₀ M) ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) from
    h.dih1.rM_comm_refl k).zpow_zpow i j).eq

theorem card_V4 (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    Nat.card ↥(zpowers (xx t a₀ M) ⊔ zpowers ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t)) = 4 := by
  rw [card_sup_of_commute (h.V4_comm k)
      (zpowers_inf_zpowers_of_sq h.xx_sq (h.dih1.refl_sq k) (h.w_ne_x k).symm),
    card_zpowers_of_sq h.xx_sq h.rel.dl1_M_ne_one,
    card_zpowers_of_sq (h.dih1.refl_sq k) (h.w_ne_one k)]

omit [Finite G] in
theorem V4_inf_D2 (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    (zpowers (xx t a₀ M) ⊔ zpowers ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t)) ⊓
      D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have : g ∈ D1 a₀ (t * a₀ * t⁻¹) t ⊓ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t :=
    ⟨h.V4_le_D1 k hg.1, hg.2⟩
  rw [h.rel.D1_inf_D2] at this
  exact this

theorem card_Cw (h : Canon S P₁ P₂ z t a a₀ b₀ M) (k : ℤ) :
    Nat.card ↥(Tc S t a₀ M ⊓ centralizer ({(a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t} : Set G)) =
      2 ^ (a + 1) := by
  rw [h.Cw_eq k]
  have hcomm : ∀ g ∈ zpowers (xx t a₀ M) ⊔ zpowers ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t),
      ∀ g' ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t, g * g' = g' * g :=
    fun g hg g' hg' => h.rel.D1_D2_comm g (h.V4_le_D1 k hg) g' hg'
  rw [card_sup_of_commute hcomm (h.V4_inf_D2 k), h.card_V4 k, h.rel.card_D2, h.pow8]
  ring

omit [Finite G] in
theorem refl2_eq (h : Canon S P₁ P₂ z t a a₀ b₀ M) (j : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t) =
      rr t (a₀ ^ j * b₀) (a₀ ^ j * b₀) * t := by
  have e1 : t * (a₀ ^ j * b₀) * t⁻¹ = (t * a₀ * t⁻¹) ^ j * (t * b₀ * t⁻¹) := by
    calc t * (a₀ ^ j * b₀) * t⁻¹ = (t * a₀ ^ j * t⁻¹) * (t * b₀ * t⁻¹) := by group
      _ = (t * a₀ * t⁻¹) ^ j * (t * b₀ * t⁻¹) := by rw [conj_zpow]
  have hc : b₀ * (t * a₀ * t⁻¹) ^ j = (t * a₀ * t⁻¹) ^ j * b₀ := h.rel.b_zpow_a' j
  unfold rr
  rw [e1, h.rel.dl2_zpow j]
  generalize (t * a₀ * t⁻¹) ^ j = A' at hc ⊢
  calc a₀ ^ j * A' * (b₀ * (t * b₀ * t⁻¹) * t) = a₀ ^ j * (A' * b₀) * (t * b₀ * t⁻¹) * t := by
        simp only [mul_assoc]
    _ = a₀ ^ j * (b₀ * A') * (t * b₀ * t⁻¹) * t := by rw [hc]
    _ = a₀ ^ j * b₀ * (A' * (t * b₀ * t⁻¹)) * t := by simp only [mul_assoc]

theorem x_refl2_mem_Z (h : Canon S P₁ P₂ z t a a₀ b₀ M) (j : ℤ) :
    xx t a₀ M * ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) ∈ Zc (P₁ ⊔ P₂) z t := by
  have hd := h.data
  have hc : a₀ ^ M ∈ P₁ := h.c_mem
  have hci : (a₀ ^ M)⁻¹ ∈ P₁ := inv_mem hc
  have hq : a₀ ^ j * b₀ ∈ P₁ := mul_mem (zpow_mem h.ha j) h.hb
  rw [h.refl2_eq j, h.xx_eq_rr, ← mul_assoc, hd.rr_mul hci hq]
  refine (hd.rrt_mem_Zc_iff (mul_mem hc hq) (mul_mem hci hq)).2 ?_
  have e1 : b₀ * (a₀ ^ M)⁻¹ = a₀ ^ M * b₀ := by
    have := h.rel.b_zpow_a (-(M : ℤ))
    rwa [neg_neg, zpow_neg, zpow_natCast] at this
  have e2 : b₀ * a₀ ^ j = a₀ ^ (-j) * b₀ := h.rel.b_zpow_a j
  have e3 : a₀ ^ M * a₀ ^ j = a₀ ^ j * a₀ ^ M := by
    have := ((Commute.refl a₀).zpow_zpow (M : ℤ) j).eq
    rwa [zpow_natCast] at this
  calc a₀ ^ M * (a₀ ^ j * b₀) * ((a₀ ^ M)⁻¹ * (a₀ ^ j * b₀))
      = a₀ ^ M * a₀ ^ j * (b₀ * (a₀ ^ M)⁻¹) * a₀ ^ j * b₀ := by simp only [mul_assoc]
    _ = a₀ ^ M * a₀ ^ j * (a₀ ^ M * b₀) * a₀ ^ j * b₀ := by rw [e1]
    _ = a₀ ^ M * a₀ ^ j * a₀ ^ M * (b₀ * a₀ ^ j) * b₀ := by simp only [mul_assoc]
    _ = a₀ ^ M * a₀ ^ j * a₀ ^ M * (a₀ ^ (-j) * b₀) * b₀ := by rw [e2]
    _ = a₀ ^ ((M : ℤ) + j + M + -j) * (b₀ * b₀) := by
        rw [zpow_add, zpow_add, zpow_add, zpow_natCast]
        simp only [mul_assoc]
    _ = 1 := by
        rw [h.rel.b_sq, show (M : ℤ) + j + M + -j = ((2 * M : ℕ) : ℤ) by push_cast; ring,
          zpow_natCast]
        exact h.rel.aN_sq

end Canon

end Fin

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem card_D2' (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    Nat.card ↥(D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t) = 2 ^ (a - 1) := by
  have h3 := h.three_le
  rw [h.rel.card_D2, h.hN, show a - 1 = (a - 2) + 1 by omega, pow_succ]
  ring

omit [Finite G] in
theorem refl2_ne_one (h : Canon S P₁ P₂ z t a a₀ b₀ M) (j : ℤ) :
    (a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t) ≠ 1 := by
  intro e
  apply h.dih2.refl_ne_rot h.rel.s2_not_mem_dl2 j 0
  rw [zpow_zero]
  exact e

omit [Finite G] in
theorem V4_sq (h : Canon S P₁ P₂ z t a a₀ b₀ M) {w : G} (hw : w * w = 1)
    (hxw : xx t a₀ M * w = w * xx t a₀ M) {g : G}
    (hg : g ∈ zpowers (xx t a₀ M) ⊔ zpowers w) : g * g = 1 := by
  rcases (mem_sup_of_sq_comm h.xx_sq hw hxw).1 hg with e | e | e | e
  · rw [e, one_mul]
  · rw [e]; exact h.xx_sq
  · rw [e]; exact hw
  · rw [e]
    calc xx t a₀ M * w * (xx t a₀ M * w) = xx t a₀ M * (w * xx t a₀ M) * w := by simp only [mul_assoc]
      _ = xx t a₀ M * (xx t a₀ M * w) * w := by rw [hxw]
      _ = (xx t a₀ M * xx t a₀ M) * (w * w) := by simp only [mul_assoc]
      _ = 1 := by rw [h.xx_sq, hw, mul_one]

theorem rigid (h : Canon S P₁ P₂ z t a a₀ b₀ M) {w : G} {k : ℤ}
    (hw : w = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ k * t) {U : Subgroup G}
    (hU : U ≤ Tc S t a₀ M ⊓ centralizer ({w} : Set G)) (hcard : Nat.card ↥U = 2 ^ (a - 1))
    (hinf : ∀ y ∈ U, y ∈ zpowers (xx t a₀ M) ⊔ zpowers w → y = 1)
    (hcls : ∀ d ∈ U, d * d = 1 → d ≠ 1 → d ∈ Xc (P₁ ⊔ P₂) z t ∧ w * d ∈ Xc (P₁ ⊔ P₂) z t ∧
      xx t a₀ M * w * d ∈ Xc (P₁ ⊔ P₂) z t ∧ xx t a₀ M * d ∈ Zc (P₁ ⊔ P₂) z t) :
    U = D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := by
  have hd := h.data
  have hwD1 : w ∈ D1 a₀ (t * a₀ * t⁻¹) t := by rw [hw]; exact h.refl_mem_D1 k
  have hww : w * w = 1 := by rw [hw]; exact h.dih1.refl_sq k
  have hxw : xx t a₀ M * w = w * xx t a₀ M := by rw [hw]; exact h.dih1.rM_comm_refl k
  have hCw : Tc S t a₀ M ⊓ centralizer ({w} : Set G) =
      (zpowers (xx t a₀ M) ⊔ zpowers w) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := by
    rw [hw]; exact h.Cw_eq k
  have hcardC : Nat.card ↥(Tc S t a₀ M ⊓ centralizer ({w} : Set G)) = 2 ^ (a + 1) := by
    rw [hw]; exact h.card_Cw k
  have hV4card : Nat.card ↥(zpowers (xx t a₀ M) ⊔ zpowers w) = 4 := by rw [hw]; exact h.card_V4 k
  have hV4D1 : zpowers (xx t a₀ M) ⊔ zpowers w ≤ D1 a₀ (t * a₀ * t⁻¹) t := by
    rw [hw]; exact h.V4_le_D1 k
  have hVcomm : ∀ g ∈ zpowers (xx t a₀ M), ∀ g' ∈ zpowers w, g * g' = g' * g := by
    rw [hw]; exact h.V4_comm k
  have hUcomm : ∀ u' ∈ U, ∀ f ∈ zpowers (xx t a₀ M) ⊔ zpowers w, u' * f = f * u' := by
    intro u' hu' f hf
    have hu'C := hU hu'
    have hux : u' * xx t a₀ M = xx t a₀ M * u' :=
      mul_inv_eq_iff_eq_mul.1 ((mem_Tc_iff S t a₀ M).1 hu'C.1).2
    have huw : u' * w = w * u' := mem_centralizer_singleton_iff.1 hu'C.2
    have hle : zpowers (xx t a₀ M) ⊔ zpowers w ≤ centralizer ({u'} : Set G) := by
      refine sup_le ?_ ?_ <;> rw [zpowers_le, mem_centralizer_singleton_iff]
      · exact hux.symm
      · exact huw.symm
    exact (mem_centralizer_singleton_iff.1 (hle hf)).symm
  have hUinf : U ⊓ (zpowers (xx t a₀ M) ⊔ zpowers w) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    exact hinf y hy.1 hy.2
  have hUV : U ⊔ (zpowers (xx t a₀ M) ⊔ zpowers w) = Tc S t a₀ M ⊓ centralizer ({w} : Set G) := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [hCw]
      exact sup_le (hCw ▸ hU) le_sup_left
    · rw [card_sup_of_commute hUcomm hUinf, hcard, hV4card, hcardC]
      exact (h.pow4).ge
  have key : ∀ e ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t, e * e = 1 → e ≠ 1 →
      xx t a₀ M * e ∈ Zc (P₁ ⊔ P₂) z t →
      ∀ g ∈ zpowers (xx t a₀ M) ⊔ zpowers w, g * e ∈ U → e ∈ U := by
    intro e heD2 hesq hene hCF g hg hge
    have hgsq : g * g = 1 := h.V4_sq hww hxw hg
    have hgD1 := hV4D1 hg
    have hxD1 : xx t a₀ M ∈ D1 a₀ (t * a₀ * t⁻¹) t := h.xx_mem_D1
    have hcommge : g * e = e * g := h.rel.D1_D2_comm g hgD1 e heD2
    have hxe : xx t a₀ M * e = e * xx t a₀ M := h.rel.D1_D2_comm _ hxD1 e heD2
    have hdsq : (g * e) * (g * e) = 1 := by
      calc g * e * (g * e) = g * (e * g) * e := by simp only [mul_assoc]
        _ = g * (g * e) * e := by rw [hcommge]
        _ = (g * g) * (e * e) := by simp only [mul_assoc]
        _ = 1 := by rw [hgsq, hesq, mul_one]
    have hdne : g * e ≠ 1 := by
      intro h1
      apply hene
      have h2 : e = g⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h3 : e ∈ D1 a₀ (t * a₀ * t⁻¹) t ⊓ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t :=
        ⟨by rw [h2]; exact hV4D1 (Subgroup.inv_mem _ hg), heD2⟩
      rw [h.rel.D1_inf_D2] at h3
      exact h3
    have hysq : (xx t a₀ M * e) * (xx t a₀ M * e) = 1 := by
      calc xx t a₀ M * e * (xx t a₀ M * e) = xx t a₀ M * (e * xx t a₀ M) * e := by simp only [mul_assoc]
        _ = xx t a₀ M * (xx t a₀ M * e) * e := by rw [hxe]
        _ = (xx t a₀ M * xx t a₀ M) * (e * e) := by simp only [mul_assoc]
        _ = 1 := by rw [h.xx_sq, hesq, mul_one]
    have hyne : xx t a₀ M * e ≠ 1 := by
      intro h1
      apply hene
      have h2 : e = (xx t a₀ M)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h3 : e ∈ D1 a₀ (t * a₀ * t⁻¹) t ⊓ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t :=
        ⟨by rw [h2]; exact Subgroup.inv_mem _ hxD1, heD2⟩
      rw [h.rel.D1_inf_D2] at h3
      exact h3
    have hyS : xx t a₀ M * e ∈ S := mul_mem h.xx_mem_S (h.D2_le_S heD2)
    have hno : xx t a₀ M * e ∈ Xc (P₁ ⊔ P₂) z t → False := fun hX =>
      (hd.partition _ hyS hysq hyne).2 ⟨hCF, hX⟩
    rcases (mem_sup_of_sq_comm h.xx_sq hww hxw).1 hg with e1 | e1 | e1 | e1
    · rw [e1, one_mul] at hge
      exact hge
    · exfalso
      rw [e1] at hge hdsq hdne
      exact hno (hcls _ hge hdsq hdne).1
    · exfalso
      rw [e1] at hge hdsq hdne
      have h4 := (hcls _ hge hdsq hdne).2.2.1
      have e5 : xx t a₀ M * w * (w * e) = xx t a₀ M * e := by
        calc xx t a₀ M * w * (w * e) = xx t a₀ M * ((w * w) * e) := by simp only [mul_assoc]
          _ = xx t a₀ M * e := by rw [hww, one_mul]
      rw [e5] at h4
      exact hno h4
    · exfalso
      rw [e1] at hge hdsq hdne
      have h4 := (hcls _ hge hdsq hdne).2.1
      have e5 : w * (xx t a₀ M * w * e) = xx t a₀ M * e := by
        calc w * (xx t a₀ M * w * e) = (w * xx t a₀ M) * w * e := by simp only [mul_assoc]
          _ = (xx t a₀ M * w) * w * e := by rw [hxw]
          _ = xx t a₀ M * (w * w) * e := by simp only [mul_assoc]
          _ = xx t a₀ M * e := by rw [hww, mul_one]
      rw [e5] at h4
      exact hno h4
  have hrefl : ∀ j : ℤ, (a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t) ∈ U := by
    intro j
    have heD2 := h.dih2.refl_mem_D j
    have hCe : (a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t) ∈
        Tc S t a₀ M ⊓ centralizer ({w} : Set G) := by
      rw [hCw]; exact mem_sup_right heD2
    rw [← hUV] at hCe
    obtain ⟨u', hu', f, hf, hef⟩ := (mem_sup_iff_of_commute hUcomm).1 hCe
    have hfe : f * ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) =
        ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) * f :=
      h.rel.D1_D2_comm f (hV4D1 hf) _ heD2
    refine key _ heD2 (h.dih2.refl_sq j) (h.refl2_ne_one j) (h.x_refl2_mem_Z j) f⁻¹ (Subgroup.inv_mem _ hf) ?_
    have e1 : f⁻¹ * ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) = u' := by
      have e2 : u' = ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) * f⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]; exact hef.symm
      rw [e2]
      exact ((show Commute f _ from hfe).inv_left).eq
    rw [e1]
    exact hu'
  have hs2U : b₀ * (t * b₀ * t⁻¹) * t ∈ U := by
    have := hrefl 0
    rwa [zpow_zero, one_mul] at this
  have hDU : D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ≤ U := by
    intro g hg
    obtain ⟨i, hi | hi⟩ := h.dih2.mem_iff.1 hg
    · rw [hi]
      have e1 : (a₀ * (t * a₀ * t⁻¹)) ^ i =
          ((a₀ * (t * a₀ * t⁻¹)) ^ i * (b₀ * (t * b₀ * t⁻¹) * t)) * (b₀ * (t * b₀ * t⁻¹) * t) := by
        calc (a₀ * (t * a₀ * t⁻¹)) ^ i
            = (a₀ * (t * a₀ * t⁻¹)) ^ i * (b₀ * (t * b₀ * t⁻¹) * t) *
                (b₀ * (t * b₀ * t⁻¹) * t)⁻¹ := (mul_inv_cancel_right _ _).symm
          _ = _ := by rw [h.rel.s2_inv]
      rw [e1]
      exact mul_mem (hrefl i) hs2U
    · rw [hi]
      exact hrefl i
  exact (Subgroup.eq_of_le_of_card_ge hDU (by rw [hcard, h.card_D2'])).symm

end Canon

end Fin

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
