module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NI

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
private theorem conj_conj_eq_self_of_sq {G : Type} [Group G] {g w : G} (hg : g * g = 1) :
    g * (g * w * g⁻¹) * g⁻¹ = w := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [hginv]
  calc g * (g * w * g) * g = (g * g) * w * (g * g) := by group
    _ = w := by rw [hg]; group

namespace Ctx4Z

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

theorem zpowers_tau_cent_Y {u : G} (hu : u ∈ zpowers tau) {a : G}
    (ha : a ∈ ctxYq t tau x₁ x₂ rho) : u * a = a * u := by
  have h : tau ∈ Subgroup.centralizer ({a} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hz.tau_cent_Y a ha)
  exact mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le.mpr h hu)

theorem E8_normalizes_W : ∀ c ∈ closure ({t, tau, lam} : Set G), ∀ w ∈ ctxWN t tau x₁ x₂ rho,
    c * w * c⁻¹ ∈ ctxWN t tau x₁ x₂ rho := by
  intro c hc w hw
  have hgen : ({t, tau, lam} : Set G) ⊆
      Subgroup.normalizer ((ctxWN t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Subgroup.mem_set_normalizer_iff.mpr fun w =>
        ⟨fun hw => hz.t_conj_ctxWN hw, fun hw => by
          rw [← conj_conj_eq_self_of_sq (w := w) hz.t_mul_self]; exact hz.t_conj_ctxWN hw⟩
    · exact Subgroup.mem_set_normalizer_iff.mpr fun w =>
        ⟨fun hw => hz.tau_conj_ctxWN hw, fun hw => by
          rw [← conj_conj_eq_self_of_sq (w := w) hz.tau_mul_self]; exact hz.tau_conj_ctxWN hw⟩
    · exact Subgroup.mem_set_normalizer_iff.mpr fun w =>
        ⟨fun hw => hz.lam_conj_ctxWN hw, fun hw => by
          rw [← conj_conj_eq_self_of_sq (w := w) hz.lam_mul_self]; exact hz.lam_conj_ctxWN hw⟩
  have hcnorm : c ∈ Subgroup.normalizer ((ctxWN t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_closure.mp hc _ hgen
  exact (Subgroup.mem_set_normalizer_iff.mp hcnorm) w |>.mp hw

theorem E8_inf_ctxCQ : ∀ g ∈ closure ({t, tau, lam} : Set G),
    g ∈ ctxCQ t tau x₁ x₂ rho → g = 1 := by
  intro g hgE hgC
  have hcommY : ∀ a ∈ ctxYq t tau x₁ x₂ rho, g * a = a * g :=
    fun a ha => (mem_centralizer_iff.mp hgC a (hz.Y_le_Q ha)).symm
  rcases z4_mem_zpowers_of_mul_self hz.tau_mul_self (hz.E8_cent_Y g hgE hcommY) with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hgC) hz.tau_not_mem_ctxCQ

theorem inf_E8_W :
    ctxWN t tau x₁ x₂ rho ⊓ closure ({t, tau, lam} : Set G) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  exact hz.E8_inf_ctxCQ x hx.2 (ctxWN_le_ctxCQ t tau x₁ x₂ rho hx.1)

theorem mem_ctxE0N_iff {x : G} :
    x ∈ ctxE0N t tau x₁ x₂ rho ↔
      x ∈ ctxWN t tau x₁ x₂ rho ∨ ∃ w ∈ ctxWN t tau x₁ x₂ rho, x = w * tau := by
  have hnorm : ∀ k ∈ zpowers tau, ∀ h ∈ ctxWN t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxWN t tau x₁ x₂ rho := by
    intro k hk h hh
    rcases z4_mem_zpowers_of_mul_self hz.tau_mul_self hk with rfl | rfl
    · simpa using hh
    · exact hz.tau_conj_ctxWN hh
  constructor
  · intro hx
    unfold ctxE0N at hx
    obtain ⟨h, hh, k, hk, rfl⟩ :=
      mem_sup_of_normalizes (A := ctxWN t tau x₁ x₂ rho) (C := zpowers tau) hnorm hx
    rcases z4_mem_zpowers_of_mul_self hz.tau_mul_self hk with rfl | rfl
    · exact Or.inl (by simpa using hh)
    · exact Or.inr ⟨h, hh, rfl⟩
  · rintro (hw | ⟨w, hw, rfl⟩)
    · exact Subgroup.mem_sup_left hw
    · exact Subgroup.mul_mem_sup hw (Subgroup.mem_zpowers tau)

theorem E0_le_cent_Y : ∀ e ∈ ctxE0N t tau x₁ x₂ rho, ∀ a ∈ ctxYq t tau x₁ x₂ rho,
    e * a = a * e := by
  intro e he a ha
  rcases hz.mem_ctxE0N_iff.mp he with heW | ⟨w, hw, rfl⟩
  · exact ctxCQ_comm (ctxWN_le_ctxCQ t tau x₁ x₂ rho heW) (hz.Y_le_Q ha)
  · calc (w * tau) * a = w * (tau * a) := by group
      _ = w * (a * tau) := by rw [hz.tau_cent_Y a ha]
      _ = (w * a) * tau := by group
      _ = (a * w) * tau := by
        rw [ctxCQ_comm (ctxWN_le_ctxCQ t tau x₁ x₂ rho hw) (hz.Y_le_Q ha)]
      _ = a * (w * tau) := by group

theorem t_conj_ctxE0N : ∀ e ∈ ctxE0N t tau x₁ x₂ rho, t * e * t⁻¹ ∈ ctxE0N t tau x₁ x₂ rho := by
  intro e he
  rcases hz.mem_ctxE0N_iff.mp he with heW | ⟨w, hw, rfl⟩
  · exact hz.mem_ctxE0N_iff.mpr (Or.inl (hz.t_conj_ctxWN heW))
  · apply hz.mem_ctxE0N_iff.mpr
    refine Or.inr ⟨t * w * t⁻¹, hz.t_conj_ctxWN hw, ?_⟩
    rw [show t * (w * tau) * t⁻¹ = (t * w * t⁻¹) * tau from by
      calc t * (w * tau) * t⁻¹ = (t * w * t⁻¹) * (t * tau * t⁻¹) := by group
        _ = (t * w * t⁻¹) * tau := by rw [hz.t_comm_tau]; group]

theorem E8_inf_E0 : ∀ g ∈ closure ({t, tau, lam} : Set G), g ∈ ctxE0N t tau x₁ x₂ rho →
    g ∈ zpowers tau := by
  intro g hgE hgE0
  rcases hz.mem_ctxE0N_iff.mp hgE0 with hgW | ⟨w, hw, rfl⟩
  · have hbot : g ∈ (⊥ : Subgroup G) := by
      rw [← hz.inf_E8_W]
      exact ⟨hgW, hgE⟩
    rw [Subgroup.mem_bot] at hbot
    rw [hbot]
    exact Subgroup.one_mem _
  · have htauE : tau ∈ closure ({t, tau, lam} : Set G) := Subgroup.subset_closure (by simp)
    have hwE : w ∈ closure ({t, tau, lam} : Set G) := by
      have h1 : w = (w * tau) * tau⁻¹ := by group
      rw [h1]
      exact Subgroup.mul_mem _ hgE (Subgroup.inv_mem _ htauE)
    have hbot : w ∈ (⊥ : Subgroup G) := by
      rw [← hz.inf_E8_W]
      exact ⟨hw, hwE⟩
    rw [Subgroup.mem_bot] at hbot
    rw [hbot, one_mul]
    exact Subgroup.mem_zpowers tau

theorem t_not_mem_E0 : t ∉ ctxE0N t tau x₁ x₂ rho := by
  intro ht
  have htE : t ∈ closure ({t, tau, lam} : Set G) := Subgroup.subset_closure (by simp)
  rcases z4_mem_zpowers_of_mul_self hz.tau_mul_self (hz.E8_inf_E0 t htE ht) with h1 | h1
  · exact hz.t_ne_one h1
  · exact hz.t_ne_tau h1

theorem lam_not_mem_E0 : lam ∉ ctxE0N t tau x₁ x₂ rho := by
  intro hl
  have hlE : lam ∈ closure ({t, tau, lam} : Set G) := Subgroup.subset_closure (by simp)
  have hzpt := hz.E8_inf_E0 lam hlE hl
  have hy : x₁ ^ 2 ∈ ctxYq t tau x₁ x₂ rho := hz.V_le_Y hz.y_mem_V
  have h1 : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by
    rw [hz.zpowers_tau_cent_Y hzpt hy, mul_assoc, mul_inv_cancel, mul_one]
  rw [hz.nGood.lam_conj_y] at h1
  exact hz.y_ne_x₂_sq h1.symm

theorem tlam_not_mem_E0 : t * lam ∉ ctxE0N t tau x₁ x₂ rho := by
  intro hl
  have htE : t ∈ closure ({t, tau, lam} : Set G) := Subgroup.subset_closure (by simp)
  have hlE : lam ∈ closure ({t, tau, lam} : Set G) := Subgroup.subset_closure (by simp)
  have htlamE : t * lam ∈ closure ({t, tau, lam} : Set G) := Subgroup.mul_mem _ htE hlE
  have hzpt := hz.E8_inf_E0 (t * lam) htlamE hl
  have hy : x₁ ^ 2 ∈ ctxYq t tau x₁ x₂ rho := hz.V_le_Y hz.y_mem_V
  have h1 : (t * lam) * x₁ ^ 2 * (t * lam)⁻¹ = x₁ ^ 2 := by
    rw [hz.zpowers_tau_cent_Y hzpt hy, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : (t * lam) * x₁ ^ 2 * (t * lam)⁻¹ = x₂ ^ 2 := by
    rw [hz.t_lam_comm]; exact hz.sigma_y
  rw [h2] at h1
  exact hz.y_ne_x₂_sq h1.symm

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
