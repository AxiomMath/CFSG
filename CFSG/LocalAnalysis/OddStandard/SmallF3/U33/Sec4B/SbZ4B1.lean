module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4B0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem schur_V {y z w ρ σ a b : G} (hy : y * y = 1) (hz : z * z = 1) (hyz : y * z = w)
    (hzy : z * y = w) (hw1 : w ≠ 1) (hyz' : y ≠ z)
    (ha : a = 1 ∨ a = y ∨ a = z ∨ a = w)
    (hσy : σ * y * σ⁻¹ = w) (hσz : σ * z * σ⁻¹ = z) (hσw : σ * w * σ⁻¹ = y)
    (hb : b = σ * a * σ⁻¹)
    (hρ : (ρ * y * ρ⁻¹ = w ∧ ρ * w * ρ⁻¹ = z ∧ ρ * z * ρ⁻¹ = y ∧ b = ρ * a * ρ⁻¹) ∨
      (ρ * y * ρ⁻¹ = z ∧ ρ * z * ρ⁻¹ = w ∧ ρ * w * ρ⁻¹ = y ∧ a * b = ρ * a * ρ⁻¹)) :
    (a = 1 ∧ b = 1) ∨ (a = y ∧ b = w) := by
  have hyw : y * w = z := by rw [← hyz, ← mul_assoc, hy, one_mul]
  have hwy : w * y = z := by rw [← hzy, mul_assoc, hy, mul_one]
  rcases ha with ha | ha | ha | ha
  · left; refine ⟨ha, ?_⟩; rw [hb, ha]; group
  · right; exact ⟨ha, by rw [hb, ha, hσy]⟩
  · exfalso
    have hbz : b = z := by rw [hb, ha, hσz]
    rcases hρ with ⟨_, _, h3, h4⟩ | ⟨_, h2, _, h4⟩
    · rw [ha, h3] at h4; exact hyz' (h4.symm.trans hbz)
    · rw [ha, h2, hbz, hz] at h4; exact hw1 h4.symm
  · exfalso
    have hby : b = y := by rw [hb, ha, hσw]
    rcases hρ with ⟨_, h2, _, h4⟩ | ⟨_, _, h3, h4⟩
    · rw [ha, h2] at h4; exact hyz' (hby.symm.trans h4)
    · rw [ha, hby, hwy, h3] at h4; exact hyz' h4.symm

namespace Ctx4Q

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem lam_mem_L : lam ∈ L := by
  have h : lam ∈ S ⊓ L := by rw [hc.inf_eq]; exact subset_closure (by simp)
  exact h.2

theorem t_lam_comm : t * lam = lam * t :=
  (mem_centralizer_iff.mp hc.hyp.mem_centralizer lam hc.lam_mem_L).symm

theorem lam_mul_self : lam * lam = 1 := by
  have h1 := pow_orderOf_eq_one lam
  rw [hc.wreath.ord_lam] at h1
  simpa [pow_two] using h1

theorem rho_pow_three : rho ^ 3 = 1 := by
  have h1 := pow_orderOf_eq_one rho
  rwa [hc.ord_rho] at h1

theorem sigma_sq : (lam * t) * (lam * t) = 1 :=
  calc lam * t * (lam * t) = lam * (t * lam) * t := by group
    _ = lam * (lam * t) * t := by rw [hc.t_lam_comm]
    _ = (lam * lam) * (t * t) := by group
    _ = 1 := by rw [hc.lam_mul_self, hc.t_mul_self, one_mul]

theorem sigma_rho : (lam * t) * rho * (lam * t)⁻¹ = rho⁻¹ := by
  have h : t * rho * t⁻¹ = rho := by rw [← hc.rho_comm_t]; group
  calc (lam * t) * rho * (lam * t)⁻¹ = lam * (t * rho * t⁻¹) * lam⁻¹ := by group
    _ = lam * rho * lam⁻¹ := by rw [h]
    _ = rho⁻¹ := hc.lam_rho

theorem sigma_comm_tau : (lam * t) * tau = tau * (lam * t) :=
  calc lam * t * tau = lam * (t * tau) := by group
    _ = lam * (tau * t) := by rw [hc.t_comm_tau]
    _ = (lam * tau) * t := by group
    _ = (tau * lam) * t := by rw [hc.tau_lam]
    _ = tau * (lam * t) := by group

theorem sigma_comm_t : (lam * t) * t = t * (lam * t) :=
  calc lam * t * t = (lam * t) * t := rfl
    _ = (t * lam) * t := by rw [hc.t_lam_comm]
    _ = t * (lam * t) := by group

theorem sigma_mem_M : lam * t ∈ ctxM t tau x₁ x₂ :=
  mul_mem hc.lam_mem_M hc.t_mem_M

theorem t_comm_V : ∀ v ∈ fourGrp x₁ x₂, t * v = v * t := by
  have h : t ∈ ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [← hc.O_eq_CV]; exact hc.t_mem_O
  intro v hv
  exact (mem_centralizer_iff.mp h.2 v hv).symm

theorem tau_comm_V : ∀ v ∈ fourGrp x₁ x₂, tau * v = v * tau := by
  have h : tau ∈ ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [← hc.O_eq_CV]; exact hc.tau_mem_O
  intro v hv
  exact (mem_centralizer_iff.mp h.2 v hv).symm

theorem y_mem_V : x₁ ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)

theorem z_mem_V : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)

theorem w_mem_V : x₂ ^ 2 ∈ fourGrp x₁ x₂ := by
  rw [hc.x₂_sq]; exact mul_mem hc.y_mem_V hc.z_mem_V

theorem y_comm_z : x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 :=
  ((Commute.refl x₁).mul_right hc.x₁_comm_x₂).pow_pow 2 2

theorem mem_V_iff (a : G) :
    a ∈ fourGrp x₁ x₂ ↔ a = 1 ∨ a = x₁ ^ 2 ∨ a = (x₁ * x₂) ^ 2 ∨ a = x₂ ^ 2 := by
  have h := S4B.mem_closure_pair_of_invol (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2) (x := a)
    (by rw [← pow_two]; exact hc.y_sq) (by rw [← pow_two]; exact hc.z_sq) hc.y_comm_z
  rw [← hc.x₂_sq] at h
  exact h

theorem y_ne_z : x₁ ^ 2 ≠ (x₁ * x₂) ^ 2 := fun h => by
  apply hc.x₂_sq_ne_one
  rw [hc.x₂_sq, ← h, ← pow_two]; exact hc.y_sq

theorem z_ne_one : (x₁ * x₂) ^ 2 ≠ 1 := fun h => by
  apply hc.y_ne_x₂_sq
  rw [hc.x₂_sq, h, mul_one]

theorem y_ne_w : x₁ ^ 2 ≠ x₂ ^ 2 := hc.y_ne_x₂_sq

theorem z_ne_w : (x₁ * x₂) ^ 2 ≠ x₂ ^ 2 := fun h => by
  apply hc.y_ne_one
  have h2 : x₁ ^ 2 * (x₁ * x₂) ^ 2 = 1 * (x₁ * x₂) ^ 2 := by rw [← hc.x₂_sq, ← h, one_mul]
  exact mul_right_cancel h2

theorem lam_conj_x₂ : lam * x₂ * lam⁻¹ = x₁ :=
  calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by rw [hc.wreath.conj_x₁]
    _ = (lam * lam) * x₁ * (lam * lam)⁻¹ := by group
    _ = x₁ := by rw [hc.lam_mul_self]; group

theorem sigma_y : (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = x₂ ^ 2 := by
  have h : t * x₁ ^ 2 * t⁻¹ = x₁ ^ 2 := by rw [hc.t_comm_V _ hc.y_mem_V]; group
  calc (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = lam * (t * x₁ ^ 2 * t⁻¹) * lam⁻¹ := by group
    _ = lam * x₁ ^ 2 * lam⁻¹ := by rw [h]
    _ = (lam * x₁ * lam⁻¹) ^ 2 := conj_pow.symm
    _ = x₂ ^ 2 := by rw [hc.wreath.conj_x₁]

theorem sigma_z : (lam * t) * (x₁ * x₂) ^ 2 * (lam * t)⁻¹ = (x₁ * x₂) ^ 2 := by
  have h : t * (x₁ * x₂) ^ 2 * t⁻¹ = (x₁ * x₂) ^ 2 := by rw [hc.t_comm_V _ hc.z_mem_V]; group
  calc (lam * t) * (x₁ * x₂) ^ 2 * (lam * t)⁻¹ = lam * (t * (x₁ * x₂) ^ 2 * t⁻¹) * lam⁻¹ := by
        group
    _ = lam * (x₁ * x₂) ^ 2 * lam⁻¹ := by rw [h]
    _ = (lam * (x₁ * x₂) * lam⁻¹) ^ 2 := conj_pow.symm
    _ = (x₂ * x₁) ^ 2 := by
        rw [show lam * (x₁ * x₂) * lam⁻¹ = (lam * x₁ * lam⁻¹) * (lam * x₂ * lam⁻¹) by group,
          hc.wreath.conj_x₁, hc.lam_conj_x₂]
    _ = (x₁ * x₂) ^ 2 := by rw [hc.x₁_comm_x₂]

theorem sigma_w : (lam * t) * x₂ ^ 2 * (lam * t)⁻¹ = x₁ ^ 2 := by
  have h : t * x₂ ^ 2 * t⁻¹ = x₂ ^ 2 := by rw [hc.t_comm_V _ hc.w_mem_V]; group
  calc (lam * t) * x₂ ^ 2 * (lam * t)⁻¹ = lam * (t * x₂ ^ 2 * t⁻¹) * lam⁻¹ := by group
    _ = lam * x₂ ^ 2 * lam⁻¹ := by rw [h]
    _ = (lam * x₂ * lam⁻¹) ^ 2 := conj_pow.symm
    _ = x₁ ^ 2 := by rw [hc.lam_conj_x₂]

theorem rho_conj_V {a : G} (ha : a ∈ fourGrp x₁ x₂) : rho * a * rho⁻¹ ∈ fourGrp x₁ x₂ :=
  hc.normal_V.2 rho hc.rho_mem_M a ha

theorem rho_fpf_V {a : G} (ha : a ∈ fourGrp x₁ x₂) (h : rho * a * rho⁻¹ = a) : a = 1 := by
  have h1 : a ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
    ⟨hc.V_le_Q ha, mem_centralizer_iff.mpr fun g hg => by
      rw [Set.mem_singleton_iff.mp hg]; rw [mul_inv_eq_iff_eq_mul] at h; exact h⟩
  rw [hc.CQ_rho] at h1
  exact mem_bot.mp h1

theorem rho_V :
    (rho * x₁ ^ 2 * rho⁻¹ = x₂ ^ 2 ∧ rho * x₂ ^ 2 * rho⁻¹ = (x₁ * x₂) ^ 2 ∧
      rho * (x₁ * x₂) ^ 2 * rho⁻¹ = x₁ ^ 2) ∨
    (rho * x₁ ^ 2 * rho⁻¹ = (x₁ * x₂) ^ 2 ∧ rho * (x₁ * x₂) ^ 2 * rho⁻¹ = x₂ ^ 2 ∧
      rho * x₂ ^ 2 * rho⁻¹ = x₁ ^ 2) := by
  have hinj : ∀ a b : G, rho * a * rho⁻¹ = rho * b * rho⁻¹ → a = b := fun a b h => by
    have h1 := mul_right_cancel h
    exact mul_left_cancel h1
  have hy := hc.rho_conj_V hc.y_mem_V
  have hz := hc.rho_conj_V hc.z_mem_V
  have hw := hc.rho_conj_V hc.w_mem_V
  rw [hc.mem_V_iff] at hy hz hw
  have hy1 : rho * x₁ ^ 2 * rho⁻¹ ≠ 1 := fun h => hc.y_ne_one (hinj _ 1 (by rw [h]; group))
  have hz1 : rho * (x₁ * x₂) ^ 2 * rho⁻¹ ≠ 1 := fun h => hc.z_ne_one (hinj _ 1 (by rw [h]; group))
  have hw1 : rho * x₂ ^ 2 * rho⁻¹ ≠ 1 := fun h => hc.x₂_sq_ne_one (hinj _ 1 (by rw [h]; group))
  have hy2 : rho * x₁ ^ 2 * rho⁻¹ ≠ x₁ ^ 2 := fun h => hc.y_ne_one (hc.rho_fpf_V hc.y_mem_V h)
  have hz2 : rho * (x₁ * x₂) ^ 2 * rho⁻¹ ≠ (x₁ * x₂) ^ 2 := fun h =>
    hc.z_ne_one (hc.rho_fpf_V hc.z_mem_V h)
  have hw2 : rho * x₂ ^ 2 * rho⁻¹ ≠ x₂ ^ 2 := fun h =>
    hc.x₂_sq_ne_one (hc.rho_fpf_V hc.w_mem_V h)
  have hcube : ∀ a : G, rho * (rho * (rho * a * rho⁻¹) * rho⁻¹) * rho⁻¹ = a := fun a => by
    have h3 : rho * rho * rho = 1 := by
      have h := hc.rho_pow_three
      rwa [pow_succ, pow_two] at h
    calc rho * (rho * (rho * a * rho⁻¹) * rho⁻¹) * rho⁻¹
        = (rho * rho * rho) * a * (rho * rho * rho)⁻¹ := by group
      _ = a := by rw [h3]; group
  rcases hy with h | h | h | h
  · exact absurd h hy1
  · exact absurd h hy2
  ·
    rcases hz with h' | h' | h' | h'
    · exact absurd h' hz1
    ·
      exact absurd (by rw [← hcube (x₁ ^ 2), h, h', h]) hc.y_ne_z
    · exact absurd h' hz2
    · right
      refine ⟨h, h', ?_⟩
      rcases hw with h'' | h'' | h'' | h''
      · exact absurd h'' hw1
      · exact h''
      · exact absurd (hinj _ _ (h''.trans h.symm)) hc.y_ne_w.symm
      · exact absurd h'' hw2
  ·
    rcases hz with h' | h' | h' | h'
    · exact absurd h' hz1
    · left
      refine ⟨h, ?_, h'⟩
      rcases hw with h'' | h'' | h'' | h''
      · exact absurd h'' hw1
      · exact absurd (hinj _ _ (h''.trans h'.symm)) hc.z_ne_w.symm
      · exact h''
      · exact absurd h'' hw2
    · exact absurd h' hz2
    · exact absurd (hinj _ _ (h'.trans h.symm)) hc.y_ne_z.symm

end Ctx4Q

end CFSG.OddStandard.SmallF3.HarrisU33
