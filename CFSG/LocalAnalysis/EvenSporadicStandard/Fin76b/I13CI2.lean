module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13R

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

theorem card_W2' : Nat.card ↥c.W2 = 64 := c.h.card_W2 c.hα c.hF c.hWr c.hBD

theorem exists_W1_not_W2 : ∃ w ∈ c.W1, w ∉ c.W2 := by
  by_contra hcon
  have hcon' : ∀ w ∈ c.W1, w ∈ c.W2 := fun w hw => by_contra fun hh => hcon ⟨w, hw, hh⟩
  have hQW : c.Qs ≤ c.W2 := by
    intro q hq
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := c.Qs_eq hq
    exact mul_mem (hcon' w₁ hw₁) hw₂
  have := Subgroup.card_le_of_le hQW
  rw [c.card_Qs, c.card_W2'] at this
  omega

theorem t_mul_comm_Qs {w : G} (hw : w ∈ c.Qs) : t * w = w * t := c.Zs_comm_Qs c.t_mem_Zs hw

variable {c}

namespace IsRs

variable {Rs : Subgroup G} (hR : c.IsRs Rs)

include hR

theorem rho_eq_one_of_comm {n : G} (hn : n ∈ Rs ⊓ c.N1)
    (hcomm : ∀ s ∈ Rs, n * s * n⁻¹ * s⁻¹ = 1 ∨ n * s * n⁻¹ * s⁻¹ = t) :
    c.rho ⟨n, hn.2⟩ = 1 := by
  have key : ∀ m : G, (hm : m ∈ c.N1) → (∀ w ∈ c.W1, m * w * m⁻¹ = w ∨ m * w * m⁻¹ = w * t) →
      c.rho1 ⟨m, hm⟩ = 1 := by
    intro m hm hmw
    refine MulEquiv.ext fun e => ?_
    obtain ⟨w, rfl⟩ := c.thetaHom_surjective e
    rw [c.rho1_theta]
    show c.thetaHom (c.conjW1 ⟨m, hm⟩ w) = c.thetaHom w
    refine Eq.symm ?_
    rw [c.thetaHom_eq_iff]
    rcases hmw w w.2 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hRw : ∀ w ∈ c.Qs, w ∈ Rs := fun w hw => hR.Qs_le hw
  have hc1 : ∀ w ∈ c.W1, n * w * n⁻¹ = w ∨ n * w * n⁻¹ = w * t := by
    intro w hw
    have hwq : w ∈ c.Qs := c.W1_le_Qs hw
    rcases hcomm w (hRw w hwq) with h1 | h1
    · left
      calc n * w * n⁻¹ = (n * w * n⁻¹ * w⁻¹) * w := by group
        _ = w := by rw [h1, one_mul]
    · right
      calc n * w * n⁻¹ = (n * w * n⁻¹ * w⁻¹) * w := by group
        _ = t * w := by rw [h1]
        _ = w * t := c.t_mul_comm_Qs hwq
  have hc2 : ∀ w ∈ c.W1, (z * n * z⁻¹) * w * (z * n * z⁻¹)⁻¹ = w ∨
      (z * n * z⁻¹) * w * (z * n * z⁻¹)⁻¹ = w * t := by
    intro w hw
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right c.h.z_sq
    have hs : z⁻¹ * w * z ∈ c.W2 := by
      have h0 := c.z_conj_W1 hw
      rw [hzi] at h0 ⊢
      exact h0
    have hsq : z⁻¹ * w * z ∈ c.Qs := c.W2_le_Qs hs
    have hev : (z * n * z⁻¹) * w * (z * n * z⁻¹)⁻¹ =
        z * (n * (z⁻¹ * w * z) * n⁻¹ * (z⁻¹ * w * z)⁻¹) * z⁻¹ * w := by
      group
    have hz1 : z * (1 : G) * z⁻¹ * w = w := by group
    have hzt : z * t * z⁻¹ * w = w * t := by
      rw [c.h.z_conj_t]
      exact c.t_mul_comm_Qs (c.W1_le_Qs hw)
    rcases hcomm _ (hRw _ hsq) with h1 | h1
    · left
      rw [hev, h1, hz1]
    · right
      rw [hev, h1, hzt]
  refine Prod.ext ?_ ?_
  · exact key n hn.2 hc1
  · show c.rho1 (c.zconjN1 ⟨n, hn.2⟩) = 1
    exact key _ (c.z_conj_N1 hn.2) hc2

theorem Z2_le {n : G} (hn : n ∈ Rs)
    (hcomm : ∀ s ∈ Rs, n * s * n⁻¹ * s⁻¹ = 1 ∨ n * s * n⁻¹ * s⁻¹ = t) : n ∈ c.Zs := by
  by_cases hnN : n ∈ c.N1
  · have hnR : n ∈ Rs ⊓ c.N1 := ⟨hn, hnN⟩
    have hρ := hR.rho_eq_one_of_comm hnR hcomm
    exact hR.R_inf_KR_le ⟨hnR, c.mem_KR.2 ⟨hnN, hρ⟩⟩
  · exfalso
    rcases c.Nc_perm (hR.le_Nc hn) with ⟨h1, -, -⟩ | ⟨-, h1, h2⟩
    · exact hnN (c.mem_N1.2 ⟨hR.le_Nc hn, h1⟩)
    · obtain ⟨w, hw1, hw2⟩ := c.exists_W1_not_W2
      have hwq : w ∈ c.Qs := c.W1_le_Qs hw1
      have hnw : n * w * n⁻¹ ∈ c.W2 := h1 w hw1
      apply hw2
      rcases hcomm w (hR.Qs_le hwq) with h3 | h3
      · have : n * w * n⁻¹ = w := by
          calc n * w * n⁻¹ = (n * w * n⁻¹ * w⁻¹) * w := by group
            _ = w := by rw [h3, one_mul]
        rwa [this] at hnw
      · have : n * w * n⁻¹ = w * t := by
          calc n * w * n⁻¹ = (n * w * n⁻¹ * w⁻¹) * w := by group
            _ = t * w := by rw [h3]
            _ = w * t := c.t_mul_comm_Qs hwq
        rw [this] at hnw
        have : w = (w * t) * t⁻¹ := by group
        rw [this]
        exact mul_mem hnw (inv_mem (c.Zs_le_W2 c.t_mem_Zs))

end IsRs

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
