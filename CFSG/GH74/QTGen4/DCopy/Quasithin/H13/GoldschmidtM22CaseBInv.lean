module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBNB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBFix

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace BCtx_F4

variable {T M L V : Subgroup G} {g : G} {D : Subgroup G} (c : BCtx_F4 T M L V g D)

include c in
theorem conj_into_V {a : G} (haV1 : a ∈ conjSubgroup V g ⊓ CHU T L V)
    (haN : a ∈ Subgroup.normalizer (V : Set G)) (has : Equiv.Perm.sign (c.ρ a) = -1)
    (ha2 : a * a = 1) {x : G} (hx : x ∈ L ⊔ Subgroup.zpowers a) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ h : G, ∃ v ∈ V, v ≠ 1 ∧ h * x * h⁻¹ = v := by
  have hNB : ∀ y ∈ L ⊔ Subgroup.zpowers a, y ∈ Subgroup.normalizer (V : Set G) := fun y hy =>
    sup_le c.L_le_N (Subgroup.zpowers_le.mpr haN) hy
  have hxN := hNB x hx
  by_cases hρ : c.ρ x = 1
  · exact ⟨1, x, c.NB_inf_Q_le_V haN has ha2 hx ((c.ρ.eq_one_iff hxN).mp hρ), hx1, by simp⟩
  · have hρ2 : c.ρ x * c.ρ x = 1 := by
      rw [← PermRho.apply_mul hxN hxN, hx2, PermRho.apply_one]
    have haa : c.ρ a * c.ρ a = 1 := by
      rw [← PermRho.apply_mul haN haN, ha2, PermRho.apply_one]
    obtain ⟨x₁, hx₁NB, hx₁Vg, hx₁2, hx₁ρ2, hx₁ρ1, hx₁s⟩ : ∃ x₁ ∈ L ⊔ Subgroup.zpowers a,
        x₁ ∈ conjSubgroup V g ∧ x₁ * x₁ = 1 ∧ c.ρ x₁ * c.ρ x₁ = 1 ∧ c.ρ x₁ ≠ 1 ∧
        Equiv.Perm.sign (c.ρ x₁) = Equiv.Perm.sign (c.ρ x) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (c.ρ x)) with hs | hs
      · obtain ⟨y, hyL, hyVg, hy2, hyρ2, hyρ1, hys⟩ := c.exists_y
        exact ⟨y, Subgroup.mem_sup_left hyL, hyVg, by rw [← pow_two]; exact hy2, hyρ2, hyρ1,
          by rw [hys, hs]⟩
      · refine ⟨a, Subgroup.mem_sup_right (Subgroup.mem_zpowers a), (Subgroup.mem_inf.mp haV1).1,
          ha2, haa, fun h => ?_, by rw [has, hs]⟩
        have := congrArg Equiv.Perm.sign h
        rw [has, map_one] at this
        exact absurd this (by decide)
    have hx₁N := hNB x₁ hx₁NB
    obtain ⟨π, hπ⟩ := perm5_isConj_of_involution hx₁ρ2 hρ2 hx₁ρ1 hρ hx₁s
    obtain ⟨n, hnNB, hn⟩ := c.exists_rho_NB haN has ha2 π
    have hnN := hNB n hnNB
    have hx₂NB : n * x₁ * n⁻¹ ∈ L ⊔ Subgroup.zpowers a :=
      (L ⊔ Subgroup.zpowers a).mul_mem ((L ⊔ Subgroup.zpowers a).mul_mem hnNB hx₁NB)
        ((L ⊔ Subgroup.zpowers a).inv_mem hnNB)
    have hx₂N := hNB _ hx₂NB
    have hx₂2 : (n * x₁ * n⁻¹) * (n * x₁ * n⁻¹) = 1 := by
      calc n * x₁ * n⁻¹ * (n * x₁ * n⁻¹) = n * (x₁ * x₁) * n⁻¹ := by group
        _ = 1 := by rw [hx₁2]; group
    have hρx₂ : c.ρ (n * x₁ * n⁻¹) = c.ρ x := by
      rw [PermRho.apply_conj hnN hx₁N, hn]
      exact hπ
    have hq : (n * x₁ * n⁻¹)⁻¹ * x ∈ Subgroup.centralizer (V : Set G) :=
      (c.ρ.eq_iff hx₂N hxN).mp hρx₂
    have hqV : (n * x₁ * n⁻¹)⁻¹ * x ∈ V :=
      c.NB_inf_Q_le_V haN has ha2
        ((L ⊔ Subgroup.zpowers a).mul_mem ((L ⊔ Subgroup.zpowers a).inv_mem hx₂NB) hx) hq
    have hx₂Q : n * x₁ * n⁻¹ ∉ Subgroup.centralizer (V : Set G) := fun h =>
      hρ (hρx₂ ▸ (c.ρ.eq_one_iff hx₂N).mpr h)
    generalize hx₂ : n * x₁ * n⁻¹ = x₂ at *
    have hx₂inv : x₂⁻¹ = x₂ := inv_eq_of_mul_eq_one_right hx₂2
    have hqinv : (x₂⁻¹ * x)⁻¹ = x₂⁻¹ * x := by
      have := c.h.toHyp611.isElemAbelian.2 _ hqV
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact this)
    have hcent : (x₂⁻¹ * x) ∈ Subgroup.centralizer ({x₂} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : x₂ * (x₂⁻¹ * x) * x₂ * (x₂⁻¹ * x) = 1 := by
        calc x₂ * (x₂⁻¹ * x) * x₂ * (x₂⁻¹ * x) = x * x := by group
          _ = 1 := hx2
      have h2 : x₂ * (x₂⁻¹ * x) * x₂ = x₂⁻¹ * x := by
        rw [eq_inv_of_mul_eq_one_left h1, hqinv]
      calc x₂⁻¹ * x * x₂ = (x₂ * (x₂⁻¹ * x) * x₂) * x₂ := by rw [h2]
        _ = x₂ * (x₂⁻¹ * x) * (x₂ * x₂) := by group
        _ = x₂ * (x₂⁻¹ * x) := by rw [hx₂2, mul_one]
    obtain ⟨v, hv, hvq⟩ := c.exists_comm_of_involution hx₂N hx₂2 hx₂Q _ ⟨hqV, hcent⟩
    have hxeq : x = v * x₂ * v⁻¹ := by
      have h3 : x₂ * (x₂⁻¹ * x) = x₂⁻¹ * x * x₂ :=
        (Subgroup.mem_centralizer_singleton_iff.mp hcent).symm
      calc x = x₂ * (x₂⁻¹ * x) := by group
        _ = x₂⁻¹ * x * x₂ := h3
        _ = v * x₂ * v⁻¹ * x₂⁻¹ * x₂ := by rw [← hvq]
        _ = v * x₂ * v⁻¹ := by group
    have hw : g * x₁ * g⁻¹ ∈ V := mem_conjSubgroup_iff.mp hx₁Vg
    refine ⟨g * n⁻¹ * v⁻¹, g * x₁ * g⁻¹, hw, fun h => hx₁ρ1 ?_, ?_⟩
    · have : x₁ = 1 := by
        have h' : g * x₁ * g⁻¹ = 1 := h
        simpa using h'
      rw [this, PermRho.apply_one]
    · calc g * n⁻¹ * v⁻¹ * x * (g * n⁻¹ * v⁻¹)⁻¹
          = g * n⁻¹ * v⁻¹ * (v * x₂ * v⁻¹) * (g * n⁻¹ * v⁻¹)⁻¹ := by rw [hxeq]
        _ = g * n⁻¹ * x₂ * n * g⁻¹ := by group
        _ = g * x₁ * g⁻¹ := by rw [← hx₂]; group

end BCtx_F4

end CFSG.Quasithin.H13.GM22
