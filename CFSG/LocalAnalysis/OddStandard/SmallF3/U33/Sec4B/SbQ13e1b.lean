module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e1a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0e

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13e_class_one (h : Q13Om t L S x₁ x₂ lam rho tau om) (hC : Q13C t x₁ x₂ lam tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {b p : G} (hbB : b ∈ q13B t tau x₁ x₂ rho om)
    (hp : p ∈ q13H1 t tau x₁ x₂ lam rho) (hb : (t * lam) * b * (t * lam)⁻¹ = b * p) :
    b ∈ q13E0 t tau x₁ x₂ rho om := by
  have hpP : p ∈ q13P t tau x₁ x₂ rho om :=
    (q13e_H1_le_AN.trans (q13e_AN_le_P h)) hp
  obtain ⟨q, hqP, hq⟩ := q13e_P_of_H1 h hC hD p⁻¹ (Subgroup.inv_mem _ hp)
  have hq' : (t * lam) * q * (t * lam)⁻¹ * q⁻¹ = p⁻¹ := hq.symm
  have hfix : (t * lam) * (b * q) * (t * lam)⁻¹ = b * q := by
    rw [q13e_cocycle_change h hD hb hpP hqP, hq']
    group
  have hcomm : (t * lam) * (b * q) = (b * q) * (t * lam) := by
    calc (t * lam) * (b * q) =
        ((t * lam) * (b * q) * (t * lam)⁻¹) * (t * lam) := by group
      _ = (b * q) * (t * lam) := by rw [hfix]
  have hbqB : b * q ∈ q13B t tau x₁ x₂ rho om :=
    (q13B t tau x₁ x₂ rho om).mul_mem hbB (hD.E0_le_B ((q13d_P_le_E0 h) hqP))
  have hbqE0 : b * q ∈ q13E0 t tau x₁ x₂ rho om := q13e_CB_f h hC hD (b * q) hbqB hcomm
  have hbq : b = (b * q) * q⁻¹ := by group
  rw [hbq]
  exact (q13E0 t tau x₁ x₂ rho om).mul_mem hbqE0
    ((q13E0 t tau x₁ x₂ rho om).inv_mem ((q13d_P_le_E0 h) hqP))

theorem q13e_class_gam (h : Q13Om t L S x₁ x₂ lam rho tau om) (hC : Q13C t x₁ x₂ lam tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {b₁ b₂ p₁ p₂ : G} (hb₁ : b₁ ∈ q13B t tau x₁ x₂ rho om)
    (hb₂ : b₂ ∈ q13B t tau x₁ x₂ rho om) (hp₁ : p₁ ∈ q13P t tau x₁ x₂ rho om)
    (hp₂ : p₂ ∈ q13P t tau x₁ x₂ rho om) (h₁ : (t * lam) * b₁ * (t * lam)⁻¹ = b₁ * p₁)
    (h₂ : (t * lam) * b₂ * (t * lam)⁻¹ = b₂ * p₂)
    (hc₁ : (t * om)⁻¹ * p₁ ∈ q13H1 t tau x₁ x₂ lam rho)
    (hc₂ : (t * om)⁻¹ * p₂ ∈ q13H1 t tau x₁ x₂ lam rho) :
    b₁⁻¹ * b₂ ∈ q13E0 t tau x₁ x₂ rho om := by
  have hgP : t * om ∈ q13P t tau x₁ x₂ rho om := q13d_gam_mem_P h
  have hginvP : (t * om)⁻¹ ∈ q13P t tau x₁ x₂ rho om := Subgroup.inv_mem _ hgP
  obtain ⟨q₁, hq₁P, hq₁⟩ :=
    q13e_P_of_H1 h hC hD ((t * om)⁻¹ * p₁)⁻¹ (Subgroup.inv_mem _ hc₁)
  obtain ⟨q₂, hq₂P, hq₂⟩ :=
    q13e_P_of_H1 h hC hD ((t * om)⁻¹ * p₂)⁻¹ (Subgroup.inv_mem _ hc₂)
  have hq₁' : (t * lam) * q₁ * (t * lam)⁻¹ * q₁⁻¹ = ((t * om)⁻¹ * p₁)⁻¹ := hq₁.symm
  have hq₂' : (t * lam) * q₂ * (t * lam)⁻¹ * q₂⁻¹ = ((t * om)⁻¹ * p₂)⁻¹ := hq₂.symm
  have hfix₁ : (t * lam) * (b₁ * q₁) * (t * lam)⁻¹ = (b₁ * q₁) * (t * om) := by
    rw [q13e_cocycle_change h hD h₁ hp₁ hq₁P, hq₁']
    group
  have hfix₂ : (t * lam) * (b₂ * q₂) * (t * lam)⁻¹ = (b₂ * q₂) * (t * om) := by
    rw [q13e_cocycle_change h hD h₂ hp₂ hq₂P, hq₂']
    group
  have hb₁'B : b₁ * q₁ ∈ q13B t tau x₁ x₂ rho om :=
    (q13B t tau x₁ x₂ rho om).mul_mem hb₁ (hD.E0_le_B ((q13d_P_le_E0 h) hq₁P))
  have hb₂'B : b₂ * q₂ ∈ q13B t tau x₁ x₂ rho om :=
    (q13B t tau x₁ x₂ rho om).mul_mem hb₂ (hD.E0_le_B ((q13d_P_le_E0 h) hq₂P))
  let bb : G := (b₁ * q₁)⁻¹ * (b₂ * q₂)
  let nn : G := bb⁻¹ * (t * om)⁻¹ * bb * (t * om)
  have hbB : bb ∈ q13B t tau x₁ x₂ rho om := by
    dsimp only [bb]
    exact (q13B t tau x₁ x₂ rho om).mul_mem
      ((q13B t tau x₁ x₂ rho om).inv_mem hb₁'B) hb₂'B
  have hfix : (t * lam) * bb * (t * lam)⁻¹ = bb * nn := by
    dsimp only [bb, nn]
    have hconj : (t * lam) * ((b₁ * q₁)⁻¹ * (b₂ * q₂)) * (t * lam)⁻¹ =
        ((t * lam) * (b₁ * q₁) * (t * lam)⁻¹)⁻¹ *
          ((t * lam) * (b₂ * q₂) * (t * lam)⁻¹) := by group
    rw [hconj, hfix₁, hfix₂]
    group
  have hnN : nn ∈ ctxN tau x₁ x₂ := by
    dsimp only [nn]
    have hc := q13e_comm_BP h hD bb⁻¹ ((q13B t tau x₁ x₂ rho om).inv_mem hbB)
      ((t * om)⁻¹) hginvP
    simpa using hc
  have hn_cyc : nn * ((t * lam) * nn * (t * lam)⁻¹) = 1 := q13e_cocycle h hfix
  have hnH1 : nn ∈ q13H1 t tau x₁ x₂ lam rho :=
    q13e_Z1_AN h nn (q13e_N_le_AN h hnN) hn_cyc
  have hbE0 : bb ∈ q13E0 t tau x₁ x₂ rho om := q13e_class_one h hC hD hbB hnH1 hfix
  have hfinal : b₁⁻¹ * b₂ = q₁ * bb * q₂⁻¹ := by
    dsimp only [bb]
    group
  rw [hfinal]
  exact (q13E0 t tau x₁ x₂ rho om).mul_mem
    ((q13E0 t tau x₁ x₂ rho om).mul_mem ((q13d_P_le_E0 h) hq₁P) hbE0)
    ((q13E0 t tau x₁ x₂ rho om).inv_mem ((q13d_P_le_E0 h) hq₂P))

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
