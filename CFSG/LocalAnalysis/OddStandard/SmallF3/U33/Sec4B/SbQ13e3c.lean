module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d5b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e3a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13e_kap_conj_eq {t g b p0 : G} (ht : t * t = 1)
    (hg' : g⁻¹ * t * g = t * p0) (hpt : p0 * t = t * p0⁻¹)
    (hbt : b * t = t * ⁅t, b⁆ * b) (hcomm : p0⁻¹ * ⁅t, b⁆ = ⁅t, b⁆ * p0⁻¹) :
    ⁅t, g * b * g⁻¹⁆ = g * ⁅t, b⁆ * (p0⁻¹ * (b * p0 * b⁻¹)) * g⁻¹ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hgt : t * g * t = g * p0⁻¹ := by
    have h1 : t * g = g * (t * p0) := by rw [← hg']; group
    calc t * g * t = g * (t * p0) * t := by rw [h1]
      _ = g * (t * (p0 * t)) := by group
      _ = g * (t * (t * p0⁻¹)) := by rw [hpt]
      _ = g * ((t * t) * p0⁻¹) := by group
      _ = g * p0⁻¹ := by rw [ht, one_mul]
  rw [commutatorElement_def, hti]
  calc t * (g * b * g⁻¹) * t * (g * b * g⁻¹)⁻¹
      = (t * g * b) * (g⁻¹ * t * g) * (b⁻¹ * g⁻¹) := by group
    _ = (t * g * b) * (t * p0) * (b⁻¹ * g⁻¹) := by rw [hg']
    _ = (t * g) * (b * t * p0 * b⁻¹) * g⁻¹ := by group
    _ = (t * g) * (t * ⁅t, b⁆ * b * p0 * b⁻¹) * g⁻¹ := by rw [hbt]
    _ = ((t * g * t) * (⁅t, b⁆ * b * p0 * b⁻¹)) * g⁻¹ := by group
    _ = ((g * p0⁻¹) * (⁅t, b⁆ * b * p0 * b⁻¹)) * g⁻¹ := by rw [hgt]
    _ = ((g * (p0⁻¹ * ⁅t, b⁆)) * (b * p0 * b⁻¹)) * g⁻¹ := by group
    _ = ((g * (⁅t, b⁆ * p0⁻¹)) * (b * p0 * b⁻¹)) * g⁻¹ := by rw [hcomm]
    _ = g * ⁅t, b⁆ * (p0⁻¹ * (b * p0 * b⁻¹)) * g⁻¹ := by group

theorem q13e_kap_conj (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ g ∈ q13L t tau x₁ x₂ rho om, ∀ b ∈ q13B t tau x₁ x₂ rho om,
      ⁅t, g * b * g⁻¹⁆ * (g * ⁅t, b⁆ * g⁻¹)⁻¹ ∈ ctxN tau x₁ x₂ := by
  intro g hg b hb
  have ht : t * t = 1 := q13a_t_mul_self h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hbL : b ∈ q13L t tau x₁ x₂ rho om := by
    rw [q13B] at hb
    exact hb.1
  have hp0P : ⁅t, g⁻¹⁆ ∈ q13P t tau x₁ x₂ rho om :=
    q13e_kap_mem_P h hD g⁻¹ (inv_mem hg)
  have hkbP : ⁅t, b⁆ ∈ q13P t tau x₁ x₂ rho om := q13e_kap_mem_P h hD b hbL
  have hg' : g⁻¹ * t * g = t * ⁅t, g⁻¹⁆ := by
    simpa only [inv_inv] using q13e_conj_t h g⁻¹
  have hpt : ⁅t, g⁻¹⁆ * t = t * (⁅t, g⁻¹⁆)⁻¹ := by
    have hp : t * ⁅t, g⁻¹⁆ * t⁻¹ = (⁅t, g⁻¹⁆)⁻¹ := hD.t_inv_P ⁅t, g⁻¹⁆ hp0P
    rw [hti] at hp
    calc ⁅t, g⁻¹⁆ * t = (t * t) * ⁅t, g⁻¹⁆ * t := by rw [ht, one_mul]
      _ = t * (t * ⁅t, g⁻¹⁆ * t) := by group
      _ = t * (⁅t, g⁻¹⁆)⁻¹ := by rw [hp]
  have hbt : b * t = t * ⁅t, b⁆ * b := by
    have hbconj : b * t * b⁻¹ = t * ⁅t, b⁆ := q13e_conj_t h b
    rw [← hbconj]
    group
  have hcomm : (⁅t, g⁻¹⁆)⁻¹ * ⁅t, b⁆ = ⁅t, b⁆ * (⁅t, g⁻¹⁆)⁻¹ :=
    q13d_P_comm h hD.A_cent (⁅t, g⁻¹⁆)⁻¹ (inv_mem hp0P) ⁅t, b⁆ hkbP
  have hmain := q13e_kap_conj_eq (t := t) (g := g) (b := b) (p0 := ⁅t, g⁻¹⁆) ht hg' hpt hbt hcomm
  have hP1 : b * ⁅t, g⁻¹⁆ * b⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
    q13d_P_normal_L h hD.A_cent b hbL ⁅t, g⁻¹⁆ hp0P
  have hn0P : (⁅t, g⁻¹⁆)⁻¹ * (b * ⁅t, g⁻¹⁆ * b⁻¹) ∈ q13P t tau x₁ x₂ rho om :=
    (q13P t tau x₁ x₂ rho om).mul_mem (inv_mem hp0P) hP1
  have hn0N : (⁅t, g⁻¹⁆)⁻¹ * (b * ⁅t, g⁻¹⁆ * b⁻¹) ∈ ctxN tau x₁ x₂ := by
    have hN : b * ⁅t, g⁻¹⁆ * b⁻¹ * (⁅t, g⁻¹⁆)⁻¹ ∈ ctxN tau x₁ x₂ :=
      q13e_comm_BP h hD b hb ⁅t, g⁻¹⁆ hp0P
    have hcommP : b * ⁅t, g⁻¹⁆ * b⁻¹ * (⁅t, g⁻¹⁆)⁻¹ =
        (⁅t, g⁻¹⁆)⁻¹ * (b * ⁅t, g⁻¹⁆ * b⁻¹) :=
      q13d_P_comm h hD.A_cent (b * ⁅t, g⁻¹⁆ * b⁻¹) hP1 (⁅t, g⁻¹⁆)⁻¹ (inv_mem hp0P)
    rw [← hcommP]
    exact hN
  have hcommN : ⁅t, b⁆ * ((⁅t, g⁻¹⁆)⁻¹ * (b * ⁅t, g⁻¹⁆ * b⁻¹)) =
      ((⁅t, g⁻¹⁆)⁻¹ * (b * ⁅t, g⁻¹⁆ * b⁻¹)) * ⁅t, b⁆ :=
    q13d_P_comm h hD.A_cent ⁅t, b⁆ hkbP ((⁅t, g⁻¹⁆)⁻¹ * (b * ⁅t, g⁻¹⁆ * b⁻¹)) hn0P
  have hprod : ⁅t, g * b * g⁻¹⁆ * (g * ⁅t, b⁆ * g⁻¹)⁻¹ =
      g * ((⁅t, g⁻¹⁆)⁻¹ * (b * ⁅t, g⁻¹⁆ * b⁻¹)) * g⁻¹ := by
    rw [hmain]
    calc (g * ⁅t, b⁆ * ((⁅t, g⁻¹⁆)⁻¹ * (b * ⁅t, g⁻¹⁆ * b⁻¹)) * g⁻¹) *
          (g * ⁅t, b⁆ * g⁻¹)⁻¹
        = g * ⁅t, b⁆ * ((⁅t, g⁻¹⁆)⁻¹ * (b * ⁅t, g⁻¹⁆ * b⁻¹)) * ⁅t, b⁆⁻¹ * g⁻¹ := by group
      _ = g * (⁅t, b⁆ * ((⁅t, g⁻¹⁆)⁻¹ * (b * ⁅t, g⁻¹⁆ * b⁻¹))) * ⁅t, b⁆⁻¹ * g⁻¹ := by group
      _ = g * (((⁅t, g⁻¹⁆)⁻¹ * (b * ⁅t, g⁻¹⁆ * b⁻¹)) * ⁅t, b⁆) * ⁅t, b⁆⁻¹ * g⁻¹ := by
            rw [hcommN]
      _ = g * ((⁅t, g⁻¹⁆)⁻¹ * (b * ⁅t, g⁻¹⁆ * b⁻¹)) * g⁻¹ := by group
  rw [hprod]
  exact q13d_N_normal_L h g hg _ hn0N

theorem q13e_kap_conj_t {g : G} (hg : g * t = t * g) (b : G) :
    ⁅t, g * b * g⁻¹⁆ = g * ⁅t, b⁆ * g⁻¹ := by
  have hgt : g * t * g⁻¹ = t := by
    rw [hg]
    group
  have hconj := conjugate_commutatorElement (g₁ := t) (g₂ := b) (g₃ := g)
  rw [hgt] at hconj
  exact hconj.symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
