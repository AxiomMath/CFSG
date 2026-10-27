module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e3a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13e_kap_mul_B (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ b ∈ q13B t tau x₁ x₂ rho om, ∀ b' ∈ q13B t tau x₁ x₂ rho om,
      ⁅t, b * b'⁆ * (⁅t, b⁆ * ⁅t, b'⁆)⁻¹ ∈ ctxN tau x₁ x₂ := by
  intro b hb b' hb'
  have hbL : b ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hb).1
  have hb'L : b' ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hb').1
  have hkb : ⁅t, b⁆ ∈ q13P t tau x₁ x₂ rho om := q13e_kap_mem_P h hD b hbL
  have hkb' : ⁅t, b'⁆ ∈ q13P t tau x₁ x₂ rho om := q13e_kap_mem_P h hD b' hb'L
  have hn : b * ⁅t, b'⁆ * b⁻¹ * ⁅t, b'⁆⁻¹ ∈ ctxN tau x₁ x₂ :=
    q13e_comm_BP h hD b hb ⁅t, b'⁆ hkb'
  have hnP : b * ⁅t, b'⁆ * b⁻¹ * ⁅t, b'⁆⁻¹ ∈ q13P t tau x₁ x₂ rho om := q13d_N_le_P h hn
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h1 : b * ⁅t, b'⁆ * b⁻¹ =
      (b * ⁅t, b'⁆ * b⁻¹ * ⁅t, b'⁆⁻¹) * ⁅t, b'⁆ := by group
  have hE : (⁅t, b⁆ * b * ⁅t, b'⁆ * b⁻¹) * (⁅t, b⁆ * ⁅t, b'⁆)⁻¹ =
      ⁅t, b⁆ * (b * ⁅t, b'⁆ * b⁻¹ * ⁅t, b'⁆⁻¹) * ⁅t, b⁆⁻¹ := by
    rw [show (⁅t, b⁆ * b * ⁅t, b'⁆ * b⁻¹) = ⁅t, b⁆ * (b * ⁅t, b'⁆ * b⁻¹) from by group, h1]
    group
  rw [hE]
  have hcomm : ⁅t, b⁆ * (b * ⁅t, b'⁆ * b⁻¹ * ⁅t, b'⁆⁻¹) =
      (b * ⁅t, b'⁆ * b⁻¹ * ⁅t, b'⁆⁻¹) * ⁅t, b⁆ :=
    q13d_P_comm h hD.A_cent _ hkb _ hnP
  rw [hcomm]
  convert hn using 1
  group

theorem q13e_kap_N_iff (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ b ∈ q13B t tau x₁ x₂ rho om, ⁅t, b⁆ ∈ ctxN tau x₁ x₂ ↔ b ∈ q13E0 t tau x₁ x₂ rho om := by
  intro b hb
  constructor
  · intro hkN
    have hbL : b ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hb).1
    have hbt : b * t * b⁻¹ = t * ⁅t, b⁆ := q13e_conj_t h b
    have hmem : b * t * b⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) t := by
      rw [h.c11.tM]
      rw [q13d_mem_N h] at hkN
      rcases hkN with hV | ⟨v, hv, hvN⟩
      · exact Or.inl (Set.mem_smul_set.mpr ⟨⁅t, b⁆, hV, by rw [smul_eq_mul, hbt]⟩)
      · refine Or.inr (Set.mem_smul_set.mpr ⟨v, hv, ?_⟩)
        rw [smul_eq_mul, hbt, hvN]
        group
    obtain ⟨m, hmM, hm_eq⟩ := hmem
    have hgL : m⁻¹ * b ∈ q13L t tau x₁ x₂ rho om :=
      mul_mem (inv_mem (hD.M_le_L hmM)) hbL
    have hgt : (m⁻¹ * b) * t * (m⁻¹ * b)⁻¹ = t := by
      have hb1 : (m⁻¹ * b) * t * (m⁻¹ * b)⁻¹ = m⁻¹ * (b * t * b⁻¹) * m := by group
      rw [hb1, ← hm_eq]
      group
    have hgt' : (m⁻¹ * b) * t = t * (m⁻¹ * b) := by
      calc (m⁻¹ * b) * t = (m⁻¹ * b) * t * (m⁻¹ * b)⁻¹ * (m⁻¹ * b) := by group
        _ = t * (m⁻¹ * b) := by rw [hgt]
    have hgcent : m⁻¹ * b ∈ centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hgt'
    have hgmem : m⁻¹ * b ∈ q13L t tau x₁ x₂ rho om ⊓ centralizer ({t} : Set G) := ⟨hgL, hgcent⟩
    have hgM : m⁻¹ * b ∈ ctxM t tau x₁ x₂ := by
      rw [hD.CL_t] at hgmem
      exact (Subgroup.mem_inf.mp hgmem).1
    have hbM : b ∈ ctxM t tau x₁ x₂ := by
      have hmul : m * (m⁻¹ * b) = b := by group
      rw [← hmul]
      exact mul_mem hmM hgM
    have hbBM : b ∈ q13B t tau x₁ x₂ rho om ⊓ ctxM t tau x₁ x₂ := ⟨hb, hbM⟩
    rwa [q13e_B_inf_M h hB hD] at hbBM
  · intro hbE0
    exact q13e_kap_E0 h hD b hbE0

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
