module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d5a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d3a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d4a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_N_normal_L (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ g ∈ q13L t tau x₁ x₂ rho om, ∀ n ∈ ctxN tau x₁ x₂, g * n * g⁻¹ ∈ ctxN tau x₁ x₂ := by
  intro g hg n hn
  rw [← q13d_cent_E0 h] at hn ⊢
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro e he
  have hg' : g⁻¹ ∈ q13L t tau x₁ x₂ rho om := inv_mem hg
  rw [q13L] at hg'
  have hconj : g⁻¹ * e * g ∈ q13E0 t tau x₁ x₂ rho om := by
    simpa using (Subgroup.mem_normalizer_iff.mp hg' e).mp he
  have hcomm : (g⁻¹ * e * g) * n = n * (g⁻¹ * e * g) := hn _ hconj
  calc e * (g * n * g⁻¹) = g * ((g⁻¹ * e * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * e * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * n * g⁻¹) * e := by group

theorem q13d_U_le_L (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) :
    ctxU t tau x₁ x₂ lam ≤ q13L t tau x₁ x₂ rho om := by
  rw [q13L]
  exact (Subgroup.le_normalizer : ctxU t tau x₁ x₂ lam ≤
    Subgroup.normalizer (ctxU t tau x₁ x₂ lam : Set G)).trans
    (q13d_normalizer_le_of_charIn (q13d_E0_char_U h hB))

theorem q13d_M_le_L (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) :
    ctxM t tau x₁ x₂ ≤ q13L t tau x₁ x₂ rho om := by
  rw [h.c11.M_eq]
  refine sup_le ((q13b_O_le_U h).trans (q13d_U_le_L h hB)) ?_
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · rw [hx]; exact q13d_rho_norm h
  · rw [hx]
    exact q13d_U_le_L h hB (Subgroup.mem_sup_right (Subgroup.mem_zpowers lam))

private theorem q13d5b_conj_mem_X (h : Q13Om t L S x₁ x₂ lam rho tau om) {u : G}
    (huL : u ∈ q13L t tau x₁ x₂ rho om)
    (huC : u ∈ centralizer ({t} : Set G)) :
    ∀ x ∈ ctxX t tau x₁ x₂, u * x * u⁻¹ ∈ ctxX t tau x₁ x₂ := by
  have hgen : ∀ x ∈ ({t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G),
      u * x * u⁻¹ ∈ ctxX t tau x₁ x₂ := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx
    · rw [hx]
      have hut : u * t = t * u := Subgroup.mem_centralizer_singleton_iff.mp huC
      have hfix : u * t * u⁻¹ = t := by rw [hut]; group
      rw [hfix]
      exact Subgroup.subset_closure (by simp)
    · rw [hx]
      exact (p0_V_le_N_le_X t tau x₁ x₂).2
        (q13d_N_normal_L h u huL tau (q13b_tau_mem_N h))
    · rw [hx]
      exact (p0_V_le_N_le_X t tau x₁ x₂).2
        (q13d_N_normal_L h u huL (x₁ ^ 2) (Subgroup.subset_closure (by simp)))
    · rw [hx]
      exact (p0_V_le_N_le_X t tau x₁ x₂).2
        (q13d_N_normal_L h u huL ((x₁ * x₂) ^ 2) (Subgroup.subset_closure (by simp)))
  intro x hx
  have hle : ctxX t tau x₁ x₂ ≤
      (ctxX t tau x₁ x₂).comap (MulAut.conj u).toMonoidHom := by
    rw [ctxX, Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change u * y * u⁻¹ ∈ ctxX t tau x₁ x₂
    exact hgen y hy
  exact hle hx

theorem q13d_CL_t (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) :
    q13L t tau x₁ x₂ rho om ⊓ centralizer ({t} : Set G) = ctxM t tau x₁ x₂
      ⊓ centralizer ({t} : Set G) := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_inf] at hg ⊢
    obtain ⟨hgL, hgC⟩ := hg
    refine ⟨?_, hgC⟩
    rw [ctxM, Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      rw [Subgroup.mem_comap]
      change g * x * g⁻¹ ∈ ctxX t tau x₁ x₂
      exact q13d5b_conj_mem_X h hgL hgC x hx
    · intro x hx
      have hgL' : g⁻¹ ∈ q13L t tau x₁ x₂ rho om := inv_mem hgL
      have hgC' : g⁻¹ ∈ centralizer ({t} : Set G) := inv_mem hgC
      have hx' : g⁻¹ * x * g ∈ ctxX t tau x₁ x₂ := by
        simpa using q13d5b_conj_mem_X h hgL' hgC' x hx
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hx', ?_⟩
      change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  · intro g hg
    rw [Subgroup.mem_inf] at hg ⊢
    obtain ⟨hgM, hgC⟩ := hg
    exact ⟨q13d_M_le_L h hB hgM, hgC⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
