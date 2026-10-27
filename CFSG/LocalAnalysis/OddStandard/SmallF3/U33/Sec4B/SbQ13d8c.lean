module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d7b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d5b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13d8c_K_normal (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    NormalIn (ctxM t tau x₁ x₂ ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G))
      (ctxM t tau x₁ x₂) := by
  refine ⟨inf_le_left, ?_⟩
  intro g hg k hk
  rw [Subgroup.mem_inf] at hk ⊢
  obtain ⟨hkM, hkC⟩ := hk
  refine ⟨mul_mem (mul_mem hg hkM) (inv_mem hg), ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hkC ⊢
  intro n hn
  have hgn : g⁻¹ * n * g ∈ ctxN tau x₁ x₂ := by
    simpa using h.c11.normal_N.2 g⁻¹ (inv_mem hg) n hn
  have hcomm : k * (g⁻¹ * n * g) = (g⁻¹ * n * g) * k := (hkC _ hgn).symm
  exact (calc (g * k * g⁻¹) * n = g * (k * (g⁻¹ * n * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * n * g) * k) * g⁻¹ := by rw [hcomm]
    _ = n * (g * k * g⁻¹) := by group).symm

theorem q13d_card_CM_N_le (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)) ≤ 2 ^ 7 := by
  have hKB : ctxM t tau x₁ x₂ ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) ≤
      q13B t tau x₁ x₂ rho om := by
    rw [q13B]
    exact inf_le_inf_right _ (q13d_M_le_L h hB)
  have hK2 : IsPGroup 2 ↥(ctxM t tau x₁ x₂ ⊓
      centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)) :=
    (q13d_B_two h hII).to_le hKB
  have hKO : ctxM t tau x₁ x₂ ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) ≤
      ctxO t tau x₁ x₂ :=
    p0_le_O_of_normal t tau x₁ x₂ (q13d8c_K_normal h) hK2
  have hKE0 : ctxM t tau x₁ x₂ ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) ≤
      q13E0 t tau x₁ x₂ rho om :=
    (le_inf (hKO.trans (q13b_O_le_U h)) inf_le_right).trans (le_of_eq (q13d_E0_eq h))
  calc Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G))
      ≤ Nat.card ↥(q13E0 t tau x₁ x₂ rho om) := Subgroup.card_le_of_le hKE0
    _ = 2 ^ 7 := q13d_card_E0 h

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
