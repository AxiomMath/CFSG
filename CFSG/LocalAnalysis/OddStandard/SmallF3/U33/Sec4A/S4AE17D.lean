module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18K
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE17A
public import CFSG.GH74.GLS.Bg.TwoGroups.L23Fin

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem e17_Q1_comm (h : L41GPh16 t L S x₁ x₂ lam rho)
    (e : Sec4SectionIso (l41Q1 t x₁ x₂ rho) (l41Y t x₁ x₂ rho)
      CFSG.GH74.GLS.Bg.TwoGroups.Z4Z4) :
    ∀ a ∈ l41Q1 t x₁ x₂ rho, ∀ b ∈ l41Q1 t x₁ x₂ rho, a * b = b * a := by
  obtain ⟨φ, hφ, hker⟩ := e
  obtain ⟨a, ha, b, hb, hgen⟩ := e17_two_gen φ hφ hker
  exact e17_abelian ha hb hgen h.q1facts.Y_le (fun y hy k hk => z18_Y_central h hy hk)
    (fun y hy => z18_Y_sq h.toL41GPh11 hy) (fun x hx x' hx' => z18_Q1_comm h.toL41GPh15 hx hx')
    (fun k hk => z18_conj_Q1 h.toL41GPh15 (z18_rho_mem_M h.toL41GPh14) hk)
    (fun k hk hρ => z18_cent_Q1_rho h.toL41GPh15 hk hρ)

theorem e17_exists_pow4 (e : Sec4SectionIso (l41Q1 t x₁ x₂ rho) (l41Y t x₁ x₂ rho)
      CFSG.GH74.GLS.Bg.TwoGroups.Z4Z4)
    (hΩ : ∀ x ∈ l41Q1 t x₁ x₂ rho, x * x = 1 → x ∈ l41Y t x₁ x₂ rho) :
    ∃ a ∈ l41Q1 t x₁ x₂ rho, a ^ 4 ≠ 1 := by
  obtain ⟨φ, hφ, hker⟩ := e
  obtain ⟨a₀, ha₀⟩ := hφ (Multiplicative.ofAdd ((1, 0) : ZMod 4 × ZMod 4))
  refine ⟨(a₀ : G), a₀.2, fun h4 => ?_⟩
  have hsq : (a₀ : G) ^ 2 * (a₀ : G) ^ 2 = 1 := by rw [← pow_add]; exact h4
  have h2Q : (a₀ : G) ^ 2 ∈ l41Q1 t x₁ x₂ rho := Subgroup.pow_mem _ a₀.2 2
  have hY : (a₀ : G) ^ 2 ∈ l41Y t x₁ x₂ rho := hΩ _ h2Q hsq
  have hmem : (a₀ ^ 2 : ↥(l41Q1 t x₁ x₂ rho)) ∈ φ.ker := by
    rw [hker, Subgroup.mem_subgroupOf]
    exact hY
  have h1 : φ (a₀ ^ 2) = 1 := hmem
  rw [map_pow, ha₀, ← ofAdd_nsmul] at h1
  have h3 : (2 : ℕ) • ((1, 0) : ZMod 4 × ZMod 4) = 0 := h1
  exact absurd h3 (by decide)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
