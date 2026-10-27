module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs
public import CFSG.GH74.GLS.C3.Layer2.FusionTools

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G]

theorem fzr_nonabelian_of_wreath {x₁ x₂ lam : G} (h : WreathRel x₁ x₂ lam) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have h1 : x₂ = x₁ := by
    rw [← h.conj_x₁, hcomm lam x₁]
    group
  have hx : x₁ ∈ zpowers x₁ ⊓ zpowers x₂ :=
    ⟨mem_zpowers x₁, h1 ▸ mem_zpowers x₁⟩
  rw [h.inf_eq_bot, mem_bot] at hx
  have h4 := h.ord_x₁
  rw [hx, orderOf_one] at h4
  exact absurd h4 (by norm_num)

theorem fzr_transfer [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {T M : Subgroup G} (hT : FzSylow T) (hMT : M ≤ T) (hM : M.relIndex T = 2) {g : G}
    (hgT : g ∈ T) (hg : g * g = 1) : ∃ x : G, x⁻¹ * g * x ∈ M := by
  by_cases hgM : g ∈ M
  · exact ⟨1, by simpa using hgM⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hg1 : g ≠ 1 := fun h1 => hgM (h1 ▸ M.one_mem)
    have hg2 : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg) hg1
    have hS : ((hT.1.toSylow hT.2 : Sylow 2 G) : Subgroup G) = T := IsPGroup.toSylow_coe hT.1 hT.2
    exact CFSG.GH74.GLS.C3.Layer2.exists_conj_mem_of_simple ‹IsSimpleGroup G› hnab
      (hT.1.toSylow hT.2) (by rw [hS]; exact hMT) (by rw [hS]; exact hM) hg2

theorem fzr_exists_conj_mem_maximal [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {T M : Subgroup G} (hT : FzSylow T) (hMT : M ≤ T)
    (hM : M.relIndex T = 2) {g : G} (hgT : g ∈ T) (hg : g * g = 1) :
    ∃ m ∈ M, ∃ x : G, x * g * x⁻¹ = m := by
  obtain ⟨x, hx⟩ := fzr_transfer hnab hT hMT hM hgT hg
  exact ⟨_, hx, x⁻¹, by group⟩

end CFSG.OddStandard.SmallF3.FritzII
