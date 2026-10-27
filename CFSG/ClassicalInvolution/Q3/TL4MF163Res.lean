module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

namespace MF163

variable {X : Type} [Group X]

theorem map_eq_of_centralizer_eq_bot [Finite X] {N : Subgroup X} [hNn : N.Normal]
    [IsSimpleGroup N] (hC : Subgroup.centralizer (N : Set X) = ⊥) (β : MulAut X) :
    N.map (β : X →* X) = N := by
  set M := N.map (β : X →* X) with hM
  have hMn : M.Normal := hNn.map _ β.surjective
  have hNM : N ⊓ M ≠ ⊥ := by
    intro h
    have hMC : M ≤ Subgroup.centralizer (N : Set X) := by
      intro m hm
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 : n * m * n⁻¹ * m⁻¹ ∈ N ⊓ M := by
        refine Subgroup.mem_inf.2 ⟨?_, M.mul_mem (hMn.conj_mem m hm n) (inv_mem hm)⟩
        simpa only [mul_assoc] using N.mul_mem hn (hNn.conj_mem n⁻¹ (inv_mem hn) m)
      rw [h, Subgroup.mem_bot] at h1
      calc n * m = n * m * n⁻¹ * m⁻¹ * (m * n) := by group
        _ = m * n := by rw [h1, one_mul]
    have hM1 : M = ⊥ := le_bot_iff.1 (hC ▸ hMC)
    rw [hM, Subgroup.map_eq_bot_iff_of_injective _ β.injective] at hM1
    exact (Subgroup.nontrivial_iff_ne_bot N).1 inferInstance hM1
  have hle : N ≤ M := by
    have : (N ⊓ M).Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ M).subgroupOf N) with h | h
    · exfalso
      apply hNM
      rw [Subgroup.subgroupOf_eq_bot] at h
      exact h.eq_bot_of_le inf_le_left
    · rw [Subgroup.subgroupOf_eq_top] at h
      exact h.trans inf_le_right
  exact (Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective β.injective))).symm

theorem eq_of_eqOn {N : Subgroup X} [hNn : N.Normal] (hC : Subgroup.centralizer (N : Set X) = ⊥)
    {β₁ β₂ : MulAut X} (hmap : N.map (β₂ : X →* X) = N) (h : ∀ n ∈ N, β₁ n = β₂ n) :
    β₁ = β₂ := by
  ext x
  have hg : (β₂ x)⁻¹ * β₁ x ∈ Subgroup.centralizer (N : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    rw [← hmap] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    have h1 := h (x * n * x⁻¹) (hNn.conj_mem n hn x)
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, h n hn] at h1
    have h2 : β₁ x * β₂ n = β₂ x * β₂ n * (β₂ x)⁻¹ * β₁ x := by
      calc β₁ x * β₂ n = (β₁ x * β₂ n * (β₁ x)⁻¹) * β₁ x := by group
        _ = β₂ x * β₂ n * (β₂ x)⁻¹ * β₁ x := by rw [h1]
    change β₂ n * ((β₂ x)⁻¹ * β₁ x) = ((β₂ x)⁻¹ * β₁ x) * β₂ n
    calc β₂ n * ((β₂ x)⁻¹ * β₁ x) = (β₂ x)⁻¹ * (β₂ x * β₂ n * (β₂ x)⁻¹ * β₁ x) := by group
      _ = (β₂ x)⁻¹ * (β₁ x * β₂ n) := by rw [h2]
      _ = (β₂ x)⁻¹ * β₁ x * β₂ n := by group
  rw [hC, Subgroup.mem_bot] at hg
  exact (inv_mul_eq_one.1 hg).symm

noncomputable def restrictAut {N : Subgroup X} (β : MulAut X) (hβ : N.map (β : X →* X) = N) :
    MulAut N :=
  (MulEquiv.subgroupMap β N).trans (MulEquiv.subgroupCongr hβ)

theorem coe_restrictAut {N : Subgroup X} (β : MulAut X) (hβ : N.map (β : X →* X) = N) (n : N) :
    ((restrictAut β hβ n : N) : X) = β n := by
  simp [restrictAut, MulEquiv.coe_subgroupMap_apply]

end MF163

end CFSG.ClassicalInvolution.Q3.TL4
