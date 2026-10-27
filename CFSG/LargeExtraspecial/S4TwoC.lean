module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

theorem card_le_finrank_add_one_of_beta_eq_one [FiniteDimensional (ZMod 2) V] (hβ : β.IsAlt)
    {s : Finset V} (hs : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → β x y = 1) :
    s.card ≤ finrank (ZMod 2) V + 1 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp
  set s' := s.erase p₀ with hs'
  have hli : LinearIndependent (ZMod 2) (fun x : s' => (x : V)) := by
    rw [linearIndependent_iff']
    intro t c hsum k hk
    have hmem : ∀ i : s', (i : V) ∈ s := fun i => Finset.mem_of_mem_erase i.2
    have hne : ∀ i : s', (i : V) ≠ p₀ := fun i => Finset.ne_of_mem_erase i.2
    have h1 : ∑ i ∈ t, c i = 0 := by
      have := congrArg (fun w => β w p₀) hsum
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        map_zero, LinearMap.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hs _ (hmem i) _ hp₀ (hne i), mul_one]
    have h2 : ∑ i ∈ t, c i * β (i : V) k = 0 := by
      have := congrArg (fun w => β w k) hsum
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        map_zero, LinearMap.zero_apply] at this
      exact this
    have h3 : ∑ i ∈ t, c i * β (i : V) k = ∑ i ∈ t, c i - c k := by
      rw [← Finset.sum_erase_add t _ hk, ← Finset.sum_erase_add t c hk, hβ.self_eq_zero,
        mul_zero, add_zero, add_sub_cancel_right]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : (i : V) ≠ k := fun h => (Finset.ne_of_mem_erase hi) (Subtype.ext h)
      rw [hs _ (hmem i) _ (hmem k) hik, mul_one]
    rw [h3, h1, zero_sub, neg_eq_zero] at h2
    exact h2
  have h1 := hli.finset_card_le_finrank (b := s')
  have h2 : s'.card + 1 = s.card := Finset.card_erase_add_one hp₀
  omega

end CFSG.LargeExtraspecial.S4
