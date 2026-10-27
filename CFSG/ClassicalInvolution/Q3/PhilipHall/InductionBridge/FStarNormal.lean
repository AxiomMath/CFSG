module

public import CFSG.Adapters.GeneralizedFitting
public import CFSG.ClassicalInvolution.SubnormalClosure

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge

open CFSG.Open

theorem normal_eq_bot_or_fstar_le {Y : Type} [Group Y] [Finite Y]
    (hS : IsSimpleGroup ↥(genFittingFStar Y)) {N : Subgroup Y} (hN : N.Normal) :
    N = ⊥ ∨ genFittingFStar Y ≤ N := by
  have hLn : (genFittingFStar Y).Normal := CFSG.ClassicalInvolution.genFittingFStar_normal Y
  have hNL : (N.subgroupOf (genFittingFStar Y)).Normal := hN.subgroupOf _
  have := hS
  have := hNL
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (genFittingFStar Y)) with h | h
  · left
    have hinf : N ⊓ genFittingFStar Y = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at h
      exact disjoint_iff.mp h
    have hcomm : ∀ n ∈ N, ∀ l ∈ genFittingFStar Y, l * n = n * l := by
      intro n hn l hl
      have h1 : l * n * l⁻¹ * n⁻¹ ∈ N := N.mul_mem (hN.conj_mem n hn l) (N.inv_mem hn)
      have h2 : l * n * l⁻¹ * n⁻¹ ∈ genFittingFStar Y := by
        have := (genFittingFStar Y).mul_mem hl (hLn.conj_mem l⁻¹ ((genFittingFStar Y).inv_mem hl) n)
        simpa [mul_assoc] using this
      have h3 : l * n * l⁻¹ * n⁻¹ ∈ N ⊓ genFittingFStar Y := ⟨h1, h2⟩
      rw [hinf, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
      exact h3
    have hcent : ∀ n ∈ N, n ∈ genFittingFStar Y := fun n hn =>
      CFSG.Adapters.generalized_fitting_self_centralizing Y
        (Subgroup.mem_centralizer_iff.mpr fun l hl => hcomm n hn l hl)
    rw [eq_bot_iff]
    intro n hn
    have : n ∈ N ⊓ genFittingFStar Y := ⟨hn, hcent n hn⟩
    rwa [hinf] at this
  · right
    exact Subgroup.subgroupOf_eq_top.mp h

theorem center_eq_bot_of_fstar_simple {Y : Type} [Group Y] [Finite Y]
    (hS : IsSimpleGroup ↥(genFittingFStar Y))
    (hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) : Subgroup.center Y = ⊥ := by
  rcases normal_eq_bot_or_fstar_le hS (inferInstance : (Subgroup.center Y).Normal) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    exact Subtype.ext (Subgroup.mem_center_iff.mp (h b.2) a.1)

end CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge
