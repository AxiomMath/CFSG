module

public import CFSG.GH74.Uniqueness.SU.SU2Final
public import CFSG.GH74.Uniqueness.SU.SU2Cases

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

variable {X : Type} [Group X] {V : Type} [Group V] [MulDistribMulAction X V]

theorem fixSub_subgroupOf {Y K : Subgroup X} (hYK : Y ≤ K) :
    fixSub V (Y.subgroupOf K) = fixSub V Y := by
  ext v
  rw [mem_fixSub, mem_fixSub]
  constructor
  · intro h y hy
    exact h ⟨y, hYK hy⟩ hy
  · intro h y hy
    exact h y hy

theorem commSub_subgroupOf {Y K : Subgroup X} (hYK : Y ≤ K) :
    commSub V (Y.subgroupOf K) = commSub V Y := by
  unfold commSub
  congr 1
  ext u
  constructor
  · rintro ⟨y, hy, v, rfl⟩
    exact ⟨y, hy, v, rfl⟩
  · rintro ⟨y, hy, v, rfl⟩
    exact ⟨⟨y, hYK hy⟩, hy, v, rfl⟩

theorem GOPair.restrict {Y : Subgroup X} (hGO : GOPair V Y) {K : Subgroup X} (hYK : Y ≤ K) :
    GOPair V (Y.subgroupOf K) where
  exp_two := hGO.exp_two
  faithful := fun x hx => Subtype.ext (hGO.faithful x (fun v => hx v))
  isCyclic := by
    have := hGO.isCyclic
    exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hYK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hYK).injective
  odd_card := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv]
    exact hGO.odd_card
  ne_bot := by
    intro h
    apply hGO.ne_bot
    rw [Subgroup.eq_bot_iff_card] at h ⊢
    rw [← h]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv).symm
  transitive := by
    rw [commSub_subgroupOf hYK]
    intro v hv hv1 w hw hw1
    obtain ⟨y, hy, hyv⟩ := hGO.transitive v hv hv1 w hw hw1
    exact ⟨⟨y, hYK hy⟩, hy, hyv⟩
  fixSub_ne_bot := by
    rw [fixSub_subgroupOf hYK]
    exact hGO.fixSub_ne_bot
  inter_trivial := by
    rw [fixSub_subgroupOf hYK]
    intro x₁ x₂ h
    exact hGO.inter_trivial (x₁ : X) (x₂ : X) h
  normal_in_stab := by
    rw [fixSub_subgroupOf hYK]
    intro x hx y hy
    exact hGO.normal_in_stab (x : X) hx (y : X) hy

theorem onan_odd [Finite X] [Finite V] {Y : Subgroup X} (hGO : GOPair V Y)
    (hodd : Odd (Nat.card X)) : OnanConclusion V Y := by
  rcases hGO.step12 with h | ⟨⟨W₁, hW₁⟩, ⟨W₂, hW₂⟩⟩
  · exact h
  · exact Or.inr (Or.inr (Or.inr (hGO.odd_case hodd hW₁ hW₂)))

end CFSG.GH74.Uniqueness.SU.SU2
