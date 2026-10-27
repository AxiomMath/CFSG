module

public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

theorem mem_zpowers_or_coset {G : Type} [Group G] [Finite G] {P : Subgroup G} {u b : G}
    (hP : Nat.card P = 2 * orderOf u) (huP : u ∈ P) (hbP : b ∈ P)
    (hb : b ∉ Subgroup.zpowers u) :
    ∀ s ∈ P, s ∈ Subgroup.zpowers u ∨ b⁻¹ * s ∈ Subgroup.zpowers u := by
  intro s hs
  by_cases hsu : s ∈ Subgroup.zpowers u
  · exact Or.inl hsu
  refine Or.inr ?_
  obtain ⟨U, hU⟩ : ∃ U : Subgroup P, U = (Subgroup.zpowers u).subgroupOf P := ⟨_, rfl⟩
  have hle : Subgroup.zpowers u ≤ P := Subgroup.zpowers_le.mpr huP
  have hcardU : Nat.card U = orderOf u := by
    rw [hU, ← Nat.card_zpowers u]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hidx : U.index = 2 := by
    have h := Subgroup.card_mul_index (H := U)
    rw [hcardU, hP] at h
    exact Nat.eq_of_mul_eq_mul_left (orderOf_pos u) (h.trans (mul_comm _ _))
  obtain ⟨a, _, hcos⟩ := Subgroup.index_eq_two_iff_exists_notMem_and'.mp hidx
  have hsU : (⟨s, hs⟩ : P) ∉ U := by
    rw [hU]
    exact fun h => hsu (Subgroup.mem_subgroupOf.mp h)
  have hbU : (⟨b, hbP⟩ : P) ∉ U := by
    rw [hU]
    exact fun h => hb (Subgroup.mem_subgroupOf.mp h)
  have has : a * ⟨s, hs⟩ ∈ U := (hcos _).resolve_right hsU
  have hab : a * ⟨b, hbP⟩ ∈ U := (hcos _).resolve_right hbU
  have key : (⟨b, hbP⟩ : P)⁻¹ * ⟨s, hs⟩ ∈ U := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hab) has
    simpa [mul_assoc] using h
  rw [hU] at key
  exact Subgroup.mem_subgroupOf.mp key

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
