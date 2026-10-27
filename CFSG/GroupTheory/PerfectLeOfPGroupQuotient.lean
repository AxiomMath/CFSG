module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace Subgroup

variable {G : Type*} [Group G]

theorem le_of_commutator_eq_self_of_isSolvable_quotient {M H : Subgroup G} [M.Normal]
    [Group.IsSolvable (G ⧸ M)] (hH : ⁅H, H⁆ = H) : H ≤ M := by
  have hmap : ⁅H.map (QuotientGroup.mk' M), H.map (QuotientGroup.mk' M)⁆
      = H.map (QuotientGroup.mk' M) := by
    rw [← Subgroup.map_commutator, hH]
  have hbot : H.map (QuotientGroup.mk' M) = ⊥ := by
    by_contra hne
    have hlt := Group.IsSolvable.commutator_lt_of_ne_bot (G := G ⧸ M) hne
    rw [hmap] at hlt
    exact (lt_irrefl _) hlt
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

theorem le_of_commutator_eq_self_of_index_eq_prime_pow {M H : Subgroup G} [M.Normal] {p k : ℕ}
    (hp : p.Prime) (hM : M.index = p ^ k) (hH : ⁅H, H⁆ = H) : H ≤ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : M.index ≠ 0 := by
    rw [hM]
    exact pow_ne_zero k hp.ne_zero
  haveI : Finite (G ⧸ M) := Subgroup.index_ne_zero_iff_finite.mp hne
  have hcard : Nat.card (G ⧸ M) = p ^ k := by
    rw [← Subgroup.index_eq_card, hM]
  have hP : IsPGroup p (G ⧸ M) := IsPGroup.of_card hcard
  haveI : Group.IsNilpotent (G ⧸ M) := hP.isNilpotent
  exact le_of_commutator_eq_self_of_isSolvable_quotient hH

theorem le_of_commutator_eq_self_of_relIndex_eq_prime_pow {D C H : Subgroup G} {p k : ℕ}
    (hp : p.Prime) (hDC : D ≤ C) (hn : C ≤ normalizer (D : Set G)) (hidx : D.relIndex C = p ^ k)
    (hHC : H ≤ C) (hH : ⁅H, H⁆ = H) : H ≤ D := by
  haveI : (D.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDC).2 hn
  have hH' : ⁅H.subgroupOf C, H.subgroupOf C⁆ = H.subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hHC, hH]
  have hle : H.subgroupOf C ≤ D.subgroupOf C :=
    le_of_commutator_eq_self_of_index_eq_prime_pow (M := D.subgroupOf C) (H := H.subgroupOf C) hp
      (by simpa only [Subgroup.relIndex] using hidx) hH'
  intro x hx
  exact hle (show (⟨x, hHC hx⟩ : C) ∈ H.subgroupOf C from hx)

end Subgroup
