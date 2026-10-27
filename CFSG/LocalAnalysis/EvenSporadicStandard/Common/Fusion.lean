module

public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.ZStar
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.IndexTwo

public section

namespace CFSG.EvenSporadicStandard

open Subgroup

theorem not_commutator_eq_top_of_index_two {Y : Type*} [Group Y] {N : Subgroup Y}
    (hN : N.index = 2) : commutator Y ≠ ⊤ := by
  intro h
  have hle := commutator_le_of_index_eq_two hN
  rw [h, top_le_iff] at hle
  rw [hle, index_top] at hN
  exact absurd hN (by decide)

theorem not_isPerfect_of_index_eq_two {Y : Type*} [Group Y] {N : Subgroup Y}
    (hN : N.index = 2) : ¬ Group.IsPerfect Y := fun h =>
  not_commutator_eq_top_of_index_two hN (Group.isPerfect_def.1 h)

theorem not_exists_normal_index_two_of_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  rintro ⟨N, hN, hidx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
  · rw [index_bot] at hidx
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic G := isCyclic_of_prime_card hidx
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsCyclic.isMulCommutative.is_comm.comm a b)
  · rw [index_top] at hidx
    exact absurd hidx (by decide)

theorem exists_fused_commuting_involution {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) :
    ∃ g : G, g * t * g⁻¹ ≠ t ∧ (g * t * g⁻¹) * t = t * (g * t * g⁻¹) := by
  have := Fintype.ofFinite G
  by_contra hcon
  have hiso : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t :=
    fun g hg => by_contra fun hne => hcon ⟨g, hne, hg⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by decide)
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  obtain ⟨N, hN, hNodd, hNt⟩ := CFSG.ZStar.glauberman_zStar G t ht1 ht2 hiso
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
  · have hz : t ∈ center G := mem_center_iff.2 fun g => by
      have h1 := hNt g
      rw [mem_bot, mul_inv_eq_one] at h1
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [h1]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact ht1 (mem_bot.1 (h ▸ hz))
    · obtain ⟨a, b, hab⟩ := hnonab
      exact hab (mem_center_iff.1 (h ▸ mem_top b) a)
  · rw [card_top] at hNodd
    have h2 : 2 ∣ Nat.card G := ht ▸ orderOf_dvd_natCard t
    exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 h2)

theorem exists_conj_mem_complement {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {S U : Subgroup G} (hS : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.index) (hUS : U ≤ S) (hU : U.relIndex S = 2) {t : G} (htS : t ∈ S)
    (htU : t ∉ U) (ht2 : orderOf t = 2) : ∃ g : G, g⁻¹ * t * g ∈ U := by
  by_contra hcon
  push Not at hcon
  refine not_exists_normal_index_two_of_nonabelian hnonab
    (CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hS hSidx hUS hU htS htU
      (fun y _ hyU => ?_) hcon)
  have hy : orderOf y ≠ 1 := fun h => hyU (orderOf_eq_one_iff.1 h ▸ U.one_mem)
  have := orderOf_pos y
  omega

end CFSG.EvenSporadicStandard
