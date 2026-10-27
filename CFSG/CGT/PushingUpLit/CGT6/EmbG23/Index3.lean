module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbG23

open scoped commutatorElement

theorem eq_top_of_perfect_index_dvd_two {Y : Type*} [Group Y] [Group.IsPerfect Y]
    {N : Subgroup Y} [N.Normal] (hN : N.index ∣ 2) : N = ⊤ := by
  have hne : N.index ≠ 0 := fun h => by rw [h] at hN; exact absurd (zero_dvd_iff.1 hN) two_ne_zero
  have hfin : Finite (Y ⧸ N) := Nat.finite_of_card_ne_zero hne
  have hcomm : ∀ x y : Y ⧸ N, x * y = y * x := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hN with h | h
    · have hsub : Subsingleton (Y ⧸ N) := by
        have h1 : Nat.card (Y ⧸ N) = 1 := h
        exact (Nat.card_eq_one_iff_unique.1 h1).1
      intro x y
      exact Subsingleton.elim _ _
    · have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcyc : IsCyclic (Y ⧸ N) := isCyclic_of_prime_card (p := 2) h
      have := hcyc.isMulCommutative
      intro x y
      exact this.is_comm.comm x y
  have hle : commutator Y ≤ N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h1 : (QuotientGroup.mk' N) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact (commutatorElement_eq_one_iff_mul_comm).2 (hcomm _ _)
    exact (QuotientGroup.eq_one_iff _).1 h1
  rw [eq_top_iff]
  have := Group.IsPerfect.commutator_eq_top (G := Y)
  rw [← this]
  exact hle

theorem normal_of_perfect_index_three {M : Type*} [Group M] {Y : Subgroup M}
    [Group.IsPerfect ↥Y] (hidx : Y.index = 3) : Y.Normal := by
  have hfin : Finite (M ⧸ Y) :=
    Nat.finite_of_card_ne_zero (by change Y.index ≠ 0; rw [hidx]; norm_num)
  have hcard : Nat.card (M ⧸ Y) = 3 := hidx
  set K : Subgroup M := Y.normalCore with hK
  have hKY : K ≤ Y := Subgroup.normalCore_le Y
  have hKn : K.Normal := Subgroup.normalCore_normal Y
  have hKker : K = (MulAction.toPermHom M (M ⧸ Y)).ker := Subgroup.normalCore_eq_ker Y
  have hKidx : K.index ∣ 6 := by
    rw [hKker, Subgroup.index_ker]
    have h1 := Subgroup.card_subgroup_dvd_card (MulAction.toPermHom M (M ⧸ Y)).range
    rwa [Nat.card_perm, hcard, show Nat.factorial 3 = 6 from rfl] at h1
  have hrel := Subgroup.relIndex_mul_index hKY
  rw [hidx] at hrel
  have hrel2 : K.relIndex Y ∣ 2 := by
    rw [← hrel] at hKidx
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 3) (by simpa [mul_comm] using hKidx)
  have hnorm : (K.subgroupOf Y).Normal := hKn.subgroupOf Y
  have htop : K.subgroupOf Y = ⊤ :=
    eq_top_of_perfect_index_dvd_two (N := K.subgroupOf Y) hrel2
  have hYK : Y ≤ K := Subgroup.subgroupOf_eq_top.1 htop
  have : K = Y := le_antisymm hKY hYK
  rw [← this]
  exact hKn

theorem mem_of_perfect_index_three {M : Type*} [Group M] {Y : Subgroup M}
    [Group.IsPerfect ↥Y] (hidx : Y.index = 3) {x : M} (hx : (orderOf x).Coprime 3) : x ∈ Y := by
  have hY := normal_of_perfect_index_three (Y := Y) hidx
  have hcard : Nat.card (M ⧸ Y) = 3 := hidx
  have h1 : orderOf (QuotientGroup.mk' Y x) ∣ orderOf x := orderOf_map_dvd _ x
  have h2 : orderOf (QuotientGroup.mk' Y x) ∣ 3 := hcard ▸ orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk' Y x) ∣ Nat.gcd (orderOf x) 3 := Nat.dvd_gcd h1 h2
  rw [hx] at h3
  have h4 : orderOf (QuotientGroup.mk' Y x) = 1 := Nat.dvd_one.1 h3
  have h5 : QuotientGroup.mk' Y x = 1 := orderOf_eq_one_iff.1 h4
  exact (QuotientGroup.eq_one_iff x).1 h5

end CFSG.CGT.PushingUpLit.CGT6.EmbG23
