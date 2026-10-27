module

public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.OddStandard.AltStdFaithful

open Subgroup

theorem card_le_two_of_isCyclic_of_sq {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (h : ∀ a : H, a ^ 2 = 1) : Nat.card H ≤ 2 := by
  classical
  let _ := Fintype.ofFinite H
  have hle := IsCyclic.card_pow_eq_one_le (α := H) (n := 2) (by norm_num)
  rw [Finset.filter_true_of_mem fun a _ => h a, Finset.card_univ] at hle
  rwa [Nat.card_eq_fintype_card]

theorem not_isCyclic_sylow_two {H : Type*} [Group H] [Finite H] (S : Sylow 2 H) {x y : H}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x ≠ y) (hc : x * y = y * x) :
    ¬ IsCyclic S := by
  intro hS
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    omega
  have hcomm : ({x, y} : Set H).Pairwise Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hc
    · exact hc.symm
    · exact Commute.refl _
  have hEc : IsMulCommutative (Subgroup.closure ({x, y} : Set H)) :=
    Subgroup.isMulCommutative_closure hcomm
  have hsq : ∀ k (hk : k ∈ Subgroup.closure ({x, y} : Set H)), k ^ 2 = 1 := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hx2
      · exact hy2
    | one => simp
    | mul a b ha hb iha ihb =>
      have hab : a * b = b * a :=
        congrArg Subtype.val (hEc.is_comm.comm (⟨a, ha⟩ : Subgroup.closure ({x, y} : Set H))
          ⟨b, hb⟩)
      calc (a * b) ^ 2 = a * b * (a * b) := sq _
        _ = a * (b * a) * b := by simp only [mul_assoc]
        _ = a * (a * b) * b := by rw [← hab]
        _ = a * a * (b * b) := by simp only [mul_assoc]
        _ = 1 := by rw [← sq, ← sq, iha, ihb, one_mul]
    | inv a ha iha =>
      rw [inv_pow, iha, inv_one]
  have hP : IsPGroup 2 (Subgroup.closure ({x, y} : Set H)) := fun g =>
    ⟨1, Subtype.ext (by simpa using hsq g g.2)⟩
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  have hxQ : x ∈ (Q : Subgroup H) := hQ (Subgroup.subset_closure (Set.mem_insert _ _))
  have hyQ : y ∈ (Q : Subgroup H) :=
    hQ (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hQc : IsCyclic (Q : Subgroup H) := ((Sylow.equiv S Q).isCyclic).1 hS
  let _ := Fintype.ofFinite (Q : Subgroup H)
  have hle := IsCyclic.card_pow_eq_one_le (α := (Q : Subgroup H)) (n := 2) (by norm_num)
  have hsub : ({1, ⟨x, hxQ⟩, ⟨y, hyQ⟩} : Finset (Q : Subgroup H)) ⊆
      Finset.univ.filter fun a : (Q : Subgroup H) => a ^ 2 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow _
    · exact Subtype.ext (by simpa using hx2)
    · exact Subtype.ext (by simpa using hy2)
  have h3 : ({1, ⟨x, hxQ⟩, ⟨y, hyQ⟩} : Finset (Q : Subgroup H)).card = 3 := by
    refine Finset.card_eq_three.2 ⟨1, ⟨x, hxQ⟩, ⟨y, hyQ⟩, ?_, ?_, ?_, rfl⟩
    · intro h
      exact hx1 (congrArg Subtype.val h).symm
    · intro h
      exact hy1 (congrArg Subtype.val h).symm
    · intro h
      exact hxy (congrArg Subtype.val h)
  have := Finset.card_le_card hsub
  omega

theorem pRank_two_eq_one_of_isCyclic {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    (hC : Even (Nat.card C)) (S : Sylow 2 C) (hS : IsCyclic S) : CFSG.Open.pRank 2 C = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : 1 < 2 := by norm_num
  refine le_antisymm ?_ ?_
  · rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 2) C,
      ← (CFSG.SectionRank.pRank_sylow S).1]
    refine CFSG.SectionRank.pRank_le hp fun E hES hE => ?_
    have : IsCyclic (S : Subgroup C) := hS
    have : IsCyclic E := Subgroup.isCyclic_of_le hES
    have hsq : ∀ a : E, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hE.2 a a.2)
    simpa using card_le_two_of_isCyclic_of_sq hsq
  · obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hC)
    have hu' : orderOf (u : G) = 2 := (Subgroup.orderOf_coe u).trans hu
    refine CFSG.SectionRank.le_pRank hp (E := Subgroup.zpowers (u : G))
      (Subgroup.zpowers_le.2 u.2) ⟨inferInstance, ?_⟩ ?_
    · intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hu', pow_orderOf_eq_one,
        one_zpow]
    · rw [Nat.card_zpowers, hu', pow_one]

end CFSG.OddStandard.AltStdFaithful
