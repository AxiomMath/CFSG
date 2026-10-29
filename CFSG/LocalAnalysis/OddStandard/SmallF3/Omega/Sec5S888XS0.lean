module

public import Mathlib.GroupTheory.Index

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X]

private lemma relIndex_eq_two_of_card_le [Finite X] {J I : Subgroup X} (hIJ : I ≤ J)
    (hcard : Nat.card J ≤ 2 * Nat.card I) {a : X} (ha : a ∈ J) (haI : a ∉ I) :
    I.relIndex J = 2 := by
  have hrel : I.relIndex J * Nat.card I = Nat.card J := by
    simpa only [inf_of_le_left hIJ] using (Subgroup.relIndex_mul_card (H := I) (K := J))
  have hIpos : 0 < Nat.card I := by
    haveI : Finite I := Finite.of_injective (fun x : I => (x : X)) Subtype.val_injective
    haveI : Nonempty I := ⟨1⟩
    exact Nat.card_pos
  have hle : I.relIndex J ≤ 2 := by
    refine Nat.le_of_mul_le_mul_right ?_ hIpos
    rw [hrel]
    exact hcard
  have hne1 : I.relIndex J ≠ 1 := fun h => haI ((Subgroup.relIndex_eq_one.mp h) ha)
  have hne0 : I.relIndex J ≠ 0 := by
    intro h
    have hJpos : 0 < Nat.card J := by
      haveI : Finite J := Finite.of_injective (fun x : J => (x : X)) Subtype.val_injective
      haveI : Nonempty J := ⟨1⟩
      exact Nat.card_pos
    rw [← hrel, h, Nat.zero_mul] at hJpos
    exact absurd hJpos (lt_irrefl 0)
  omega

theorem mem_of_triple_of_card_le [Finite X] {J I : Subgroup X} (hIJ : I ≤ J)
    (hcard : Nat.card J ≤ 2 * Nat.card I) {a b c : X} (ha : a ∈ J) (hb : b ∈ J) (hc : c ∈ J)
    (habc : a * b * c = 1) : a ∈ I ∨ b ∈ I ∨ c ∈ I := by
  by_contra h
  push Not at h
  obtain ⟨haI, hbI, hcI⟩ := h
  have hrel : I.relIndex J = 2 := relIndex_eq_two_of_card_le hIJ hcard ha haI
  let K : Subgroup J := I.subgroupOf J
  have hK : K.index = 2 := by simpa only [K, Subgroup.relIndex] using hrel
  let A : J := ⟨a, ha⟩
  let B : J := ⟨b, hb⟩
  let C : J := ⟨c, hc⟩
  have hAK : A ∉ K := by
    intro hA
    exact haI (by simpa only [K, A] using (Subgroup.mem_subgroupOf.mp hA))
  have hBK : B ∉ K := by
    intro hB
    exact hbI (by simpa only [K, B] using (Subgroup.mem_subgroupOf.mp hB))
  have hCK : C ∉ K := by
    intro hC
    exact hcI (by simpa only [K, C] using (Subgroup.mem_subgroupOf.mp hC))
  have hAB : A * B ∈ K := by
    rw [Subgroup.mul_mem_iff_of_index_two hK]
    exact ⟨fun h => absurd h hAK, fun h => absurd h hBK⟩
  have hABC : A * B * C ∉ K := by
    rw [Subgroup.mul_mem_iff_of_index_two hK]
    intro hiff
    exact hCK (hiff.mp hAB)
  have h1 : A * B * C = 1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_one, A, B, C] using habc
  exact hABC (h1.symm ▸ K.one_mem)

end CFSG.OddStandard.SmallF3.Omega
