module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem mem_center_of_card_center_centralizer_le_two {R : Type*} [Group R] [Finite R]
    (hR : IsPGroup 2 R) {s : R} (hs : s * s = 1) (hs1 : s ≠ 1)
    (hZ : Nat.card (center (centralizer ({s} : Set R))) ≤ 2) : s ∈ center R := by
  let C : Subgroup R := centralizer ({s} : Set R)
  have hsC : s ∈ C := by
    show s ∈ centralizer ({s} : Set R)
    rw [Subgroup.mem_centralizer_singleton_iff]
  let sC : C := ⟨s, hsC⟩
  have hsC_ne_one : sC ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  have hsC_mem_center : sC ∈ center C := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    change (c : R) * s = s * (c : R)
    exact Subgroup.mem_centralizer_singleton_iff.mp c.2
  let z0 : center C := ⟨sC, hsC_mem_center⟩
  have hz0_ne_one : z0 ≠ 1 := fun h => hsC_ne_one (congrArg Subtype.val h)
  haveI : Nontrivial (center C) := ⟨z0, 1, hz0_ne_one⟩
  have h2le : 2 ≤ Nat.card (center C) := by
    have := Finite.one_lt_card (α := center C)
    omega
  have hZeq2 : Nat.card (center C) = 2 := le_antisymm hZ h2le
  have hz_eq : ∀ z : center C, z = 1 ∨ z = z0 := by
    intro z
    by_cases hz : z = 1
    · exact Or.inl hz
    · right
      obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : center C)).mp hZeq2
      exact (huniq z hz).trans (huniq z0 hz0_ne_one).symm
  have hN_le : normalizer (C : Set R) ≤ C := by
    intro n hn
    have hn_s : n * s * n⁻¹ ∈ C := (Subgroup.mem_set_normalizer_iff.mp hn s).mp hsC
    let zC : C := ⟨n * s * n⁻¹, hn_s⟩
    have hzC_center : zC ∈ center C := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      have hnin : n⁻¹ ∈ normalizer (C : Set R) := inv_mem hn
      have hwC : n⁻¹ * (c : R) * n ∈ C := by
        simpa using (Subgroup.mem_set_normalizer_iff.mp hnin (c : R)).mp c.2
      have hval : (n⁻¹ * (c : R) * n) * s = s * (n⁻¹ * (c : R) * n) := by
        simpa using congrArg Subtype.val
          (Subgroup.mem_center_iff.mp hsC_mem_center ⟨n⁻¹ * (c : R) * n, hwC⟩)
      show (c : R) * (n * s * n⁻¹) = (n * s * n⁻¹) * (c : R)
      have hconj : n * ((n⁻¹ * (c : R) * n) * s) * n⁻¹
          = n * (s * (n⁻¹ * (c : R) * n)) * n⁻¹ := by rw [hval]
      calc (c : R) * (n * s * n⁻¹)
          = n * ((n⁻¹ * (c : R) * n) * s) * n⁻¹ := by group
        _ = n * (s * (n⁻¹ * (c : R) * n)) * n⁻¹ := hconj
        _ = (n * s * n⁻¹) * (c : R) := by group
    let zZ : center C := ⟨zC, hzC_center⟩
    have hzZ_ne_one : zZ ≠ 1 := by
      intro h
      have h1 : zC = 1 := congrArg (fun x : center C => (x : C)) h
      have h3 : s = 1 := by
        have h2 : (zC : R) = 1 := congrArg (fun x : C => (x : R)) h1
        have h2' : n * s * n⁻¹ = 1 := h2
        calc s = n⁻¹ * (n * s * n⁻¹) * n := by group
          _ = n⁻¹ * 1 * n := by rw [h2']
          _ = 1 := by group
      exact hs1 h3
    have hz_eq_z0 : zZ = z0 := by
      rcases hz_eq zZ with h | h
      · exact absurd h hzZ_ne_one
      · exact h
    have hns : n * s * n⁻¹ = s := by
      have h1 : zC = sC := congrArg Subtype.val hz_eq_z0
      exact congrArg Subtype.val h1
    show n ∈ centralizer ({s} : Set R)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * s = n * s * n⁻¹ * n := by group
      _ = s * n := by rw [hns]
  have hnormalizer_eq : normalizer (C : Set R) = C :=
    le_antisymm hN_le Subgroup.le_normalizer
  haveI : Group.IsNilpotent R := hR.isNilpotent
  have hnc : NormalizerCondition R := Group.normalizerCondition_of_isNilpotent
  have hCtop : C = ⊤ := by
    by_contra hne
    have hlt : C < ⊤ := lt_of_le_of_ne le_top hne
    have hstep : C < normalizer C := hnc C hlt
    rw [hnormalizer_eq] at hstep
    exact (lt_irrefl C) hstep
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ C := by rw [hCtop]; trivial
  have hg' : g ∈ centralizer ({s} : Set R) := hg
  exact Subgroup.mem_centralizer_singleton_iff.mp hg'

end CFSG.GroupTheory.SmallFixedTwoGroup
