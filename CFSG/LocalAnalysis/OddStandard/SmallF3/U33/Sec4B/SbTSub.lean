module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem relIndex_eq_two_of_covBy {A B : Subgroup G} (hA : IsPGroup 2 A) (hB : B ⋖ A) :
    B.relIndex A = 2 := by
  have hcoat : IsCoatom (B.subgroupOf A) := by
    rw [SetLike.isCoatom_iff]
    refine ⟨?_, ?_⟩
    · intro htop
      exact not_le_of_gt hB.lt ((Subgroup.subgroupOf_eq_top).mp htop)
    · intro H g hBH hgB hgH
      let c : Subgroup G := H.map A.subtype
      have hcA : c ≤ A := Subgroup.map_subtype_le H
      have hBc : B ≤ c := by
        intro b hb
        have hbA : b ∈ A := hB.le hb
        have hbg : (⟨b, hbA⟩ : ↥A) ∈ B.subgroupOf A := by
          rw [Subgroup.mem_subgroupOf]
          exact hb
        have hHg : (⟨b, hbA⟩ : ↥A) ∈ H := hBH hbg
        exact Subgroup.mem_map.mpr ⟨⟨b, hbA⟩, hHg, rfl⟩
      have hne : B ≠ c := by
        intro hEq
        have hg1c : g.1 ∈ c := Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩
        rw [← hEq] at hg1c
        exact hgB ((Subgroup.mem_subgroupOf).mpr hg1c)
      have hBlt : B < c := lt_of_le_of_ne hBc hne
      have hnot : ¬ c < A := hB.2 hBlt
      have hc_eq : c = A := le_antisymm hcA (by
        by_contra hAc
        exact hnot ⟨hcA, hAc⟩)
      rw [eq_top_iff]
      intro x _
      have hxmem : x.1 ∈ c := by
        rw [hc_eq]
        exact x.2
      rcases Subgroup.mem_map.mp hxmem with ⟨y, hy, hyx⟩
      rw [← Subtype.ext hyx]
      exact hy
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥A := IsPGroup.isNilpotent hA
  have hindex : (B.subgroupOf A).index = 2 :=
    (IsPGroup.isCoatom_iff_index_eq_prime hA).mp hcoat
  exact hindex

theorem card_le_two_mul_card_inf {A B Q : Subgroup G} (hBA : B ≤ A) (hQA : Q.relIndex A = 2) :
    Nat.card B ≤ 2 * Nat.card ↥(B ⊓ Q) := by
  have h1 := Subgroup.relIndex_mul_card (H := B ⊓ Q) (K := B)
  rw [inf_eq_left.mpr inf_le_left] at h1
  have h2 : (B ⊓ Q).relIndex B = Q.relIndex B := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
  rw [h2] at h1
  have h3 : Q.relIndex B ≤ 2 := by
    calc Q.relIndex B ≤ Q.relIndex A :=
          Subgroup.relIndex_le_of_le_right hBA (by rw [hQA]; norm_num)
      _ = 2 := hQA
  rw [← h1]
  exact Nat.mul_le_mul_right _ h3

theorem card_le_mul_card_inf_of_index_le {Q : Subgroup G} {n : ℕ} (hQ : Q.index ≤ n)
    (B : Subgroup G) : Nat.card B ≤ n * Nat.card ↥(B ⊓ Q) := by
  have h1 := Subgroup.relIndex_mul_card (H := B ⊓ Q) (K := B)
  rw [inf_eq_left.mpr inf_le_left] at h1
  have h2 : (B ⊓ Q).relIndex B = Q.relIndex B := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
  rw [h2] at h1
  have h3 : Q.relIndex B ≤ n := by
    calc Q.relIndex B ≤ Q.relIndex ⊤ :=
          Subgroup.relIndex_le_of_le_right le_top
            (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
      _ = Q.index := Subgroup.relIndex_top_right Q
      _ ≤ n := hQ
  rw [← h1]
  exact Nat.mul_le_mul_right _ h3

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
