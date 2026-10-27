module

public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalOrder504Sylow

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

variable {G : Type*} [Group G]

open Subgroup

theorem card_centralizer_sylow_five_le [Finite G] [IsSimpleGroup G] (P : Sylow 5 G)
    (hP : Nat.card (P : Subgroup G) = 5) (hn : Nat.card (Sylow 5 G) = 6) :
    Nat.card (centralizer ((P : Subgroup G) : Set G)) ≤ 5 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hPn : ¬ (P : Subgroup G).Normal := by
    intro hnormal
    haveI : Unique (Sylow 5 G) := Sylow.unique_of_normal P hnormal
    have : Nat.card (Sylow 5 G) = 1 := Nat.card_unique
    omega
  let _ : Fintype (Sylow 5 G) := Fintype.ofFinite _
  have hinj :=
    CFSG.ComponentClassification.LiteratureLocal.Order504.toPermHom_sylow_injective P hPn
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [hP])
  have hx : orderOf (y : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hy
  have hσ : orderOf (MulAction.toPermHom G (Sylow 5 G) y) = 5 := by
    rw [orderOf_injective _ hinj]
    exact hx
  have hcard : Fintype.card (Sylow 5 G) = 5 + 1 := by
    rw [← Nat.card_eq_fintype_card, hn]
  have hcent := CFSG.LocalAnalysis.ComponentInitial.centralizer_singleton_eq (p := 5) hcard hσ
  have hCx : Nat.card (centralizer ({(y : G)} : Set G)) ≤ 5 := by
    have hle : (centralizer ({(y : G)} : Set G)).map (MulAction.toPermHom G (Sylow 5 G)) ≤
        centralizer {MulAction.toPermHom G (Sylow 5 G) y} := by
      rintro _ ⟨g, hg, rfl⟩
      have hg' : g ∈ centralizer ({(y : G)} : Set G) := hg
      rw [mem_centralizer_singleton_iff] at hg' ⊢
      rw [← map_mul, hg', map_mul]
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective hinj, hcent, Nat.card_zpowers, hσ] at this
  exact (Subgroup.card_le_of_le
    (centralizer_le (Set.singleton_subset_iff.mpr y.2))).trans hCx

end CFSG.GroupTheory.SmallFixedTwoGroup
