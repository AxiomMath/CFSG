module

public import Mathlib.GroupTheory.Nilpotent

public section

open scoped commutatorElement

namespace CFSG.GroupTheory.HuppertProduct

variable {G : Type*} [Group G]

private theorem le_of_le_sup_commutator_top {K : Type*} [Group K] [Group.IsNilpotent K]
    (N A : Subgroup K) [N.Normal] (h : A ≤ N ⊔ ⁅A, (⊤ : Subgroup K)⁆) : A ≤ N := by
  have hsurj : Function.Surjective (QuotientGroup.mk' N : K →* K ⧸ N) :=
    QuotientGroup.mk'_surjective N
  have hnil : Group.IsNilpotent (K ⧸ N) := Group.nilpotent_of_surjective _ hsurj
  have hN : N.map (QuotientGroup.mk' N : K →* K ⧸ N) = ⊥ :=
    (Subgroup.map_eq_bot_iff N).2 (QuotientGroup.ker_mk' N).ge
  have hA : A.map (QuotientGroup.mk' N : K →* K ⧸ N) ≤
      ⁅A.map (QuotientGroup.mk' N : K →* K ⧸ N), (⊤ : Subgroup (K ⧸ N))⁆ := by
    have h' := Subgroup.map_mono (f := (QuotientGroup.mk' N : K →* K ⧸ N)) h
    rw [Subgroup.map_sup, hN, bot_sup_eq, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hsurj] at h'
    exact h'
  have key : ∀ k : ℕ, A.map (QuotientGroup.mk' N : K →* K ⧸ N) ≤
      (⊤ : Subgroup (K ⧸ N)).lowerCentralSeries k := by
    intro k
    induction k with
    | zero => rw [Subgroup.lowerCentralSeries_zero]; exact le_top
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      exact hA.trans (Subgroup.commutator_mono ih le_rfl)
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.1 hnil
  have hbot : A.map (QuotientGroup.mk' N : K →* K ⧸ N) = ⊥ :=
    le_bot_iff.1 ((key n).trans hn.le)
  intro a ha
  have hmem : (QuotientGroup.mk' N : K →* K ⧸ N) a ∈ A.map (QuotientGroup.mk' N : K →* K ⧸ N) :=
    Subgroup.mem_map_of_mem _ ha
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff a).1 hmem

theorem le_of_le_sup_commutator {H Q L : Subgroup G} (hH : Group.IsNilpotent H) (hQH : Q ≤ H)
    (hQ : H ≤ Subgroup.normalizer (Q : Set G)) (hLH : L ≤ H) (h : L ≤ Q ⊔ ⁅L, H⁆) : L ≤ Q := by
  haveI : (Q.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQ
  have hT : L.subgroupOf H ≤ Q.subgroupOf H ⊔ ⁅L.subgroupOf H, (⊤ : Subgroup H)⁆ := by
    refine Subgroup.map_subtype_le_map_subtype.1 ?_
    rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLH,
      Subgroup.map_subgroupOf_eq_of_le hQH, Subgroup.map_top, Subgroup.range_subtype]
    exact h
  intro y hy
  have hyH : y ∈ H := hLH hy
  have hy' : (⟨y, hyH⟩ : H) ∈ L.subgroupOf H := hy
  exact Subgroup.mem_subgroupOf.1
    (le_of_le_sup_commutator_top (Q.subgroupOf H) (L.subgroupOf H) hT hy')

end CFSG.GroupTheory.HuppertProduct
