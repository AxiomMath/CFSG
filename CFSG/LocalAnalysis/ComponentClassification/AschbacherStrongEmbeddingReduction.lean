module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingTransport

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

@[expose] def NormStatement (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X ≤ n →
    ∀ (M : Subgroup X) (x : X), orderOf x = 2 → M ≠ ⊤ →
      (∀ g : X, x ∈ rightConjugate M g ↔ g ∈ M) → CentralProductCentralizer M x →
      involutionPointHull x = ⊤ → CFSG.oddCore X = ⊥ → NormSplit X M x

theorem pointHullStrongSplit_of_normStatement {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {z : G} (hz : orderOf z = 2) (hH : H ≠ ⊤)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (h2 : CentralProductCentralizer H z)
    (hnorm : NormStatement (Nat.card G)) : PointHullStrongSplit H z := by
  by_cases hiso : ∀ t ∈ involutionPointClass z, Commute z t → t = z
  · exact Or.inl (twoRank_hull_le_one_of_isolated hz h2.1 hiso)
  obtain ⟨t, ht, hzt, hne⟩ : ∃ t ∈ involutionPointClass z, Commute z t ∧ t ≠ z := by
    by_contra h
    apply hiso
    intro t ht hzt
    by_contra hne
    exact h ⟨t, ht, hzt, hne⟩
  have h1 := productUniqueContainment_of_centralProductCentralizer hz huniq h2
  let L := involutionPointHull z
  have hzL : z ∈ L := Subgroup.subset_closure (distinguished_mem_pointClass z)
  let zL : L := ⟨z, hzL⟩
  have hLH : ¬ L ≤ H := by
    intro hle
    apply hH
    refine eq_top_iff.mpr fun g _ => (conj_mem_iff huniq g).mp ?_
    exact hle (Subgroup.subset_closure (class_conj_mem (distinguished_mem_pointClass z) g))
  have hzL2 : orderOf zL = 2 := (Subgroup.orderOf_mk z hzL).trans hz
  have huniqL := unique_subgroupOf huniq L hzL
  have h2L := centralProduct_subgroupOf hz huniq h2 L hzL hLH
  have htL := class_mem_hull_class hz huniq h1 hH ht
  have hztL : Commute zL ⟨t, Subgroup.subset_closure ht⟩ := Subtype.ext hzt
  have hneL : (⟨t, Subgroup.subset_closure ht⟩ : L) ≠ zL := fun h => hne (congrArg Subtype.val h)
  have hO : CFSG.oddCore L ≤ H.subgroupOf L :=
    oddCore_le_of_commuting_class hzL2 huniqL h2L htL hztL hneL
  let q := QuotientGroup.mk' (CFSG.oddCore L)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = CFSG.oddCore L := QuotientGroup.ker_mk' _
  have hodd : Odd (Nat.card q.ker) := by
    rw [hker]
    exact CFSG.ComponentClassification.OddCore.odd_card L
  have hkerH : q.ker ≤ H.subgroupOf L := by
    rw [hker]
    exact hO
  have hHL : H.subgroupOf L ≠ ⊤ := by
    intro htop
    apply hLH
    intro y hy
    have hmem : (⟨y, hy⟩ : L) ∈ H.subgroupOf L := htop ▸ Subgroup.mem_top _
    exact hmem
  have hcard : Nat.card (L ⧸ CFSG.oddCore L) ≤ Nat.card G :=
    (Nat.card_le_card_of_surjective q hq).trans
      (Nat.card_le_card_of_injective L.subtype L.subtype_injective)
  have hN := hnorm (L ⧸ CFSG.oddCore L) hcard ((H.subgroupOf L).map q) (q zL)
    (orderOf_map_of_odd q hodd hzL2) (map_ne_top q hkerH hHL) (unique_map q hq hkerH huniqL)
    (centralProduct_map q hq hodd hzL2 h2L)
    (hull_map_eq_top q hq (hull_internal_eq_top hz huniq h1 hH))
    (CFSG.ComponentClassification.OddCore.quotient_corefree L)
  exact pointHullStrongSplit_of_normSplit hz huniq h1 hH hO hN

end CFSG.ComponentClassification.AschbacherStrongEmbedding
