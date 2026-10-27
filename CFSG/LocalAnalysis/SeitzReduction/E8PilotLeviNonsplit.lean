module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviDescent
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplitLayer

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.EPilot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_mem_zpowers_mul_of_commute_nonsplit_E8 {x : ModGL .E8 K}
    (hxJ : x ∈ highRootSL2 .E8 K) (hx : orderOf x = Nat.card K + 1) {g : ModGL .E8 K}
    (hg : g ∈ adjointGroup .E8 K) (hgx : g * x = x * g) :
    ∃ y ∈ Subgroup.zpowers x, ∃ d ∈ rootSpan .E8 K (perpRoots .E8), g = y * d :=
  E6Pilot.exists_mem_zpowers_mul_of_commute_nonsplit_of_descent (Or.inr (Or.inr rfl))
    perpLeviFrobDescent_E8 hxJ hx hg hgx

theorem adjointGroup_inf_centralizer_nonsplit_E8 {X : Subgroup (ModGL .E8 K)}
    (hXJ : X ≤ highRootSL2 .E8 K) (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    adjointGroup .E8 K ⊓ centralizer (X : Set (ModGL .E8 K)) =
        X ⊔ rootSpan .E8 K (perpRoots .E8) ∧
      Disjoint X (rootSpan .E8 K (perpRoots .E8)) ∧
      X ≤ centralizer (rootSpan .E8 K (perpRoots .E8) : Set (ModGL .E8 K)) :=
  E6Pilot.adjointGroup_inf_centralizer_nonsplit_of_descent (Or.inr (Or.inr rfl))
    perpLeviFrobDescent_E8 hXJ hcyc hX

theorem exists_mul_of_mem_centralizer_nonsplit_E8 {X : Subgroup (adjointGroup .E8 K)}
    (hXJ : X ≤ (highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) {c : adjointGroup .E8 K}
    (hc : c ∈ centralizer (X : Set (adjointGroup .E8 K))) :
    ∃ y ∈ X, ∃ d ∈ e7Levi K, c = y * d :=
  E6Pilot.exists_mul_of_mem_centralizer_nonsplit_of_descent (Or.inr (Or.inr rfl))
    perpLeviFrobDescent_E8 hXJ hcyc hX hc

theorem centralizer_nonsplit_E8 {X : Subgroup (adjointGroup .E8 K)}
    (hXJ : X ≤ (highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    centralizer (X : Set (adjointGroup .E8 K)) = X ⊔ e7Levi K ∧ Disjoint X (e7Levi K) ∧
      X ≤ centralizer (e7Levi K : Set (adjointGroup .E8 K)) :=
  E6Pilot.centralizer_nonsplit_of_descent (Or.inr (Or.inr rfl)) perpLeviFrobDescent_E8 hXJ hcyc hX

theorem inSubgroup_layer_inf_centralizer_nonsplit_E8 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E8 K) {X : Subgroup (adjointGroup .E8 K)}
    (hXJ : X ≤ (highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    inSubgroup layer
        (L ⊓ centralizer (((X.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) =
      ((e7Levi K).map e.symm.toMonoidHom).map L.subtype := by
  obtain ⟨hcen, -, hXD⟩ := centralizer_nonsplit_E8 hXJ hX hcyc
  exact F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hcen hXD
    (F4Pilot.le_centralizer_self_of_isCyclic hcyc) isQuasisimple_e7Levi

theorem inf_centralizer_nonsplit_E8 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E8 K) {X : Subgroup (adjointGroup .E8 K)}
    (hXJ : X ≤ (highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    L ⊓ centralizer (((X.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) =
      (X.map e.symm.toMonoidHom).map L.subtype ⊔
        ((e7Levi K).map e.symm.toMonoidHom).map L.subtype := by
  rw [F4Pilot.inf_centralizer_map_symm, (centralizer_nonsplit_E8 hXJ hX hcyc).1, Subgroup.map_sup,
    Subgroup.map_sup]

theorem inSubgroup_layer_inf_centralizer_split_E8 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E8 K) {c : Kˣ} (hc : 3 ≤ orderOf c)
    {A : Subgroup (adjointGroup .E8 K)}
    (hAT : A ≤ (highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K))
    (hcA : (⟨rootDiagUnit .E8 (highDiag .E8 c),
      E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup (Or.inr (Or.inr rfl)) c⟩ :
        adjointGroup .E8 K) ∈ A) :
    inSubgroup layer
        (L ⊓ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) =
      ((e7Levi K).map e.symm.toMonoidHom).map L.subtype :=
  F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e
    (E6Pilot.centralizer_eq_highTorusLine_sup_of_le (Or.inr (Or.inr rfl)) hc hAT hcA)
    E6Pilot.highTorusLine_subgroupOf_le_centralizer_perpLevi
    E6Pilot.highTorusLine_subgroupOf_le_centralizer_self isQuasisimple_e7Levi

theorem inSubgroup_layer_inf_centralizer_highTorusLine_E8 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E8 K) (hq : 4 ≤ Nat.card K) :
    inSubgroup layer (L ⊓ centralizer
        ((((highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K)).map
          e.symm.toMonoidHom).map L.subtype : Set G)) =
      ((e7Levi K).map e.symm.toMonoidHom).map L.subtype := by
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  exact inSubgroup_layer_inf_centralizer_split_E8 e hc le_rfl
    (Subgroup.mem_subgroupOf.2 (rootDiagUnit_highDiag_mem_highTorusLine c))

theorem inSubgroup_layer_inf_centralizer_highRootSL2_E8 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E8 K) (hq : 4 ≤ Nat.card K) :
    inSubgroup layer (L ⊓ centralizer
        ((((highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K)).map
          e.symm.toMonoidHom).map L.subtype : Set G)) =
      ((e7Levi K).map e.symm.toMonoidHom).map L.subtype := by
  have hcen : centralizer (((highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K) :
      Subgroup (adjointGroup .E8 K)) : Set (adjointGroup .E8 K)) = ⊥ ⊔ e7Levi K := by
    rw [bot_sup_eq]
    exact centralizer_highRootSL2_subgroupOf (Or.inr (Or.inr rfl)) hq
  exact F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hcen bot_le bot_le
    isQuasisimple_e7Levi

end CFSG.SeitzReduction.E8Pilot
