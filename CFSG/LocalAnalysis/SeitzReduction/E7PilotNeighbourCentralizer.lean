module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviDescent
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplitLayer

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.EPilot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem baseChangeGL_mem_highRootSL2_E7 {M : Type} [Field M] (ι : K →+* M) {j : ModGL .E7 K}
    (hj : j ∈ highRootSL2 .E7 K) : baseChangeGL ι j ∈ highRootSL2 .E7 M := by
  have : CharP M 2 := charP_of_injective_ringHom ι.injective 2
  rw [← E6Pilot.range_rootSL2_highRoot] at hj
  obtain ⟨A, rfl⟩ := hj
  rw [E6Pilot.baseChangeGL_rootSL2_highRoot]
  exact E6Pilot.rootSL2_highRoot_mem_highRootSL2 _

theorem perpLeviFrobDescent_E7 (hq : 4 ≤ Nat.card K) : E6Pilot.PerpLeviFrobDescent .E7 K := by
  intro d hd hσd
  set ι := algebraMap K (FiniteField.Extension K 2 2) with hι
  obtain ⟨g₀, hg₀, hg₀d⟩ :=
    E8Pilot.exists_baseChangeGL_eq_of_frob_fixed_E7 (rootSpan_le_adjointGroup' _ hd) hσd
  refine ⟨g₀, ?_, hg₀d⟩
  rw [← centralizer_highRootSL2_eq (Or.inr (Or.inl rfl)) hq]
  refine Subgroup.mem_inf.2 ⟨hg₀, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩
  have hjJ := baseChangeGL_mem_highRootSL2_E7 ι hj
  have hdJ := Subgroup.mem_centralizer_iff.1
    (rootSpan_perpRoots_le_centralizer_highRootSL2 (K := FiniteField.Extension K 2 2)
      (Or.inr (Or.inl rfl)) hd) _ hjJ
  apply baseChangeGL_injective ι
  rw [map_mul, map_mul, hg₀d]
  exact hdJ

theorem adjointGroup_inf_centralizer_nonsplit_E7 (hq : 4 ≤ Nat.card K)
    {X : Subgroup (ModGL .E7 K)} (hXJ : X ≤ highRootSL2 .E7 K)
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    adjointGroup .E7 K ⊓ centralizer (X : Set (ModGL .E7 K)) =
        X ⊔ rootSpan .E7 K (perpRoots .E7) ∧
      Disjoint X (rootSpan .E7 K (perpRoots .E7)) ∧
      X ≤ centralizer (rootSpan .E7 K (perpRoots .E7) : Set (ModGL .E7 K)) :=
  E6Pilot.adjointGroup_inf_centralizer_nonsplit_of_descent (Or.inr (Or.inl rfl))
    (perpLeviFrobDescent_E7 hq) hXJ hcyc hX

theorem exists_mul_of_mem_centralizer_nonsplit_E7 (hq : 4 ≤ Nat.card K)
    {X : Subgroup (adjointGroup .E7 K)}
    (hXJ : X ≤ (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) {c : adjointGroup .E7 K}
    (hc : c ∈ centralizer (X : Set (adjointGroup .E7 K))) :
    ∃ y ∈ X, ∃ d ∈ perpLevi .E7 K, c = y * d :=
  E6Pilot.exists_mul_of_mem_centralizer_nonsplit_of_descent (Or.inr (Or.inl rfl))
    (perpLeviFrobDescent_E7 hq) hXJ hcyc hX hc

theorem centralizer_nonsplit_E7 (hq : 4 ≤ Nat.card K) {X : Subgroup (adjointGroup .E7 K)}
    (hXJ : X ≤ (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    centralizer (X : Set (adjointGroup .E7 K)) = X ⊔ perpLevi .E7 K ∧
      Disjoint X (perpLevi .E7 K) ∧
      X ≤ centralizer (perpLevi .E7 K : Set (adjointGroup .E7 K)) :=
  E6Pilot.centralizer_nonsplit_of_descent (Or.inr (Or.inl rfl)) (perpLeviFrobDescent_E7 hq) hXJ
    hcyc hX

theorem centralizer_split_E7 {c : Kˣ} (hc : 3 ≤ orderOf c) {A : Subgroup (adjointGroup .E7 K)}
    (hAT : A ≤ (highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K))
    (hcA : (⟨rootDiagUnit .E7 (highDiag .E7 c),
      E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup (Or.inr (Or.inl rfl)) c⟩ :
        adjointGroup .E7 K) ∈ A) :
    centralizer (A : Set (adjointGroup .E7 K)) =
      (highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K) ⊔ perpLevi .E7 K :=
  E6Pilot.centralizer_eq_highTorusLine_sup_of_le (Or.inr (Or.inl rfl)) hc hAT hcA

theorem centralizer_highTorusLine_E7 (hq : 4 ≤ Nat.card K) :
    centralizer ((highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K) :
        Set (adjointGroup .E7 K)) =
      (highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K) ⊔ perpLevi .E7 K :=
  E6Pilot.centralizer_highTorusLine_eq (Or.inr (Or.inl rfl)) hq

theorem highTorusLine_le_centralizer_perpLevi_E7 :
    (highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K) ≤
      centralizer (perpLevi .E7 K : Set (adjointGroup .E7 K)) :=
  E6Pilot.highTorusLine_subgroupOf_le_centralizer_perpLevi

theorem odd_card_highTorusLine_E7 {f : ℕ} (hKc : Nat.card K = 2 ^ f) :
    Odd (Nat.card ((highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K))) := by
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (E6Pilot.highTorusLine_le_adjointGroup (Or.inr (Or.inl rfl)))).toEquiv]
  exact E6Pilot.odd_card_highTorusLine (F4Pilot.one_le_of_natCard_eq_two_pow hKc) hKc

theorem inSubgroup_layer_inf_centralizer_nonsplit_E7 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E7 K) (hq : 4 ≤ Nat.card K) {X : Subgroup (adjointGroup .E7 K)}
    (hXJ : X ≤ (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    inSubgroup layer
        (L ⊓ centralizer (((X.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) =
      ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype := by
  obtain ⟨hcen, -, hXD⟩ := centralizer_nonsplit_E7 hq hXJ hX hcyc
  exact F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hcen hXD
    (F4Pilot.le_centralizer_self_of_isCyclic hcyc) isQuasisimple_perpLevi_E7

theorem inf_centralizer_nonsplit_E7 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E7 K) (hq : 4 ≤ Nat.card K) {X : Subgroup (adjointGroup .E7 K)}
    (hXJ : X ≤ (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    L ⊓ centralizer (((X.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) =
      (X.map e.symm.toMonoidHom).map L.subtype ⊔
        ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype := by
  rw [F4Pilot.inf_centralizer_map_symm, (centralizer_nonsplit_E7 hq hXJ hX hcyc).1,
    Subgroup.map_sup, Subgroup.map_sup]

theorem inSubgroup_layer_inf_centralizer_split_E7 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E7 K) {c : Kˣ} (hc : 3 ≤ orderOf c)
    {A : Subgroup (adjointGroup .E7 K)}
    (hAT : A ≤ (highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K))
    (hcA : (⟨rootDiagUnit .E7 (highDiag .E7 c),
      E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup (Or.inr (Or.inl rfl)) c⟩ :
        adjointGroup .E7 K) ∈ A) :
    inSubgroup layer
        (L ⊓ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) =
      ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype :=
  F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e (centralizer_split_E7 hc hAT hcA)
    highTorusLine_le_centralizer_perpLevi_E7
    E6Pilot.highTorusLine_subgroupOf_le_centralizer_self isQuasisimple_perpLevi_E7

theorem inSubgroup_layer_inf_centralizer_highTorusLine_E7 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E7 K) (hq : 4 ≤ Nat.card K) :
    inSubgroup layer (L ⊓ centralizer
        ((((highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K)).map
          e.symm.toMonoidHom).map L.subtype : Set G)) =
      ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype := by
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  exact inSubgroup_layer_inf_centralizer_split_E7 e hc le_rfl
    (Subgroup.mem_subgroupOf.2 (rootDiagUnit_highDiag_mem_highTorusLine c))

theorem inSubgroup_layer_inf_centralizer_highRootSL2_E7 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E7 K) (hq : 4 ≤ Nat.card K) :
    inSubgroup layer (L ⊓ centralizer
        ((((highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)).map
          e.symm.toMonoidHom).map L.subtype : Set G)) =
      ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype := by
  have hcen : centralizer (((highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) :
      Subgroup (adjointGroup .E7 K)) : Set (adjointGroup .E7 K)) = ⊥ ⊔ perpLevi .E7 K := by
    rw [bot_sup_eq]
    exact centralizer_highRootSL2_subgroupOf (Or.inr (Or.inl rfl)) hq
  exact F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hcen bot_le bot_le
    isQuasisimple_perpLevi_E7

end CFSG.SeitzReduction.E7Pilot
