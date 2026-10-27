module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotHR8Final
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAutDSetting
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotHR8Instances

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem neighbour_overgroup_E8_torus_of_seitzSetting (hcat : E7CatalogueClauses)
    (hset : SeitzSetting G L) {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : L ≃* adjointGroup .E8 K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {X : Subgroup G}
    (hX : (∃ A : Subgroup (adjointGroup .E8 K), A ≤ posJE8 K ∧ IsCyclic A ∧
        Nat.card A = Nat.card K + 1 ∧ X = (A.map e.symm.toMonoidHom).map L.subtype) ∨
      X = (((EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K)).map
        e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupE7 (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) f :=
  neighbour_overgroup_E8_torus hcat hset.standardSetting hf hK e ht
    (inf_centralizer_eq_zpowers_E8 hset hK e htC ht) hX htX hDe

theorem neighbour_overgroup_E8_torus_of_seitzSetting_of_leafInputs
    (hGLS : GLS3OddLieAutComponentsInput) (hXodd : E7NotOddLieInput)
    (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput)
    (hset : SeitzSetting G L) {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : L ≃* adjointGroup .E8 K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {X : Subgroup G}
    (hX : (∃ A : Subgroup (adjointGroup .E8 K), A ≤ posJE8 K ∧ IsCyclic A ∧
        Nat.card A = Nat.card K + 1 ∧ X = (A.map e.symm.toMonoidHom).map L.subtype) ∨
      X = (((EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K)).map
        e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupE7 (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) f :=
  neighbour_overgroup_E8_torus_of_seitzSetting
    (e7CatalogueClauses_of_leafInputs hGLS hXodd hMinn hMcomp) hset hf hK e htC ht hX htX hDe

end CFSG.SeitzReduction.E8Pilot
