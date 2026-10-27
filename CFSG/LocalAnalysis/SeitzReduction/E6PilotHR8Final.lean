module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR8Field
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.SeitzReduction.LinearPilot (SLmCatalogueClausesAt SLmNotOddLieInputAt CatSLmSporadicAt
  slmCatalogueClausesAt_six)

section FieldClauses

variable {K : Type} [Field K]

theorem neighbour_overgroup_E6_torus_field_of_four_le (hcat : SLmCatalogueClausesAt 6)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ}
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {X : Subgroup G}
    (hX : (∃ A : Subgroup (adjointGroup .E6 K), A ≤ posJ K ∧ IsCyclic A ∧
        Nat.card A = Nat.card K + 1 ∧ X = (A.map e.symm.toMonoidHom).map L.subtype) ∨
      X = (((EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K)).map
        e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSLField (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact neighbour_overgroup_E6_torus_field hcat hset hf hK e ht hKt (factF5E6_of_four_le hq) hX
    htX hDe

end FieldClauses

section Inputs

variable {K : Type} [Field K]

theorem neighbour_overgroup_E6_torus_field_of_four_le_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput) (hXodd : SLmNotOddLieInputAt 6)
    (hSpor : CatSLmSporadicAt 6) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {X : Subgroup G}
    (hX : (∃ A : Subgroup (adjointGroup .E6 K), A ≤ posJ K ∧ IsCyclic A ∧
        Nat.card A = Nat.card K + 1 ∧ X = (A.map e.symm.toMonoidHom).map L.subtype) ∨
      X = (((EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K)).map
        e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSLField (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f :=
  neighbour_overgroup_E6_torus_field_of_four_le (slmCatalogueClausesAt_six hGLS hXodd hSpor) hset
    hf hK e ht hKt hX htX hDe

end Inputs

end CFSG.SeitzReduction.E6Pilot
