module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneExceptionalKernel
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeFinal
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.SeitzReduction.OmegaPilot (NeighbourOvergroupOmega OmegaNeighbourAlternative
  OmegaCatalogueClausesAt)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

variable {K : Type} [Field K]

theorem neighbour_overgroup_E7_torus (hcat : OmegaCatalogueClausesAt 6) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {X : Subgroup G}
    (hX : (∃ A : Subgroup (adjointGroup .E7 K), A ≤ posJE7 K ∧ IsCyclic A ∧
        Nat.card A = Nat.card K + 1 ∧ X = (A.map e.symm.toMonoidHom).map L.subtype) ∨
      X = (((EPilot.highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K)).map
        e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        OmegaNeighbourAlternative
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc 6 f := by
  rcases hX with ⟨A, hAJ, hcyc, hA, hX⟩ | hX
  · exact neighbour_overgroup_E7_nonsplit hcat hset hf hK e ht hKt hAJ hA hcyc hX htX hDe
  · exact neighbour_overgroup_E7_split hcat hset hf hK e ht hKt hX htX hDe

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem lieModel_quotient_center_E7 (hZ : center L = ⊥) {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (e : L ≃* adjointGroup .E7 K) : LieModel (L ⧸ center L) .E7 0 2 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hKc
  exact Or.inr (Or.inl ⟨rfl, by decide,
    ⟨Nat.prime_two, F4Pilot.one_le_of_natCard_eq_two_pow hKc, rfl⟩, K, inferInstance,
      inferInstance, hKc, ⟨(quotientCenterMulEquiv hZ).trans (e.trans
        ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
          QuotientGroup.quotientBot).symm)⟩⟩)

theorem inf_centralizer_eq_zpowers_E7 (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
  inf_centralizer_eq_zpowers_of_exceptional exceptionalHypothesisOne hset.standardSetting
    hset.center_eq_bot (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (lieModel_quotient_center_E7 hset.center_eq_bot hKc e) htC ht

end CFSG.SeitzReduction.E7Pilot
