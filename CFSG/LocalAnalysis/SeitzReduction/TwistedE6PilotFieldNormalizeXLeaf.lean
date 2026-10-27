module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalizeSeitz
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalizeXModel
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR8Exact
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotXiFusion

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.UnitaryPilot (SUmNotOddLieInputAt)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem nonempty_fieldCoverParamX_2E6_of_leafInputs (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : SUmNotOddLieInputAt 6) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDKc : ⁅(D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Kc⁆ ≠ ⊥)
    (hKt : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc) :
    Nonempty (FieldCoverParamX σ (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) e t X) := by
  have hf : 1 ≤ f := by omega
  have := charP_two_of_card hf hK
  have hξ := twistedFusionIn_xiAut hf2 hk hK σ hσ
  obtain ⟨-, hall⟩ := neighbour_overgroup_2E6_X hGLS hXodd hMinn hMcomp hset hf2 hk hK hσ e htC
    ht hξ hX htX hDe
  obtain ⟨-, ⟨-, hDK, -, hsN, hov⟩ | ⟨hne, -⟩⟩ := hall Kc hKc hDKc
  ·
    obtain ⟨-, F, _, _, hF, eK, -, -, -⟩ := graphField_neighbour_2E6_X_of_clauses
      (sumCatalogueClausesAtF_six_of_leafInputs hGLS hXodd hMinn hMcomp hf2) hset hf2 hk hK hσ e
      htC ht hξ hX htX hDe Kc hKc hDKc hKt
    exact nonempty_fieldCoverParamX_2E6 hset hf2 hk hK hσ e htC ht hX htX hDe hKc hDK.le hsN hov
      (nonempty_a5Levi_mulEquiv_of_projectiveSL hf hk hK hσ hF eK)
      (involutionDescentComp_a5Levi hf hk hK hσ) (autExtensionComm_a5Levi hf hk hK hσ)
  · exact absurd hKt hne

end CFSG.SeitzReduction.TwistedE6Pilot
