module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2Position
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverFamilyMain
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2BLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.SeitzReduction.LinearPilot (CatSLmSporadicAt slmCatalogueClausesAt_six)
open CFSG.SeitzReduction.F4Pilot (F4Work HasBLift oddCoreLift)

section Position

theorem e6TwoPositionInput_holds : E6TwoPositionInput := by
  intro G _ _ L K _ _ _ e t hw A hAJ _ hA
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  exact not_normal_neighbour_E6_nonsplit_two hw.standard hK2 e hw.orderOf_eq hw.inf_eq hAJ hA rfl
    rfl

theorem inf_centralizer_le_nonsplit_E6 {G : Type} [Group G] {L : Subgroup G} {K : Type}
    [Field K] [Finite K] [CharP K 2] (e : L ≃* adjointGroup .E6 K)
    {A : Subgroup (adjointGroup .E6 K)} (hAJ : A ≤ posJ K) (hA : Nat.card A = Nat.card K + 1)
    (hcyc : IsCyclic A) :
    L ⊓ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) ⊓
        centralizer ((((a5Levi K).map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) ≤
      (A.map e.symm.toMonoidHom).map L.subtype := by
  obtain ⟨hcent, -, hAD⟩ := centralizer_nonsplit_E6 hAJ hA hcyc
  refine SeitzQ2.inf_centralizer_le_of_le_sup ?_ (F4Pilot.map_le_centralizer_map L.subtype
    (F4Pilot.map_le_centralizer_map e.symm.toMonoidHom hAD)) (center_map_a5Levi_eq_bot e)
  rw [F4Pilot.inf_centralizer_map_symm e A, hcent, Subgroup.map_sup, Subgroup.map_sup]

theorem hasBLift_nonsplit_E6_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup (adjointGroup .E6 K)} (hAJ : A ≤ posJ K) (hA : Nat.card A = 3)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : ⁅E, E⁆ = E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hEt : E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆) :
    HasBLift E := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := F4Pilot.charP_two_of_natCard_eq_two_pow (f := 1) (by rw [pow_one]; exact hK)
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht
  have hZL : center L = ⊥ := F4Pilot.center_eq_bot_congr e.symm center_adjointGroup_eq_bot
  have htL : t ∉ L := by
    intro htL
    have hZt : (⟨t, htL⟩ : L) ∈ center L :=
      mem_center_iff.2 fun l => Subtype.ext (mem_centralizer_iff.1 htC l l.2)
    rw [hZL, mem_bot] at hZt
    have ht1 : t = 1 := congrArg Subtype.val hZt
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by decide)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA
  have hA' : Nat.card A = Nat.card K + 1 := by rw [hA, hK]
  obtain ⟨hcent, -, hAD⟩ := centralizer_nonsplit_E6 hAJ hA' hcyc
  subst hX
  exact SeitzQ2.hasBLift_of_isPGroup_outer (SeitzQ2.isPGroup_outer_of_mulEquiv_E6_two hK e) htC ht
    htL hCN hKt htX (F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hcent hAD
      (F4Pilot.le_centralizer_self_of_isCyclic hcyc) isQuasisimple_a5Levi).symm
    (isQuasisimple_map_a5Levi e) (inf_centralizer_le_nonsplit_E6 e hAJ hA' hcyc) hE htE hEt

end Position

section Glue

theorem seitzExclusion_highE6_of_xchar_two (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor : CatSLmSporadicAt 6) (hSCT : E6SwapRowCTInput) (hSU : E6SwapRowUniqueInput)
    (h2r : E6TwoRowsInput) : SeitzExclusion (HighExceptional .E6) :=
  seitzExclusion_highE6_of_rowInputs'' hGLS (CrossChar.sLmNotOddLieInputAt (by decide)) hSpor hSCT
    hSU e6TwoPositionInput_holds h2r

end Glue

end CFSG.SeitzReduction.E6Pilot
