module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSimpleQuotient
public import CFSG.Open.GilmanSolomonDefs

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Subgroup CFSG.ComponentClassification.UnbalancedGS

theorem isQuasisimple_open_iff (X : Type*) [Group X] :
    CFSG.Open.IsQuasisimple X ↔ IsQuasisimple X :=
  (AssemblyBPredicates.isQuasisimple_iff_open X).symm.trans
    (AssemblyBPredicates.isQuasisimple_iff_native X)

theorem isSubnormal_open_iff {G : Type*} [Group G] {L K : Subgroup G} (hLK : L ≤ K) :
    CFSG.Open.IsSubnormal L K ↔ (L.subgroupOf K).IsSubnormal :=
  CFSG.Open.IsSubnormal.iff_subgroupOf hLK

theorem primeResidual_two_eq_top_of_perfect {X : Type*} [Group X] [Finite X]
    (hX : commutator X = ⊤) : CatalogueBPrimeJoin.primeResidual 2 X = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CatalogueBPrimeJoin.primeResidual 2 X).Characteristic :=
    CatalogueBPrimeJoin.primeResidual_characteristic 2 X
  have hodd : Odd (Nat.card (X ⧸ CatalogueBPrimeJoin.primeResidual 2 X)) :=
    Nat.coprime_two_left.mp (CatalogueBPrimeJoin.primeResidual_coprime_index 2 X)
  have hsolv : Group.IsSolvable (X ⧸ CatalogueBPrimeJoin.primeResidual 2 X) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsPerfect X := ⟨hX⟩
  have : Group.IsPerfect (X ⧸ CatalogueBPrimeJoin.primeResidual 2 X) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ CatalogueBPrimeJoin.primeResidual 2 X := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  have : Nontrivial (X ⧸ CatalogueBPrimeJoin.primeResidual 2 X) :=
    nontrivial_of_ne (x : X ⧸ CatalogueBPrimeJoin.primeResidual 2 X) 1
      (fun h => hx ((QuotientGroup.eq_one_iff x).mp h))
  exact Group.IsPerfect.not_isSolvable (X ⧸ CatalogueBPrimeJoin.primeResidual 2 X) hsolv

variable {G : Type*} [Group G]

theorem fusionIsTwoComponent_iff [Finite G] {L K : Subgroup G} :
    CFSG.Open.fusionIsTwoComponent L K ↔ L ≤ K ∧ IsPComponent 2 (L.subgroupOf K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.Open.IsQuasisimple (L ⧸ CFSG.Open.fusionOddCore L) ↔
      IsQuasisimple (L ⧸ pPrimeCore 2 L) :=
    (isQuasisimple_open_iff _).trans (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (QuotientGroup.quotientMulEquivOfEq (fusionOddCore_eq_pPrimeCore L)))
  constructor
  · rintro ⟨hLK, hsub, hperf, hquot⟩
    refine ⟨hLK, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L K hLK).2
      ⟨(isSubnormal_open_iff hLK).1 hsub, primeResidual_two_eq_top_of_perfect hperf,
        hq.1 hquot⟩⟩
  · rintro ⟨hLK, hL⟩
    obtain ⟨hsub, -, hquot⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L K hLK).1 hL
    have hperf := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hL
    have hperf' : Group.IsPerfect L :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLK).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hLK).surjective
    exact ⟨hLK, (isSubnormal_open_iff hLK).2 hsub, hperf'.commutator_eq_top, hq.2 hquot⟩

theorem fusionTwoLayer_eq_gsFixedLayer [Finite G] (N : Subgroup G) (t : G) :
    CFSG.Open.fusionTwoLayer (N ⊓ centralizer ({t} : Set G)) = gsFixedLayer N t := by
  set K := N ⊓ centralizer ({t} : Set G) with hK
  rw [gsFixedLayer, ← hK, pLayer, (gc_map_comap K.subtype).l_sSup, CFSG.Open.fusionTwoLayer]
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    obtain ⟨hLK, hcomp⟩ := fusionIsTwoComponent_iff.1 hL
    refine le_iSup₂_of_le (L.subgroupOf K) hcomp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hLK]
  · refine iSup₂_le fun M hM => ?_
    have hle : M.map K.subtype ≤ K := map_subtype_le M
    have hMM : (M.map K.subtype).subgroupOf K = M :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective M
    have hcomp : CFSG.Open.fusionIsTwoComponent (M.map K.subtype) K :=
      fusionIsTwoComponent_iff.2 ⟨hle, by rw [hMM]; exact hM⟩
    exact le_iSup₂_of_le (M.map K.subtype) hcomp le_rfl

theorem fusionTwoComponentCond_iff [Finite G] {L K : Subgroup G} (hLK : L ≤ K) :
    CFSG.Open.fusionTwoComponentCond L K ↔ IsPComponent 2 (L.subgroupOf K) :=
  ⟨fun h => (fusionIsTwoComponent_iff.1 ⟨hLK, h⟩).2,
    fun h => (fusionIsTwoComponent_iff.2 ⟨hLK, h⟩).2⟩

theorem fusionFixedLayer_eq_gsFixedLayer [Finite G] :
    (CFSG.Open.fusionFixedLayer : Subgroup G → G → Subgroup G) = gsFixedLayer :=
  funext₂ fusionTwoLayer_eq_gsFixedLayer

theorem fusionOddCoreOf_eq_map_pPrimeCore :
    (CFSG.Open.fusionOddCoreOf : Subgroup G → Subgroup G) =
      fun X => (pPrimeCore 2 X).map X.subtype :=
  funext fun X => by rw [CFSG.Open.fusionOddCoreOf, fusionOddCore_eq_pPrimeCore]

theorem fusionCorr_iff_gsCorr [Finite G] {a b : G} {J L : Subgroup G} :
    CFSG.Open.fusionCorr a J b L ↔ GSCorr a J b L :=
  CFSG.Open.fusionCorr_iff_grammar.trans <| (GSGrammar.corr_congr
    (fun _ _ => fusionTwoComponentCond_iff) fusionOddCoreOf_eq_map_pPrimeCore
    fusionFixedLayer_eq_gsFixedLayer).trans gsCorr_iff_grammar.symm

end CFSG.ComponentClassification.UnbalancingLocal
