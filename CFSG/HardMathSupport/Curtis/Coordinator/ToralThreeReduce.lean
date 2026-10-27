module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.Open.StatedDefs
public import Certificates.Certificate43
import CFSG.HardMathSupport.Curtis.Coordinator.BlockGlue
import CFSG.HardMathSupport.Curtis.Coordinator.AutBounds
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVTypes
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVMain
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIASix
import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIICenter
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVOut
import CFSG.RankThree.SubgroupLists2.OmegaThree
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.Fischer.Uniq.CompTau
import CFSG.GH74.Generic.Certificates
import CFSG.GH74.Statements
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocks
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
import CFSG.LocalAnalysis.AGLEmbedding.ReeData
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBarM
import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.StronglyEmbedded.ParityCriterion
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding CFSG.Open CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

theorem isPGroup_of_isElemAbelian {X : Type*} [Group X] {p : ℕ} {E : Subgroup X}
    (hE : IsElemAbelian p E) : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

omit [Finite G] in
theorem le_blockPL_of_fix {u : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hfix : ∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L)
    {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hEL : E ≤ barM M L)
    (hEC : E ≤ Subgroup.centralizer ({u} : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    E ≤ blockPL M S L := fun e he => hfix e (hEL he) (by
  rw [← Subgroup.mem_centralizer_singleton_iff.mp (hEC he), mul_inv_cancel_right])

theorem not_three_dvd_card_outer_of_center_alt {X : Type*} [Group X] [Group.IsPerfect X]
    [Nontrivial (X ⧸ Subgroup.center X)] {n : ℕ}
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n)) : ¬ 3 ∣ Nat.card (Outer X) := by
  intro h3
  have hn := five_le_of_isPerfect_mulEquiv_alternatingGroup e
  apply not_dvd_card_outer_alternatingGroup n hn 3 Nat.prime_three (by norm_num)
  rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact h3.trans (card_outer_dvd_card_outer_centerQuotient X)

theorem not_three_dvd_card_outer_of_alt {X : Type*} [Group X] [Group.IsPerfect X] [Nontrivial X]
    {n : ℕ} (e : X ≃* alternatingGroup (Fin n)) : ¬ 3 ∣ Nat.card (Outer X) := by
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact not_dvd_card_outer_alternatingGroup n (five_le_of_isPerfect_mulEquiv_alternatingGroup e)
    3 Nat.prime_three (by norm_num)

section Block

variable (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
  (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)

omit [Finite G] in
include hL in
theorem barM_isPerfect : Group.IsPerfect ↥(barM M L) :=
  Group.isPerfect_def.mpr hL.component.2.2.1

omit [Finite G] in
include hL in
theorem barM_nontrivial_center_quotient :
    Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
  hL.component.2.2.2.toNontrivial

omit [Finite G] in
include hL in
theorem barM_nontrivial : Nontrivial ↥(barM M L) :=
  have := barM_nontrivial_center_quotient hL
  (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L))).nontrivial

include hK hA hL hX hS in
theorem mem_sup_centralizer_of_rest (hT : CitedBlockTransvectionPLType)
    (h : NineThreeThree M S L ∨ NineThreeFour M S L ∨ NineThreeFive M L ∨ NineThreeSix M S L ∨
      NineThreeSeven M S L ∨ NineThreeEight M S L)
    (hperf : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockPL M S L → ⁅W, W⁆ = W →
      Nat.Coprime 3 (Nat.card W))
    {u : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hu : u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (hu3 : u ^ 3 = 1) :
    u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have := barM_isPerfect hL
  have := barM_nontrivial_center_quotient hL
  have := barM_nontrivial hL
  have hu3' : u ^ 3 ^ 1 = 1 := by rw [pow_one]; exact hu3
  rcases h with h3 | h4 | ⟨-, ⟨e⟩, -⟩ | ⟨-, n, ⟨e⟩, -⟩ | ⟨-, n, ⟨e⟩, -⟩ |
      ⟨-, N, r, ⟨m, hm⟩, hr, h0, h2, h4, -, φ, -⟩
  · obtain ⟨hOrth, hU4, -, -, hA8⟩ := hT G M S L hK hA hL hX hS h3
    rcases h3.2.1 with ⟨d, ⟨m, q, hq, hdm⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · rcases hdm with hd | hd | ⟨rfl, hd⟩
      · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨e'⟩⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
        have hm4 : 4 ≤ m := by
          have h := d.2
          rw [hd] at h
          exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
            ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
        exact (false_of_quotient_sp_of_three (k := m - 1) (by omega) ⟨q', hq', hd'⟩ hperf e').elim
      · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨e'⟩⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
        have hm4 : 4 ≤ m := by
          have h := d.2
          rw [hd] at h
          exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
            ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
        exact (false_of_quotient_sp_of_three (k := m - 1) (by omega) ⟨q', hq', hd'⟩ hperf e').elim
      · obtain ⟨e6⟩ := hU4 d ⟨q, hq, hd⟩ ⟨e⟩
        exact (false_of_surjective_perm_of_three (n := 6) (by norm_num) hperf e6.toMonoidHom
          e6.surjective).elim
    · rcases hn with rfl | rfl | rfl
      · exact mem_sup_centralizer_of_not_dvd_card_outer Nat.prime_three
          (not_three_dvd_card_outer_of_alt e) hu hu3'
      · exact mem_sup_centralizer_of_not_dvd_card_outer Nat.prime_three
          (not_three_dvd_card_outer_of_alt e) hu hu3'
      · obtain ⟨e6⟩ := hA8 ⟨e⟩
        exact (false_of_surjective_perm_of_three (n := 6) (by norm_num) hperf e6.toMonoidHom
          e6.surjective).elim
  · obtain ⟨-, hZ, he, -⟩ := h4
    exact (kFactBlockThreeASix_holds G M L hL.toIsTwoPrimeComponent hZ he).1 u hu ⟨1, hu3'⟩
  · exact mem_sup_centralizer_of_not_dvd_card_outer Nat.prime_three
      (not_three_dvd_card_outer_of_alt e) hu hu3'
  · exact mem_sup_centralizer_of_not_dvd_card_outer Nat.prime_three
      (not_three_dvd_card_outer_of_center_alt e) hu hu3'
  · exact mem_sup_centralizer_of_not_dvd_card_outer Nat.prime_three
      (not_three_dvd_card_outer_of_alt e) hu hu3'
  · exfalso
    refine false_of_surjective_perm_of_three (n := N - 2 * r) (by omega) hperf
      ((MonoidHom.snd _ _).comp (φ.toMonoidHom.comp (QuotientGroup.mk' _))) ?_
    exact Prod.snd_surjective.comp (φ.surjective.comp (QuotientGroup.mk'_surjective _))

end Block

theorem statedClassicalModel_psl_two_seven {X : Type} [Group X] {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q)
    (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) : StatedClassicalModel X .PSL 2 7 1 := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨q, hq7, hdq⟩ := hd
  simp only at hdq
  subst hdq
  obtain ⟨hp, hf⟩ : q.p = 7 ∧ q.exponent = 1 := by
    rw [TauCeti.PrimePower.card_def] at hq7
    exact (Nat.Prime.pow_eq_iff (by norm_num)).1 hq7
  have hc := statedClassicalModel_of_typeA hv e
  rw [hp, hf] at hc
  exact hc

theorem card_eq_of_psl_two_seven {X : Type} [Group X] (h : StatedClassicalModel X .PSL 2 7 1) :
    Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven h

theorem card_ne_of_perfThreeSurvivor (hZ : OddCenterRest) (hL : IsWeakSBlock M S L)
    (hsurv : IsPerfThreeSurvivor (barM M L)) {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hEL : E ≤ barM M L) (hEel : IsElemAbelian 3 E) : Nat.card E ≠ 3 ^ 3 := by
  intro hEc
  have hodd := odd_card_center_barM_of_isWeakSBlock hL
  have hdvdL : 3 ^ 3 ∣ Nat.card (barM M L) := hEc ▸ Subgroup.card_dvd_of_le hEL
  have hcardL := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(barM M L))
  rcases hsurv with ⟨d, ⟨q, hq7, hdq⟩, ⟨e⟩⟩ | ⟨hZ3, ⟨e⟩⟩ | he
  ·
    have h168 : Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) = 168 :=
      card_eq_of_psl_two_seven (statedClassicalModel_psl_two_seven ⟨q, hq7, hdq⟩ e)
    have hS : IsSmallTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
      Or.inr ⟨d, Or.inl ⟨q, hq7, hdq⟩, ⟨e⟩⟩
    rcases hZ _ (barM M L) hL.component hodd (Or.inr (Or.inr (Or.inr (Or.inr hS)))) with
      h1 | ⟨-, ⟨e6⟩⟩
    · rw [hcardL, h168, h1] at hdvdL
      norm_num at hdvdL
    · have h360 := Nat.card_congr e6.toEquiv
      rw [h168, nat_card_alternatingGroup, Nat.card_fin] at h360
      norm_num [Nat.factorial] at h360
  ·
    have hab := (kFactBlockThreeASix_holds G M L hL.toIsTwoPrimeComponent hZ3 ⟨e⟩).2.2 E hEL
      (isPGroup_of_isElemAbelian hEel)
    have := hab.2 hEel.1
    rw [hEc] at this
    norm_num at this
  ·
    obtain ⟨e⟩ := he
    have h20160 : Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) = 20160 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    have hS : IsSmallTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
      Or.inl ⟨8, Or.inr (Or.inr rfl), ⟨e⟩⟩
    rcases hZ _ (barM M L) hL.component hodd (Or.inr (Or.inr (Or.inr (Or.inr hS)))) with
      h1 | ⟨-, ⟨e6⟩⟩
    · rw [hcardL, h20160, h1] at hdvdL
      norm_num at hdvdL
    · have h360 := Nat.card_congr e6.toEquiv
      rw [h20160, nat_card_alternatingGroup, Nat.card_fin] at h360
      norm_num [Nat.factorial] at h360

theorem citedBlockToralThree_of_census
    (hC : KFactFixCensusPerfThree) (hT : CitedBlockTransvectionPLType) (hZ : OddCenterRest) :
    CitedBlockToralThree := by
  intro G _ _ M S L hK hA hL h93 hX hS hperf u hu hu3 huC hfix
  have hperfPL : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockPL M S L → ⁅W, W⁆ = W →
      Nat.Coprime 3 (Nat.card W) := fun W hW hWW =>
    coprime_card_blockPL_of_perfect hL hperf W hW hWW
  rcases h93 with h1 | h2 | hrest
  · exact absurd h1 hX
  · obtain ⟨hinner, hsurv⟩ := hC _ (barM M L) (blockPL M S L) u
      (fixPerfThreeHyp_of_nineThreeTwo hA hL hS h2 hperf hu hu3 huC hfix)
    exact ⟨hinner, fun E hEL _ hEel => card_ne_of_perfThreeSurvivor hZ hL hsurv hEL hEel⟩
  · refine ⟨mem_sup_centralizer_of_rest hK hA hL hX hS hT hrest hperfPL hu hu3, ?_⟩
    intro E hEL hEC hEel hEc
    have h9 := card_le_nine_of_blockPL_rest (citedBlockTransvectionPL_of_type hT)
      citedBlockAltSevenPL_holds hK hA hL hX hS hrest hperfPL (le_blockPL_of_fix hfix hEL hEC)
      (isPGroup_of_isElemAbelian hEel)
    rw [hEc] at h9
    norm_num at h9

end CFSG.HardMathSupport.Curtis.Coordinator
