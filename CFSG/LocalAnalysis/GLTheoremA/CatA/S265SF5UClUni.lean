module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedUnitary
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UClUniB
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Uni
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr
  exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormP primeFormConjHom)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram isPrimeFormGram_idGram)

theorem false_of_classicalModel_psu {G : Type} [Group G] [Finite G] {n f : ℕ}
    (hG : StatedClassicalModel G .PSU n 2 f) {β : MulAut G} (hβ : β ∈ innAutDerived G)
    (hβ5 : β ^ 5 = 1) (hβ1 : β ≠ 1) {J : Subgroup G} (hJ : IsComponentOf J (fixSubgroup β))
    (hZ : Subgroup.center ↥J = ⊥) {e : ℕ} (h5 : 5 ∣ 2 ^ e + 1) (h25 : ¬ 25 ∣ 2 ^ e + 1)
    (hJc : Nat.card J = ordTwistedA 4 (2 ^ e)) : False := by
  have hadm := hG.1
  obtain ⟨-, -, hn3, hne⟩ := hadm
  obtain ⟨K, _, hU, -, ⟨θ⟩⟩ := CanonU3.exists_primeFormP_mulEquiv_of_statedModel_uni hG
  obtain ⟨A, c, -, hA, hβeq⟩ := exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived hU
    (isPrimeFormGram_idGram (n := n)) hn3 (fun h => hne (by rw [h.1, h.2])) (p := 5)
    ((mem_innAutDerived_congr θ).2 hβ) (by rw [← map_pow, hβ5, map_one])
  have hβA : primeFormConjHom hU (idGram K n) A ≠ 1 := by
    rw [← hβeq]
    exact fun h1 => hβ1 ((MulEquiv.map_eq_one_iff (MulAut.congr θ)).1 h1)
  let eJ := J.equivMapOfInjective (θ : G →* primeFormP hU (idGram K n)) θ.injective
  refine false_of_component_primeForm_five hU A hA hβA
    (T := J.map (θ : G →* primeFormP hU (idGram K n))) ?_ ?_ h5 h25 ?_
  · rw [← hβeq, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr θ β]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map θ hJ
  · rw [← Subgroup.map_center_eq eJ, hZ, Subgroup.map_bot]
  · rw [← hJc]
    exact Nat.card_congr eJ.toEquiv.symm

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
