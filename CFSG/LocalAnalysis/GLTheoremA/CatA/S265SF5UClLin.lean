module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedLinear
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxLinear
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.Distinct
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
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem false_of_classicalModel_psl {G : Type} [Group G] [Finite G] {n f : ℕ}
    (hG : StatedClassicalModel G .PSL n 2 f) {β : MulAut G} (hβ : β ∈ innAutDerived G)
    (hβ5 : β ^ 5 = 1) {J : Subgroup G} (hJ : IsComponentOf J (fixSubgroup β))
    (hZ : Subgroup.center ↥J = ⊥) {e : ℕ} (he : 1 ≤ e)
    (hJc : Nat.card J = ordTwistedA 4 (2 ^ e)) : False := by
  obtain ⟨⟨-, hf, hn, -, -⟩, k, _, _, hk, ⟨eG⟩⟩ := hG
  let ψ : G ≃* projectiveSL n k := eG.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n k).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k))
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1
    (CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived_projectiveSL_le_linearAutGroup
      hn ((CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr ψ).2 hβ))
  have hA5 : conjAut n k (A ^ 5) = 1 := by
    rw [map_pow, hA, ← map_pow, hβ5, map_one]
  obtain ⟨c, hc⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_eq_scalar_of_conjAut_eq_one hn hA5
  haveI : Fintype k := Fintype.ofFinite k
  haveI : CharP k 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have h5k : ((5 : ℕ) : k) ≠ 0 := fun h0 =>
    absurd ((CharP.cast_eq_zero_iff k 2 5).1 h0) (by norm_num)
  have hJ' : IsComponentOf (J.map (ψ : G →* projectiveSL n k)) (fixSubgroup (conjAut n k A)) := by
    rw [hA, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr ψ β]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map ψ hJ
  let eJ := J.equivMapOfInjective (ψ : G →* projectiveSL n k) ψ.injective
  have hZJ : Subgroup.center ↥(J.map (ψ : G →* projectiveSL n k)) = ⊥ := by
    rw [← Subgroup.map_center_eq eJ, hZ, Subgroup.map_bot]
  obtain ⟨E, _, _, m, j, hm, hj, -, hcardE, hbig, g, hg, hker⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_component_type_card h5k hc _ hJ'
  have hker' : g.ker = Subgroup.center _ := le_antisymm hker fun z hz => by
    have hgz : g z ∈ Subgroup.center ↥(J.map (ψ : G →* projectiveSL n k)) :=
      Subgroup.mem_center_iff.2 fun y => by
        obtain ⟨w, rfl⟩ := hg y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
    rw [hZJ, Subgroup.mem_bot] at hgz
    exact MonoidHom.mem_ker.2 hgz
  have hEc : Nat.card E = 2 ^ (f * j) := by rw [hcardE, hk, ← pow_mul]
  have hfj : 1 ≤ f * j := Nat.mul_le_mul hf hj
  have h4 : m = 2 → 4 ≤ 2 ^ (f * j) := fun h2 => by
    rw [← hEc]
    exact hbig h2
  have hmod : StatedClassicalModel ↥(J.map (ψ : G →* projectiveSL n k)) .PSL m 2 (f * j) :=
    ⟨⟨Nat.prime_two, hfj, hm, fun h => by
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      have := h4 h1
      omega, fun h => by
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      have := h4 h1
      omega⟩, E, inferInstance, inferInstance, hEc,
      ⟨(QuotientGroup.quotientKerEquivOfSurjective g hg).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker').trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E))⟩⟩
  refine CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (n := m - 1) (u := 4) (by omega) hfj
    (by norm_num) he ?_
  rw [← (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).1 rfl, ← hJc]
  exact Nat.card_congr eJ.toEquiv.symm

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
