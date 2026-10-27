module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnFixed
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XType
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoIn
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieH
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Setup
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.SeitzGeneration.Hyper
public import CFSG.LieType.SeitzGeneration.HyperBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Abs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Facts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Lie
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E8D4Family

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoInAux
open CFSG.LocalAnalysis.GLTheoremA.K155XSp
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped MatrixGroups Matrix commutatorElement

theorem spPaired_exists_blockComponent {r n p : ℕ} {K : Type} [Field K] [Finite K]
    {x y : StatedSp r K} (hy : y ^ p = 1) (hxy : x * y = y * x)
    (hblocks : SpPrimaryBlocks 2 n p x (proj r K x))
    (O : ↥(reciprocalOrbits (spEnd x))) :
    ∃ yO ∈ spSupported x (O : Set K[X]), yO ^ p = 1 ∧
      ∀ g ∈ spSupported x (O : Set K[X]), Commute (yO⁻¹ * y) g := by
  classical
  haveI : Finite ↥(reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  haveI : Fintype ↥(reciprocalOrbits (spEnd x)) := Fintype.ofFinite _
  obtain ⟨hcomm, hind, hjoin⟩ := hblocks.directProduct
  let H : ↥(reciprocalOrbits (spEnd x)) → Subgroup (StatedSp r K) :=
    fun O => spSupported x (O : Set K[X])
  have hpair : Pairwise fun i j : ↥(reciprocalOrbits (spEnd x)) =>
      ∀ u v : StatedSp r K, u ∈ H i → v ∈ H j → Commute u v := by
    intro i j hij u v hu hv
    exact hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) u hu v hv
  have hyc : y ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm
  have hyrange : y ∈ (Subgroup.noncommPiCoprod hpair).range := by
    rw [Subgroup.noncommPiCoprod_range, hjoin]
    exact hyc
  obtain ⟨f, hf⟩ := hyrange
  have hinj : Function.Injective (Subgroup.noncommPiCoprod hpair) :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hfpow : f ^ p = 1 := by
    apply hinj
    rw [map_pow, hf, hy, map_one]
  refine ⟨(f O : StatedSp r K), (f O).2, ?_, ?_⟩
  · have hfO : (f ^ p) O = (1 : (i : ↥(reciprocalOrbits (spEnd x))) → H i) O :=
      congrArg (fun z : (i : ↥(reciprocalOrbits (spEnd x))) → H i => z O) hfpow
    have hsub : ((f O : ↥(H O)) ^ p) = 1 := by simpa using hfO
    exact congrArg Subtype.val hsub
  ·
    have hmain := Finset.noncommProd_erase_mul
      (Finset.univ : Finset ↥(reciprocalOrbits (spEnd x))) (Finset.mem_univ O)
      (fun i => (f i : StatedSp r K))
      (fun i _ j _ hij => hpair hij (f i) (f j) (f i).2 (f j).2)
    have hy' : y = (Finset.univ.erase O).noncommProd (fun i => (f i : StatedSp r K))
        (fun i _ j _ hij => hpair hij (f i) (f j) (f i).2 (f j).2) *
        (f O : StatedSp r K) := by
      rw [← hf, Subgroup.noncommPiCoprod_apply, ← hmain]
    have hcommFO : Commute (f O : StatedSp r K)
        ((Finset.univ.erase O).noncommProd (fun i => (f i : StatedSp r K))
          (fun i _ j _ hij => hpair hij (f i) (f j) (f i).2 (f j).2)) := by
      apply Finset.noncommProd_commute
      intro i hi
      have hne : i ≠ O := (Finset.mem_erase.mp hi).1
      exact hpair (Ne.symm hne) (f O) (f i) (f O).2 (f i).2
    have hz : (f O : StatedSp r K)⁻¹ * y =
        (Finset.univ.erase O).noncommProd (fun i => (f i : StatedSp r K))
          (fun i _ j _ hij => hpair hij (f i) (f j) (f i).2 (f j).2) := by
      rw [hy', ← hcommFO.eq]
      group
    intro g hg
    rw [hz]
    exact (Finset.noncommProd_commute (Finset.univ.erase O)
      (fun i => (f i : StatedSp r K)) _ g (fun i hi => by
        have hne : i ≠ O := (Finset.mem_erase.mp hi).1
        exact hpair (Ne.symm hne) g (f i) hg (f i).2)).symm

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
