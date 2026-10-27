module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultThreeAux
public import CFSG.Sporadic.Recognition.LyonsLocalPerfect
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm47Statement
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestNative
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Recognition.CoverTransferWords
public import CFSG.Sporadic.Recognition.McLASThreeCount
public import CFSG.Sporadic.Recognition.McLMultiplierMatrix
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import Certificates.Certificate3085Base

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.LySchreier CFSG.GH74.GLS.Stage12
  CFSG.Sporadic.Recognition.LyonsSims

theorem lyMult_three
    {J T : Type} [Group J] [Finite J] [Group T]
    (hT : Nonempty (T ≃* NativeSporadic.Ly)) (π : J →* T) (hπ : Function.Surjective π)
    (hJ : Group.IsPerfect J) (hz : π.ker ≤ center J) (hp : IsPGroup 3 π.ker) : π.ker = ⊥ := by
  obtain ⟨eT⟩ := hT
  have hcard : Nat.card T = 51765179004000000 := by
    rw [Nat.card_congr eT.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly
  have hfin : Finite T := Finite.of_surjective π hπ
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover (oneClassDoubleCover_of_ly ⟨eT⟩)
  obtain ⟨x₁, x₂, x₃, S⟩ := D.exists_lyStd
  have hperf := D.isPerfect_centralizer S
  have hcen := D.center_centralizer S
  have hc3 := D.card_center_centralizer S
  obtain ⟨eM⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  have e : ↥(centralizer ({(x₁ : T)} : Set T)) ⧸ center ↥(centralizer ({(x₁ : T)} : Set T)) ≃*
      NativeSporadic.McL := (QuotientGroup.quotientMulEquivOfEq hcen).trans eM
  have hKp : IsPGroup 3 (center ↥(centralizer ({(x₁ : T)} : Set T))) :=
    IsPGroup.of_card (n := 1) (by rw [hc3, pow_one])
  have hKc : Nat.card (centralizer ({(x₁ : T)} : Set T)) = 2694384000 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center ↥(centralizer ({(x₁ : T)} : Set T)))
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL, hc3] at h1
    omega
  have hA := eq_one_of_mem_commutator_comap π hπ hz hp (centralizer ({(x₁ : T)} : Set T)) hperf
    (MulEquiv.refl _) hKp (by rw [hc3]; exact coverBound_of_equiv_mcl e)
  refine ker_eq_bot_of_local π hπ hJ hz hp (centralizer ({(x₁ : T)} : Set T)) ?_ hA
  rw [hKc, hcard, factorization_three_cover_mcl, factorization_three_lyOrder]

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult
