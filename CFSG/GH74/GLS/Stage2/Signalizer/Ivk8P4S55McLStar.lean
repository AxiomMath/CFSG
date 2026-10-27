module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55WtModel
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55McLWt
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame
public import CFSG.Sporadic.Recognition.McLASInvolutions
public import CFSG.Sporadic.Schreier.PairMcLFaithful
public import CFSG.Sporadic.McL
import Mathlib.Tactic.IntervalCases
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
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
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Recognition.McLASClasses
public import CFSG.Sporadic.Recognition.McLASThreeCount
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import Certificates.Certificate3085Base

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WtP

open Subgroup CFSG.GroupTheory.TwoWeights CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.Schreier

theorem mcl_not_pow_dvd {p : ℕ} (hp : 3 ≤ p) : ¬ p ^ 8 ∣ 898128000 := by
  intro h
  have hle := Nat.le_of_dvd (by norm_num) h
  have hp43 : p < 43 := by
    by_contra h1
    have h2 : 43 ^ 8 ≤ p ^ 8 := Nat.pow_le_pow_left (by omega) 8
    omega
  interval_cases p <;> omega

theorem mcl_central
    {Y : Type} [Group Y] [Finite Y]
    (hY : Blueprint.NativeSporadic.IsSporadic Y .McL) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A X : Subgroup Y} (hA : Nat.card ↥A = 2 ^ 7) {τ : Y} (hτA : τ ∈ A) (hτ2 : orderOf τ = 2)
    (hτc : ∀ g ∈ A, g * τ = τ * g) (hX : IsPGroup p ↥X)
    (hN : A ≤ normalizer (X : Set Y)) : X ≤ centralizer ({τ} : Set Y) := by
  obtain ⟨e0⟩ := hY
  have hcard : Nat.card Y = 898128000 := by
    rw [Nat.card_congr e0.toEquiv]
    exact CFSG.Sporadic.McL.card_McL
  have hfact : (Nat.card Y).factorization 2 = 7 := by
    rw [hcard, show (898128000 : ℕ) = 2 ^ 7 * 7016625 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hconj : ∀ u v : Y, orderOf u = 2 → orderOf v = 2 → IsConj u v := fun u v hu hv =>
    isConj_of_equiv_of_involutions e0 (fun u v hu hv => mcl_involutions_conj u v hu hv) hu hv
  have e1 : Y ≃* ↥mclP := e0.trans CFSG.Sporadic.Schreier.mclPermEquiv
  obtain ⟨a, u₁, u₂, u₃, x, y, ha, hu₁, hu₂, hu₃, hx, hy, hao, D⟩ := McLWt.mcl_weights
  have hD : Data (⟨a, ha⟩ : ↥mclP) ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ ⟨u₃, hu₃⟩ ⟨x, hx⟩ ⟨y, hy⟩ := data_of_coe D
  have ha2 : orderOf (⟨a, ha⟩ : ↥mclP) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hao
  obtain ⟨u₁', u₂', u₃', x', y', hu₁', hu₂', hu₃', hx', hy', D'⟩ :=
    @exists_data_of_model Y ↥mclP _ _ inferInstance e1 hconj 7 hfact _ _ _ _ _ _ ha2 hD
      _ hA _ hτA hτ2 hτc
  have hsmall : Nat.card ↥X < p ^ 8 :=
    card_lt_pow_eight hp2 hcard (fun q hq => mcl_not_pow_dvd hq) hX
  exact central_of_data hp2 D' hτA hu₁' hu₂' hu₃' hx' hy' hX hN hsmall

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WtP
