module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureCases
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTorus
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous
import CFSG.Adapters.RankTwoModelTransports
import CFSG.Adapters.StatedClassicalOrders
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate9124
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

private theorem wcP2_not_sq_dvd {q n p : ℕ} (hq4 : 4 ≤ q) (hq7 : q < 7) (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hn : n = (q ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, (q ^ i - 1)) / Nat.gcd 2 (q - 1)) :
    ¬ p ^ 2 ∣ n := by
  have hn' : n = 60 ∨ n = 210 := by
    simp only [Finset.Icc_self, Finset.prod_singleton] at hn
    interval_cases q <;> simp at hn <;> omega
  intro hdvd
  have hp2' := hp.two_le
  have hle : p ^ 2 ≤ 210 := by
    rcases hn' with rfl | rfl <;>
      exact (Nat.le_of_dvd (by norm_num) hdvd).trans (by norm_num)
  have hp14 : p ≤ 14 := by nlinarith
  interval_cases p <;> rcases hn' with rfl | rfl <;> omega

theorem wcOn_cross_psl_two {K : Type} [Group K] [Finite K] {ℓ f p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (h : CFSG.Open.StatedClassicalModel K .PSL 2 ℓ f) : WCOn p K := by
  have hℓ : ℓ.Prime := h.1.1
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hf : 1 ≤ f := h.1.2.1
  have hne2 : ℓ ^ f ≠ 2 := fun h2 => h.1.2.2.2.1 (by rw [h2])
  have hne3 : ℓ ^ f ≠ 3 := fun h3 => h.1.2.2.2.2 (by rw [h3])
  have hq2 : 2 ≤ ℓ ^ f :=
    hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have hq4 : 4 ≤ ℓ ^ f := by omega
  by_cases hq7 : 7 ≤ ℓ ^ f
  · obtain ⟨e⟩ :=
      CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField K 2 ℓ f h
    haveI : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ℓ f)) :=
      Finite.of_equiv K e.toEquiv
    refine WCOn.of_mulEquiv e (WCOn.of_isCyclic_sylow fun R => ?_)
    have hK : Nat.card (GaloisField ℓ f) = ℓ ^ f := GaloisField.card ℓ f (by omega)
    refine CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card (GaloisField ℓ f) hK
      (by rw [hK]; exact hq7) p hp2 ?_ R
    rw [hK]
    exact Nat.Coprime.pow_right f ((Nat.coprime_primes Fact.out hℓ).2 hpℓ)
  · refine WCOn.of_factorization_le_one ?_
    have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num : 0 < 2) h
    by_contra hlt
    have hlt' : 2 ≤ (Nat.card K).factorization p := by omega
    have hdvd : p ^ 2 ∣ Nat.card K :=
      ((Fact.out : p.Prime).pow_dvd_iff_le_factorization Nat.card_pos.ne').2 hlt'
    exact wcP2_not_sq_dvd hq4 (by omega) Fact.out hp2 hcard hdvd

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
