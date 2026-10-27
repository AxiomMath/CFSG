module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLines
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporHeis
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporModule
public import CFSG.Sporadic.Co1Block.Perm
public import Certificates.Certificate2043
public import Certificates.Certificate3024
public import Certificates.Certificate9596
public import Certificates.Certificate13696
public import Certificates.Certificate14987
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1SevenBase
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowCo1Three
import CFSG.RankThree.PartOne.KS.Co1ScalCheck
import CFSG.Sporadic.Co1
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
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaGrpSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
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
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open

theorem wcOn_seven_of_fusion {K : Type} [Group K] [Finite K] {s t : K} (hs : s ^ 7 = 1)
    (ht : t ^ 7 = 1) (hst : s * t = t * s)
    (hcard : Nat.card (Subgroup.closure ({s, t} : Set K)) = 7 ^ 2) (h3 : ¬ 7 ^ 3 ∣ Nat.card K)
    {c₂ c₃ c₄ c₅ c₆ c₇ : K} (hx₂ : c₂ * (t * s ^ 1) = t * c₂) (hx₃ : c₃ * (t * s ^ 2) = t * c₃)
    (hx₄ : c₄ * (t * s ^ 3) = s * c₄) (hx₅ : c₅ * (t * s ^ 4) = s * c₅)
    (hx₆ : c₆ * (t * s ^ 5) = t * c₆) (hx₇ : c₇ * (t * s ^ 6) = s * c₇) : WCOn 7 K := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcomm : Commute s t := hst
  have cj : ∀ (g tg : K) (n : ℕ), g * (t * s ^ n) = tg * g → g * (s ^ n * t) * g⁻¹ = tg := by
    intro g tg n h
    rw [(hcomm.pow_left n).eq, mul_inv_eq_iff_eq_mul]
    exact h
  have cj' : ∀ (g tg : K) (n : ℕ), g * (t * s ^ n) = tg * g → g⁻¹ * tg * g = s ^ n * t := by
    intro g tg n h
    rw [← cj g tg n h]
    group
  refine WCOn.of_plane_fusion hs ht hst hcard h3 ?_ ?_
  ·
    refine ⟨c₄⁻¹, 3, 1, ?_, by decide +revert⟩
    rw [inv_inv, cj' c₄ s 3 hx₄, pow_one]
  · intro n hn
    interval_cases n
    ·
      refine ⟨c₂⁻¹, 1, 1, ?_, by decide +revert⟩
      rw [inv_inv, pow_zero, one_mul, cj' c₂ t 1 hx₂]
      simp
    · exact ⟨c₂, 0, 1, by rw [cj c₂ t 1 hx₂]; simp, by decide +revert⟩
    · exact ⟨c₃, 0, 1, by rw [cj c₃ t 2 hx₃]; simp, by decide +revert⟩
    · exact ⟨c₄, 1, 0, by rw [cj c₄ s 3 hx₄]; simp, by decide +revert⟩
    · exact ⟨c₅, 1, 0, by rw [cj c₅ s 4 hx₅]; simp, by decide +revert⟩
    · exact ⟨c₆, 0, 1, by rw [cj c₆ t 5 hx₆]; simp, by decide +revert⟩
    · exact ⟨c₇, 1, 0, by rw [cj c₇ s 6 hx₇]; simp, by decide +revert⟩

theorem wcOn_GA_seven :
    WCOn 7 ↥CFSG.Sporadic.Co1Schreier.GA := by
  open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S in
  have hS : Timmesfeld.Co1Seven.sylowOK CFSG.Sporadic.Co1Schreier.Native.aR
      CFSG.Sporadic.Co1Schreier.Native.bR = true := Certificates.certificate13696
  have h3 : ¬ 7 ^ 3 ∣ Nat.card ↥CFSG.Sporadic.Co1Schreier.GA := by
    rw [CFSG.Sporadic.Co1Schreier.card_GA_eq]
    norm_num
  open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S in
  exact wcOn_seven_of_fusion (sE_pow hS) (tE_pow hS) (sE_comm hS) (card_P0 hS) h3
    (by simpa [xE, tgtE, Timmesfeld.Co1Seven.fusTgt] using conj_to_target hS (k := 2) (by norm_num))
    (by simpa [xE, tgtE, Timmesfeld.Co1Seven.fusTgt] using conj_to_target hS (k := 3) (by norm_num))
    (by simpa [xE, tgtE, Timmesfeld.Co1Seven.fusTgt] using conj_to_target hS (k := 4) (by norm_num))
    (by simpa [xE, tgtE, Timmesfeld.Co1Seven.fusTgt] using conj_to_target hS (k := 5) (by norm_num))
    (by simpa [xE, tgtE, Timmesfeld.Co1Seven.fusTgt] using conj_to_target hS (k := 6) (by norm_num))
    (by simpa [xE, tgtE, Timmesfeld.Co1Seven.fusTgt] using conj_to_target hS (k := 7) (by norm_num))

theorem wcOn_Co1_seven_aux
    [Finite CFSG.Blueprint.NativeSporadic.Co1] :
    WCOn 7 CFSG.Blueprint.NativeSporadic.Co1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact WCOn.of_mulEquiv (K := CFSG.Blueprint.NativeSporadic.Co1)
    (L := CFSG.Sporadic.Co1Schreier.GA) CFSG.Sporadic.Co1Block.co1MatEquiv wcOn_GA_seven

theorem wcOn_Co1_seven
    [Finite (Carrier .Co1)] : WCOn 7 (Carrier .Co1) :=
  wcOn_Co1_seven_aux

theorem wcOn_Co1_five_aux
    [Finite CFSG.Blueprint.NativeSporadic.Co1] : WCOn 5 CFSG.Blueprint.NativeSporadic.Co1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact WCOn.of_hasNoncommPair (hasNoncommPair_of_commData (G := CFSG.Blueprint.NativeSporadic.Co1)
    Nat.prime_five CFSG.RankThree.PartOne.KS.Co1Scal.co1Scal_rel.commData
    CFSG.RankThree.PartOne.KS.Co1Scal.co1Scal_rel.z_eq)

theorem wcOn_Co1_five [Finite (Carrier .Co1)] :
    WCOn 5 (Carrier .Co1) :=
  wcOn_Co1_five_aux

theorem wcOn_Co1_three_aux
    [Finite CFSG.Blueprint.NativeSporadic.Co1] : WCOn 3 CFSG.Blueprint.NativeSporadic.Co1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : Nat.card CFSG.Blueprint.NativeSporadic.Co1 = 4157776806543360000 :=
    CFSG.Sporadic.Co1.card_Co1
  have hf : (Nat.card CFSG.Blueprint.NativeSporadic.Co1).factorization 3 = 9 := by
    rw [hN]
    exact factorization_eq_of_dvd Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
  have h := CFSG.HardMathSupport.Timmesfeld.SporadicRank.sylowData_of_modCheckE
    (CFSG.SectionRank.spec2 24) Nat.prime_three hN
    (by show 3 ^ 9 ∣ 4157776806543360000 ∧ ¬ 3 ^ 10 ∣ 4157776806543360000; norm_num)
    (by show 3 ^ 9 ≤ 27 * 3 ^ 6; norm_num) Certificates.certificate9596
  exact wcOn_of_sylowModuleData h (by rw [hf]; decide)

theorem wcOn_Co1_three
    [Finite (Carrier .Co1)] : WCOn 3 (Carrier .Co1) :=
  wcOn_Co1_three_aux

theorem wcSporadicAt_Co1
    [Finite (Carrier .Co1)] : WCSporadicAt .Co1 := by
  refine wcSporadicAt_of_card .Co1 (N := 4157776806543360000) CFSG.Sporadic.Co1.card_Co1 ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 4157776806543360000 = {2, 3, 5, 7, 11, 13, 23} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_Co1_three
  · exact wcOn_Co1_five
  · exact wcOn_Co1_seven
  all_goals (exfalso; norm_num at hdvd)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
