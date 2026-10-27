module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveEndConfig
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Linear
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.StronglyEmbedded.BenderBorelTransport
import CFSG.LieType.BorelTits.Suzuki
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.Blueprint.Catalog
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.OddStandard

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OutcomeLocal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL CFSG.ClassicalInvolution
open CFSG.Blueprint CFSG.Open

theorem fiveConfig_false_projectiveSL {f n : ℕ} (hf : 1 ≤ f) (hn : 2 ≤ n) {k : Type} [Field k]
    (hk : Nat.card k = 2 ^ f) (t : projectiveSL n k) (h : FiveConfig t) : False := by
  classical
  have ht : orderOf t = 2 := h.orderOf_eq
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : NeZero n := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (SpecialLinearGroup (Fin n) k) := inferInstance
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨s, rfl, hs⟩ := exists_sl_lift t htt
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  set U := flagKernel (dispRange s) (dispKer s) (dispRange_le_dispKer hs) with hUdef
  set Q := U.map (proj n k) with hQdef
  have hlift : ∀ c ∈ centralizer ({proj n k s} : Set (projectiveSL n k)),
      ∃ A : SpecialLinearGroup (Fin n) k, proj n k A = c ∧ A * s = s * A := by
    intro c hc
    obtain ⟨A, rfl⟩ := proj_surjective n k c
    exact ⟨A, rfl, commute_of_proj_commute hs (mem_centralizer_singleton_iff.mp hc)⟩
  have hQC : Q ≤ centralizer ({proj n k s} : Set (projectiveSL n k)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, commute_of_mem_flagKernel hs hu]
  have hQp : IsPGroup 2 Q := isPGroup_flagKernel.map (proj n k)
  have hnorm : ∀ c ∈ centralizer ({proj n k s} : Set (projectiveSL n k)), ∀ q ∈ Q,
      c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    obtain ⟨A, rfl, hAs⟩ := hlift c hc
    obtain ⟨u, hu, rfl⟩ := hq
    exact ⟨A * u * A⁻¹, conj_mem_flagKernel hs hAs hu, by rw [map_mul, map_mul, map_inv]⟩
  have hcen : ∀ c ∈ centralizer ({proj n k s} : Set (projectiveSL n k)),
      (∀ q ∈ Q, c * q = q * c) → c ∈ Q := by
    intro c hc hcQ
    obtain ⟨A, rfl, hAs⟩ := hlift c hc
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      exact ⟨A, mem_flagKernel_of_commute_two hs hs1 hAs, rfl⟩
    · exact mem_map_flagKernel_of_commute hn3 hf hk (dispRange_ne_bot hs1)
        (dispRange_le_dispKer hs) (dispKer_ne_top hs1)
        fun u hu => hcQ _ ⟨u, hu, rfl⟩
  refine h.false_of_twoConstrained hQC hQp
    (fun c hc => mem_normalizer_of_conj_mem fun q hq => hnorm c hc q hq) ?_
  rintro c ⟨hc, hcQ⟩
  exact hcen c hc fun q hq => ((mem_centralizer_iff.mp hcQ) q hq).symm

theorem fiveConfig_false_of_psl_model {X : Type} [Group X] {n f : ℕ}
    (h : StatedClassicalModel X .PSL n 2 f) (x : X) (hx : FiveConfig x) : False := by
  obtain ⟨⟨-, hf, hn, -, -⟩, K, _, _, hK, ⟨eT⟩⟩ := h
  let e' : X ≃* LinearFlag.projectiveSL n K :=
    eT.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  exact fiveConfig_false_projectiveSL hf hn hK (e' x) (hx.of_mulEquiv e')

theorem fiveConfig_false_of_suzukiModel {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel X 2 f) (x : X) (hx : FiveConfig x) : False := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  have e' := e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
    (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
  have hx' := hx.of_mulEquiv e'
  have : Finite (Sz a) := Finite.of_equiv X e'.toEquiv
  exact hx'.false_of_isSolvable
    (isSolvable_centralizer_of_fusionBenderBorel (bender_suzuki_borel_full a ha)
      hx'.orderOf_eq)

theorem fiveConfig_false_of_even_items {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSL 2 2 3 ∨ LieModel Y .PSL 2 2 4 ∨ LieModel Y .PSL 3 2 2 ∨
      LieModel Y .twistedB2 0 2 3) (y : Y) (hy : FiveConfig y) : False := by
  have hpsl : ∀ {n f : ℕ}, LieModel Y .PSL n 2 f → False := by
    intro n f h
    rcases h with ⟨-, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact fiveConfig_false_of_psl_model hm y hy
    · simp [chevalleyExceptionalTags] at ht
    · simp [reeTitsTags] at ht
    · exact absurd ht (by decide)
  rcases h with h | h | h | h
  · exact hpsl h
  · exact hpsl h
  · exact hpsl h
  · rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hm⟩
    · simp [classicalTags] at ht
    · simp [chevalleyExceptionalTags] at ht
    · simp [reeTitsTags] at ht
    · exact fiveConfig_false_of_suzukiModel hm y hy

end CFSG.OddStandard
