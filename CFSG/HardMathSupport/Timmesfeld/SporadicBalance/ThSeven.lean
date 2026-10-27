module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PairConj
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.PairConj
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThThree
public import CFSG.Sporadic.Th.Max3.AllConjFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenInputs
public import Certificates.Certificate16948
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSound
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiTransp
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase2
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.FischerOddCore.Basic
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate16018
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair


theorem centChecks_eq (st : BFSState) (n p0 bound c : ℕ) (Z X Y Z0 Z1 : Array V4)
    (zT xT yT yiT z0T z1T alphaT betaInvT gpl : Table) (q0 : Table × Table × Table) :
    centChecks st n p0 bound c Z X Y Z0 Z1 zT xT yT yiT z0T z1T alphaT betaInvT gpl q0
        (smallBFS (stripZ zT gpl alphaT betaInvT q0.2.1 q0.2.2 xT yiT p0).2[2]! 60 z0T z1T) =
      (centTableChecks st n c Z X Y Z0 Z1 zT xT yT yiT z0T z1T q0 &&
        centPlaneChecks n p0 bound zT xT yiT z0T z1T alphaT betaInvT gpl q0) := by
  simp only [centChecks, centTableChecks, centPlaneChecks, Bool.and_assoc]

local notation "regs7" => slpRows (rowsOf seedA) (rowsOf seedB) 43 prog7

local notation "R7" => slpJ a b prog7

theorem prog7_lt : prog7.all (Op.lt 43) = true := by decide +kernel

theorem thSeven_facts : ThList.ThSevenFacts := Certificates.certificate16948

theorem rowsMatrix_regs7 : (regs7).size = 43 ∧ ∀ r < 43, rowsMatrix regs7[r]! = matJ (R7 r) :=
  rowsMatrix_slpRows rowsMatrix_seedA rowsMatrix_seedB prog7_lt

local notation "x7" => R7 24

local notation "y7" => R7 25

local notation "z7" => x7 * y7 ^ 6

theorem rowsMatrix_x7 : rowsMatrix regs7[24]! = matJ x7 := rowsMatrix_regs7.2 24 (by norm_num)

theorem rowsMatrix_y7 : rowsMatrix regs7[25]! = matJ y7 := rowsMatrix_regs7.2 25 (by norm_num)

theorem rowsMatrix_z7 : rowsMatrix (mulRows regs7[24]! (powRowsN regs7[25]! 6)) = matJ z7 := by
  rw [rowsMatrix_mulRows, rowsMatrix_powRowsN, rowsMatrix_x7, rowsMatrix_y7, ← matJ_pow,
    ← matJ_mul]

theorem hR7 : ∀ r < (regs7).size, rowsMatrix regs7[r]! = matJ (R7 r) := fun r hr =>
  rowsMatrix_regs7.2 r (rowsMatrix_regs7.1 ▸ hr)

theorem thSeven_pair : x7 ^ 7 = 1 ∧ y7 ^ 7 = 1 ∧ matJ x7 * matJ y7 = matJ y7 * matJ x7 ∧
    x7 ≠ 1 ∧ ∀ k < 7, y7 ≠ x7 ^ k :=
  ⟨thSeven_facts.x_pow, thSeven_facts.y_pow, by rw [← matJ_mul, ← matJ_mul, thSeven_facts.comm],
    thSeven_facts.x_ne, thSeven_facts.y_ne⟩

theorem thSeven_conj {a b : ℕ} (ha : a < 7) (hb : b < 7) (hab : a + b ≠ 0) :
    ∃ m : J, matJ m * (matJ x7 ^ a * matJ y7 ^ b) = matJ z7 * matJ m := by
  obtain ⟨m, hm⟩ := thSeven_facts.conj a b ha hb hab
  refine ⟨m, ?_⟩
  rw [← matJ_pow, ← matJ_pow, ← matJ_mul, ← matJ_mul, ← matJ_mul]
  exact congrArg matJ hm

set_option maxRecDepth 100000 in
theorem thSeven_mem : ∀ i < 1176, ThList.el7 i ∈ Subgroup.centralizer ({z7} : Set J) := by
  intro i hi
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact thSeven_facts.list_comm i hi

theorem exists_conj_z7 {s : J} (hs : orderOf s = 7) : ∃ g : J, g * s * g⁻¹ = z7 := by
  obtain ⟨h7x, h7y, hcomm, hx1, hpow⟩ := thSeven_pair
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  refine CFSG.HardMathSupport.Dickson.I271.exists_conj_of_pair (matJ_injective ?_) h7x h7y hx1
    hpow ?_ (fun i j hi hj hij => ?_) s hs
  · simp only [matJ_mul]
    exact hcomm
  · rw [CFSG.Sporadic.Th.Max3.natCard_J,
      show (90745943887872000 : ℕ) = 7 ^ 2 * 1851958038528000 by norm_num,
      factorization_pow_mul Nat.prime_seven 2 _ (by norm_num)]
  · obtain ⟨m, hm⟩ := thSeven_conj hi hj hij
    refine ⟨m, matJ_injective ?_⟩
    simp only [matJ_mul, matJ_pow] at hm ⊢
    exact hm

theorem card_centralizer_z7_le : Nat.card (Subgroup.centralizer ({z7} : Set J)) ≤ 1176 := by
  obtain ⟨w, hw, hc⟩ := exists_cent7_kernel
  obtain ⟨g, hg⟩ := exists_conj_z7 hw
  rw [← hg, card_centralizer_conj_eq]
  exact hc

set_option maxRecDepth 100000 in
theorem thSeven_complete :
    (∀ c ∈ Subgroup.centralizer ({z7} : Set J), ∃ i < 1176, ThList.el7 i = c) ∧
      Nat.card (Subgroup.centralizer ({z7} : Set J)) = 1176 := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  exact list_complete ThList.el7 thSeven_mem thSeven_facts.list_ne card_centralizer_z7_le

set_option maxRecDepth 100000 in
theorem gLAPPrimeCoreOf_z7_eq_bot :
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({z7} : Set J)) = ⊥ := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  exact gLAPPrimeCoreOf_eq_bot_of_list Nat.prime_seven (k := 2) (by decide) ThList.el7
    thSeven_mem thSeven_facts.list_ne card_centralizer_z7_le (fun i => list7.wit[i]!)
    ThList.wit7_lt thSeven_facts.list_wit

theorem oPrimeCoreTrivialAt_Th_seven : OPrimeCoreTrivialAt 7 J := by
  obtain ⟨h7x, h7y, hcomm, hx1, hpow⟩ := thSeven_pair
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  refine oPrimeCoreTrivialAt_of_pair (z := z7) (matJ_injective ?_) h7x h7y hx1 hpow ?_
    (fun i j hi hj hij => ?_) gLAPPrimeCoreOf_z7_eq_bot
  · simp only [matJ_mul]
    exact hcomm
  · rw [CFSG.Sporadic.Th.Max3.natCard_J,
      show (90745943887872000 : ℕ) = 7 ^ 2 * 1851958038528000 by norm_num,
      factorization_pow_mul Nat.prime_seven 2 _ (by norm_num)]
  · obtain ⟨m, hm⟩ := thSeven_conj hi hj hij
    refine ⟨m, matJ_injective ?_⟩
    simp only [matJ_mul, matJ_pow] at hm ⊢
    exact hm

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint

theorem sporadicOPrimeHolds_Th_seven :
    SporadicOPrimeHolds .Th 7 := by
  have hK : OPrimeCoreTrivialAt 7 (NativeSporadic.Carrier .Th) :=
    OPrimeCoreTrivialAt.of_mulEquiv' (K := NativeSporadic.Carrier .Th) (K' := CFSG.Sporadic.Th.J)
      CFSG.Sporadic.Th.thEquivJ ThSeven.oPrimeCoreTrivialAt_Th_seven
  exact fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv e hK

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
