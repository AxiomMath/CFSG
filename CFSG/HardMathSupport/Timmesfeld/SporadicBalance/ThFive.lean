module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PairConj
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThThree
public import CFSG.Sporadic.Th.Max3.AllConjFinal
public import Certificates.Certificate16949
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

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFive

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
open scoped commutatorElement


local notation "regs5" => slpRows (rowsOf seedA) (rowsOf seedB) 118 prog5

local notation "R5" => slpJ a b prog5

local notation "C5" =>
  mulRows (mulRows (mulRows regs5[94]! regs5[105]!) (powRowsN regs5[94]! 4))
    (powRowsN regs5[105]! 4)

local notation "c5" => R5 94 * R5 105 * R5 94 ^ 4 * R5 105 ^ 4

theorem prog5_lt : prog5.all (Op.lt 118) = true := by decide +kernel

theorem thFive_facts : ThList.ThFiveFacts := Certificates.certificate16949

theorem rowsMatrix_regs5 : (regs5).size = 118 ∧ ∀ r < 118, rowsMatrix regs5[r]! = matJ (R5 r) :=
  rowsMatrix_slpRows rowsMatrix_seedA rowsMatrix_seedB prog5_lt

theorem rowsMatrix_x5 : rowsMatrix regs5[94]! = matJ (R5 94) := rowsMatrix_regs5.2 94 (by norm_num)

theorem rowsMatrix_y5 : rowsMatrix regs5[105]! = matJ (R5 105) :=
  rowsMatrix_regs5.2 105 (by norm_num)

theorem rowsMatrix_c5 : rowsMatrix C5 = matJ c5 := by
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_powRowsN,
    rowsMatrix_powRowsN, rowsMatrix_x5, rowsMatrix_y5, ← matJ_pow, ← matJ_pow, ← matJ_mul,
    ← matJ_mul, ← matJ_mul]

theorem hR5 : ∀ r < (regs5).size, rowsMatrix regs5[r]! = matJ (R5 r) := fun r hr =>
  rowsMatrix_regs5.2 r (rowsMatrix_regs5.1 ▸ hr)

theorem exists_conj_of_cube {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y c : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hc : c = x * y * x ^ (p - 1) * y ^ (p - 1))
    (hcx : c * x = x * c) (hcy : c * y = y * c)
    (hinj : ∀ i j k i' j' k' : ℕ, i < p → j < p → k < p → i' < p → j' < p → k' < p →
      x ^ i * y ^ j * c ^ k = x ^ i' * y ^ j' * c ^ k' → i = i' ∧ j = j' ∧ k = k')
    (hfac : (Nat.card G).factorization p = 3)
    (hconj : ∀ i j k : ℕ, i < p → j < p → k < p → i + j + k ≠ 0 →
      ∃ m : G, m * (x ^ i * y ^ j * c ^ k) = c * m)
    {s : G} (hs : orderOf s = p) : ∃ g : G, g * s * g⁻¹ = c := by
  have hp0 : 0 < p := hp.out.pos
  have hxy : ⁅x, y⁆ = c := by rw [hc, commutatorElement_eq_of_pow hp0 hx hy]
  have hzx : Commute ⁅x, y⁆ x := by rw [hxy]; exact hcx
  have hzy : Commute ⁅x, y⁆ y := by rw [hxy]; exact hcy
  have hQ : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 3 := by
    refine CFSG.SectionRank.LocalWitness.card_closure_eq_cube hp0 hx hy hzx hzy ?_
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
    simp only [hxy] at h
    obtain ⟨h1, h2, h3⟩ := hinj i j k i' j' k' i.2 j.2 k.2 i'.2 j'.2 k'.2 h
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))
  have hQfull : Nat.card (Subgroup.closure ({x, y} : Set G)) =
      p ^ (Nat.card (⊤ : Subgroup G)).factorization p := by
    rw [hQ, Subgroup.card_top, hfac]
  obtain ⟨g, -, hgQ⟩ := Co3T.exists_conj_mem_of_full le_top hQfull (Subgroup.mem_top s) hs
  obtain ⟨i, j, k, hi, hj, hk, hw⟩ :=
    CFSG.SectionRank.LocalWitness.mem_closure_normalForm hp0 hx hy hzx hzy hgQ
  rw [hxy] at hw
  have hwo : orderOf (g⁻¹ * s * g) = p := by rw [orderOf_inv_mul_mul, hs]
  have hijk : i + j + k ≠ 0 := by
    intro h0
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    have hk0 : k = 0 := by omega
    rw [hi0, hj0, hk0, pow_zero, pow_zero, pow_zero, mul_one, mul_one] at hw
    rw [hw, orderOf_one] at hwo
    exact hp.out.one_lt.ne hwo
  obtain ⟨m, hm⟩ := hconj i j k hi hj hk hijk
  refine ⟨m * g⁻¹, ?_⟩
  rw [← hw] at hm
  calc (m * g⁻¹) * s * (m * g⁻¹)⁻¹ = (m * (g⁻¹ * s * g)) * m⁻¹ := by group
    _ = c := by rw [hm]; group

theorem exists_conj_c5 {s : J} (hs : orderOf s = 5) : ∃ g : J, g * s * g⁻¹ = c5 := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine exists_conj_of_cube (c := c5) thFive_facts.x_pow thFive_facts.y_pow rfl thFive_facts.cx
    thFive_facts.cy thFive_facts.inj ?_ thFive_facts.conj hs
  rw [CFSG.Sporadic.Th.Max3.natCard_J,
    show (90745943887872000 : ℕ) = 5 ^ 3 * 725967551102976 by norm_num,
    factorization_pow_mul Nat.prime_five 3 _ (by norm_num)]

theorem card_centralizer_c5_le : Nat.card (Subgroup.centralizer ({c5} : Set J)) ≤ 3000 := by
  obtain ⟨w, hw, hc⟩ := exists_cent5_kernel
  obtain ⟨g, hg⟩ := exists_conj_c5 hw
  rw [← hg, card_centralizer_conj_eq]
  exact hc

set_option maxRecDepth 100000 in
theorem thFive_mem : ∀ i < 3000, ThList.el5 i ∈ Subgroup.centralizer ({c5} : Set J) := by
  intro i hi
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact thFive_facts.list_comm i hi

set_option maxRecDepth 100000 in
theorem thFive_complete :
    (∀ g ∈ Subgroup.centralizer ({c5} : Set J), ∃ i < 3000, ThList.el5 i = g) ∧
      Nat.card (Subgroup.centralizer ({c5} : Set J)) = 3000 := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  exact list_complete ThList.el5 thFive_mem thFive_facts.list_ne card_centralizer_c5_le

set_option maxRecDepth 100000 in
theorem gLAPPrimeCoreOf_c5_eq_bot :
    GLAPPrimeCoreOf 5 (Subgroup.centralizer ({c5} : Set J)) = ⊥ := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  exact gLAPPrimeCoreOf_eq_bot_of_list Nat.prime_five (k := 3) (by decide) ThList.el5
    thFive_mem thFive_facts.list_ne card_centralizer_c5_le (fun i => list5.wit[i]!)
    ThList.wit5_lt thFive_facts.list_wit

theorem oPrimeCoreTrivialAt_Th_five : OPrimeCoreTrivialAt 5 J := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine oPrimeCoreTrivialAt_of_cube (c := c5) thFive_facts.x_pow thFive_facts.y_pow rfl thFive_facts.cx
    thFive_facts.cy thFive_facts.inj ?_ thFive_facts.conj gLAPPrimeCoreOf_c5_eq_bot
  rw [CFSG.Sporadic.Th.Max3.natCard_J,
    show (90745943887872000 : ℕ) = 5 ^ 3 * 725967551102976 by norm_num,
    factorization_pow_mul Nat.prime_five 3 _ (by norm_num)]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFive

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint

theorem sporadicOPrimeHolds_Th_five :
    SporadicOPrimeHolds .Th 5 := by
  have hK : OPrimeCoreTrivialAt 5 (NativeSporadic.Carrier .Th) :=
    OPrimeCoreTrivialAt.of_mulEquiv' (K := NativeSporadic.Carrier .Th) (K' := CFSG.Sporadic.Th.J)
      CFSG.Sporadic.Th.thEquivJ ThFive.oPrimeCoreTrivialAt_Th_five
  exact fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv e hK

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
