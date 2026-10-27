module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusVacuity
public import CFSG.Quasithin.H13.QRCBenderModels
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSz

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open TauCeti CFSG.Blueprint

theorem suzukiModel_no_order_three_general
    (m : ℕ) (hm1 : 1 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ¬ ∃ η : MulAut ↥(suzukiGroup m K),
      η ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived _ ∧
        η ^ 3 = 1 ∧ η ≠ 1 := by
  have hZ := CFSG.Quasithin.H13.NQCore.center_suzukiGroup_eq_bot (a := m) (K := K) hm1 hK
  have h3 := CFSG.Quasithin.H13.QRC.not_three_dvd_card_suzukiGroup (a := m) (k := K) hK
  have hcyc := (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd
    (a := m) (K := K) hm1 hK).1
  haveI := hcyc
  have hcomm : ∀ a b : CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥(suzukiGroup m K), a * b = b * a :=
    fun a b => (IsCyclic.isMulCommutative
      (α := CFSG.ComponentClassification.OuterAutomorphisms.Outer
        ↥(suzukiGroup m K))).is_comm.comm a b
  exact not_exists_order_three_innAutDerived hZ hcomm h3

end CFSG.LocalAnalysis.GLTheoremA
