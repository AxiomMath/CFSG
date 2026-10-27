module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusVacuity
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSz
public import CFSG.Quasithin.H13.QRCBenderModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open TauCeti CFSG.Blueprint

theorem suzukiModel_no_order_three (m : ℕ) (hm1 : 1 ≤ m) :
    ¬ ∃ η : MulAut ↥(suzukiGroup m (GaloisField 2 (2 * m + 1))),
      η ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived _ ∧
        η ^ 3 = 1 ∧ η ≠ 1 := by
  have hK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  have hZ := CFSG.Quasithin.H13.NQCore.center_suzukiGroup_eq_bot
    (a := m) (K := GaloisField 2 (2 * m + 1)) hm1 hK
  have h3 := CFSG.Quasithin.H13.QRC.not_three_dvd_card_suzukiGroup
    (a := m) (k := GaloisField 2 (2 * m + 1)) hK
  have hcyc := (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd
    (a := m) (K := GaloisField 2 (2 * m + 1)) hm1 hK).1
  haveI := hcyc
  have hcomm : ∀ a b : CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥(suzukiGroup m (GaloisField 2 (2 * m + 1))), a * b = b * a :=
    fun a b => (IsCyclic.isMulCommutative
      (α := CFSG.ComponentClassification.OuterAutomorphisms.Outer
        ↥(suzukiGroup m (GaloisField 2 (2 * m + 1))))).is_comm.comm a b
  exact not_exists_order_three_innAutDerived hZ hcomm h3

end CFSG.LocalAnalysis.GLTheoremA
