module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.Basic
public import Certificates.Certificate197001

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
open CFSG.ClassicalInvolution.Generic

set_option linter.unusedSectionVars false


theorem card_R0_le : Nat.card R0 ≤ 8 := by
  rw [card_eq_of_map map_R0]
  exact Certificates.certificate197001.2.2.2.2.2.2.2.2.2.2.2

theorem card_R0'_le : Nat.card R0' ≤ 8 := by
  rw [R0', conjSub, Subgroup.card_map_of_injective (MulAut.conj s1).injective]
  exact card_R0_le

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1
