module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KSix
public import Certificates.Certificate28040

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

theorem card_K₃sub_ge : 25920 ≤ Nat.card K₃sub :=
  Certificates.certificate28040

theorem K₃sub_eq_StabSub_cert : K₃sub = StabSub :=
  Subgroup.eq_of_le_of_card_ge K₃sub_le_StabSub (card_StabSub_le.trans card_K₃sub_ge)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
