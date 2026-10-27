module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ExcQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.O8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.O8Outer

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Blueprint

section Certified


theorem excQuot_o8 {Q : Type} [Group Q] [Finite Q] (hQ : LieModel Q .POmegaPlus 4 2 1) :
    ExcQuot Q where
  center_eq_bot := o8_center hQ
  card_mulAut_dvd := dvd_of_eq (o8_card_mulAut hQ)
  fixLarge := fun σ hσ => o8_fixed_large o8Plus2OuterInvolutions_holds hQ σ hσ
  two_pow_dvd := by rw [o8_card hQ]; norm_num
  involution_centralizer := fun q hq2 hq1 => by
    rcases o8_card_centralizer hQ hq2 hq1 with h | h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
