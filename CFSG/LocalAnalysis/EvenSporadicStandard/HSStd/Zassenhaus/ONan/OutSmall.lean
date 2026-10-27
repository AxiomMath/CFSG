module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.NoSL29Reduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.OutSmallLie
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.OutSmallSporadic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

theorem card_mulAut_le_six_of_onanList
    {N : Type} [Group N] [Finite N] (h : ONanList N) : Nat.card (MulAut N) ≤ 6 * Nat.card N := by
  unfold ONanList at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact card_mulAut_le_of_lieModel_psu_three_five h
  · exact card_mulAut_le_of_lieModel_psl_three_seven h
  · have := card_mulAut_le_of_isSporadic_m22 h
    omega
  · have := card_mulAut_le_of_isSporadic_m23 h
    omega
  · have := card_mulAut_le_of_isSporadic_m24 h
    omega
  · have := card_mulAut_le_of_isSporadic_hs h
    omega
  · have := card_mulAut_le_of_isSporadic_ru h
    omega
  · have := card_mulAut_le_of_lieModel_psl_five_two h
    omega
  · have := card_mulAut_le_of_isSporadic_j2 h
    omega
  · have := card_mulAut_le_of_lieModel_psp_two_two_two h
    omega

theorem onanOutSmall_holds :
    ONanOutSmall := by
  intro N _ _ h
  have h6 := card_mulAut_le_six_of_onanList h
  have hpos : 0 < Nat.card N := Nat.card_pos
  omega

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
