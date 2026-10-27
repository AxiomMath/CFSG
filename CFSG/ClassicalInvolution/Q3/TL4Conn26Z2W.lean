module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26Z2A
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Z2V

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Cit3b


variable {n : ℕ}

theorem tightLinkZ2AlphaR_of (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hOm : OmegaAutOddFreeR)
    (hLKM : LieKindZ2Model) : TightLinkZ2AlphaR 3 n := by
  intro Y _ _ R S t hL hc hA hcase hmod
  have hM : LinkZ2Model ↥(linkGrp R t) (linkFam R t) := by
    rcases hmod with hM | ⟨c, hc', hsec, hsh⟩
    · exact hM
    · exact hLKM _ _ c hc' hsec hsh
  exact tightLinkZ2Alpha_of h4 htw hOm (tightZ2TFreeR_proved n) Y R S t hL hc hA hcase
    hM.simple hM.nonab hM.inv hM.alpha hM.conj hM.gen hM.concl163

end Cit3b

end CFSG.ClassicalInvolution.Q3.TL4
