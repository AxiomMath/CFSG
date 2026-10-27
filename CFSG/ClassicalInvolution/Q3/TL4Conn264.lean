module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264B
public import CFSG.ClassicalInvolution.Q3.TL4Conn264C

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

section Cit3

variable {n : ℕ}

theorem tightC26_4RG_of (hP : TightBelowRPlus 3 n) (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetBelow n) (hPair : TightC264Pair n)
    (hE2 : TightC264E2 n) (hTE4 : TightC264NoTwinE4 n) (hOm : TightC264Omega n) :
    TightC26_4RG n := by
  intro Y _ _ Rd Sd z J S R T W t hs hΛp hE
  by_cases hc : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t)
  · by_cases h2 : SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z
    · exact hE2 hP Y Rd Sd z J S R T W t hs hΛp hE hc h2
    · rcases hs.secTwinOmega_or_twinE4 h4 htw hc h2 with h4 | hom
      · exact absurd h4 (hTE4 hP Y Rd Sd z J S R T W t hs hΛp hE hc h2)
      · exact Or.inr (hOm hP Y Rd Sd z J S R T W t hs hΛp hE hc h2 hom)
  · obtain ⟨hKN, hJN⟩ := hs.secImg_normal_of_not_conj h4 hc
    exact Or.inl (hs.c264One_of_pair hKN (hPair hP Y Rd Sd z J S R T W t hs hΛp hE hKN hJN))

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
