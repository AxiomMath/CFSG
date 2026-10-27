module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6All
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Sec6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf17Lab8Cor
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf17Lab8At
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinAt2

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin


namespace TwinThin

theorem thinCrossPairAEAt_proved {n : ℕ} (hA : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) :
    ThinCrossPairAEAt n := by
  intro G _ _ hG K₀ K K' z π g S hS hnab hodd m hm hJ
  obtain ⟨J⟩ := hJ
  have h4 : Thm4RTwinBelow 3 n := TwinThmEW.t4Supply_of_twoClass n hA hP
  have hE4 : E4SplitModel := e4SplitModel_of_certs
  rcases Nat.lt_or_ge m 6 with h5 | h6
  · obtain rfl : m = 5 := by omega
    exact S.thinCrossPair_five J
  · have hF7 : F7Cent K₀ π g := S.f7Cent h4 hG hS hnab h6 J hodd
    have hAut : TwinThinPf8.AEAut m := Cross.aeAut_of_five_le (by omega)
    by_cases h8 : m = 8
    · subst h8
      have htw : S.TwinLab 8 := S.twinLab8_of_f7 hS hnab hodd hF7
      obtain ⟨α, hα, b, hlab⟩ := J.label K S.mem_fam_self
      have hβ := S.beta_eq_pair_eight hF7 J hlab
      exact S.thinCrossPair_of_secYu hS hnab hodd h6 J htw (S.nbrPiTwin_of_beta hβ)
        (S.secYu_of hP h4 hE4 hG hS hnab hodd h6 hAut htw hβ J)
    · have htw : S.TwinLab m := fun J' _ _ _ hlab => S.map_twin_eq (by omega) h8 J' hlab
      have hβ := S.beta_eq_pair_of_ne_eight (by omega) h8 J
      exact S.thinCrossPair_of_secYu hS hnab hodd h6 J htw (S.nbrPiTwin_of_beta hβ)
        (S.secYu_of hP h4 hE4 hG hS hnab hodd h6 hAut htw hβ J)

end TwinThin

theorem twinThinAll_proved :
    ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → TwinThinInput n :=
  twinThinPack_of_thinAE fun _ hA hP =>
    TwinThin.thinAEAt_of_parts (TwinThin.thinCrossPairAEAt_proved hA hP)
      (TwinThin.thinTwinLab8At_proved hA hP)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
