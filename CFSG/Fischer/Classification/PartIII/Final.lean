module

public import CFSG.Fischer.Classification.PartIII.U.Rows
public import CFSG.Fischer.Classification.PartIII.U4.Four
public import CFSG.Fischer.Classification.PartIII.U4.FortyFive

public section

namespace CFSG.Fischer.Classification

theorem classicalPartIIIInputI : ClassicalPartIIIInputI :=
  classicalPartIIIInputI_of_U4
    (fun hH hnab _ hd φ hφ => classicalConclusion_of_localU2_four hH hnab hd φ hφ)
    (fun hH hnab _ hd _ hf h45 φ hφ =>
      classicalConclusion_of_localR3_five_of_ncard hH hnab hd hf h45 φ hφ)
    (fun hf₁ hf₂ h₁ h₂ _ _ hBA hA _ _ hc₁ hc₂ hτ₁ hτ₂ _ hz₂0 hz₂ hB₂ =>
      LocalU4.eq_sPt_of_tauChart_45 hf₁ hf₂ h₁ h₂ hBA hA hc₁ hc₂ hτ₁ hτ₂ hz₂0 hz₂ hB₂)

end CFSG.Fischer.Classification
