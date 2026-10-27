module

public import CFSG.HardMathSupport.Lang.E6Descent.FixedThreeE6
public import CFSG.HardMathSupport.Lang.E6Descent.RankE6
public import CFSG.HardMathSupport.Lang.E6Descent.RankTwistedE6

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

theorem fixedThreeE6_of_blackburn_griess
    (hB : RankBoundTStar) (hGA : CFSG.Open.GriessAllModelsStatement) :
    CFSG.AGLEmbedding.FixedThree.FixedThreeE6 :=
  fixedThreeE6_of_inputs hB hGA
    (fun q hv h3 => ⟨exists_elemAbelian_27_E6 q hv h3, three_pow_four_dvd_card_E6 q hv h3⟩)
    (fun q hv h3 =>
      ⟨exists_elemAbelian_27_twistedE6 q hv h3, three_pow_four_dvd_card_twistedE6 q hv h3⟩)

end CFSG.HardMathSupport.Lang.E6Descent
