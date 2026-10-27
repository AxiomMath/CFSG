module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.BotCase
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.Assembly
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.NoKleinG2

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.StructureLie

theorem gf2Thm1311Classical_holds
    : GF2Thm1311Classical := by
  intro V _ _ hsq H L hff hcl A hAH hA hcard hineq
  exact inf_ne_bot_of_kleinBigInv hsq hff
    (kleinBigInv_of_isClassicalTwoOrG2_of_G2 (fun q hv hp2 e => noKlein_G2 q hv hp2 e) hcl)
    hAH hA hcard hineq

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
