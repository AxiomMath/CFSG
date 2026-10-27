module

public import CFSG.LargeExtraspecial.AS35YNFam
public import CFSG.LargeExtraspecial.A2ModD4Main

public section

namespace CFSG.LargeExtraspecial.S14

theorem asc512InspNondeg_ofN
    (hF : DW.DW2FieldInput) (hPSL : S12PSLModuleInputN)
    (hSp : S12SpModuleInputN) (hO : S12OmegaModuleInputN) (hM : S12ExcModuleInputN)
    (h5127 : Asc512FiveTwelveSevenStmt) (hfix : Asc512FixFreeStmt)
    (h43 : Asc512PSL4WidthThreeStmt) (hnat : Asc512POmegaNatStmt)
    (hU33 : Asc512U33ModuleInput) :
    Asc512InspFor fun (X : Type) [Group X] (D : Set X) =>
      InspNondeg X D ∧ CFSG.Timmesfeld.Outcome X :=
  asc512InspNondeg_ofN' hF hPSL hSp hO hM A2Mod.d42_commSpace h5127 hfix h43 hnat hU33

end CFSG.LargeExtraspecial.S14
