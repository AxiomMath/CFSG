module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResResidue
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResA6
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSG2
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResFinal

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint

@[expose] def Ega81CaseU43 : Prop :=
  Ega81Sit fun _ _ _ _ _ _ _ C _ =>
    LieModel (egaLayer (egQD C ⧸ fusionOddCore (egQD C))) .PSU 4 3 1 → False

theorem ega81Residue_of_cU43
    (hG : Goldschmidt74Cor4)
    (hU43 : Ega81CaseU43) : Ega81Residue :=
  ⟨residue_cA6 hG, residue_cA8, residue_cU42, residue_cL52, residue_cU52, residue_cSp44, hU43,
    DRes.residue_cStruct, DRes.residue_dPos⟩

end CFSG.EvenSporadicStandard.M24Std
