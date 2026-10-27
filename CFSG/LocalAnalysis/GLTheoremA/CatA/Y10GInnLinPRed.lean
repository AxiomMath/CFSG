module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinU64
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagLin)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (U64LinearPiece)

theorem innDiagLin_of_labelDict (hP2 : LinLabelDict) : InnDiagLin :=
  innDiagLin_of_pieces CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds
    LinPCompIsComp_holds hP2

theorem u64LinearPiece_of_labelDict_fieldLinComp3 (hP2 : LinLabelDict) (hFld : FieldLinComp3) :
    U64LinearPiece :=
  U64LinearPiece_of_pieces CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds
    LinPCompIsComp_holds hP2 LinAutDecomp3_holds hFld

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

end
