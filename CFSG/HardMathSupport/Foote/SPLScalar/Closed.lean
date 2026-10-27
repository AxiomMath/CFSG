module

public import CFSG.HardMathSupport.Foote.SPLScalar.Final
public import CFSG.HardMathSupport.Foote.SPLScalar.UnitaryAltSix

public section

namespace CFSG.HardMathSupport.Foote.SPLScalar

open CFSG.AGLEmbedding

theorem unitarySingerStatement : UnitarySingerStatement :=
  fun _ _ _ _ hd hn hev he T E hET hE hE9 hEZ _ hw hw2 =>
    exists_singer_of_unitary hd hn hev he T E hET hE hE9 hEZ hw hw2

theorem kFactSPLInvolveScalar_of_ident
    (hId : KFactOneLieIdent) : KFactSPLInvolveScalar :=
  kFactSPLInvolveScalar_of_singer unitarySingerStatement hId

end CFSG.HardMathSupport.Foote.SPLScalar
