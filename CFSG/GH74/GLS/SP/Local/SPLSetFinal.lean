module

public import CFSG.GH74.GLS.SP.Local.SPLSet
public import CFSG.GH74.GLS.SP.Local.SPLSL2Transport
public import CFSG.GH74.GLS.SP.Local.SPLSL2One
public import CFSG.GH74.GLS.SP.Local.SPLSL2Three

public section

namespace CFSG.GH74.GLS.SP.Local

theorem splLeafSet : SPLLeafSet :=
  splLeafSet_of_input (sl2OddAutTorus_of_SL2 sl2OddAutTorusSL2_one sl2OddAutTorusSL2_three)

end CFSG.GH74.GLS.SP.Local
