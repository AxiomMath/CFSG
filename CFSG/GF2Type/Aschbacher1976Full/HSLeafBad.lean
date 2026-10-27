module

public import CFSG.GF2Type.Aschbacher1976Full.HSTransFinal
public import CFSG.GF2Type.Aschbacher1976Full.HSTransFin

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint

theorem leafZ4Q8Sq_of_bad
    (hBad : HSPartBad) : Asc76LeafZ4Q8Sq :=
  leafZ4Q8Sq_of_bad_fin hBad finStmt_holds

end CFSG.GF2Type.Aschbacher1976Full.HS
