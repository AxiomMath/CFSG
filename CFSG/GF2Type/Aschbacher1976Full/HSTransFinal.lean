module

public import CFSG.GF2Type.Aschbacher1976Full.HSReduction
public import CFSG.GF2Type.Aschbacher1976Full.HSPartA
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCard
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCAssembly
public import CFSG.GF2Type.Aschbacher1976Full.HSPartE
public import CFSG.GF2Type.Aschbacher1976Full.HSTransAssembly
public import CFSG.GF2Type.Aschbacher1976Full.HSTransNT
public import CFSG.GF2Type.Aschbacher1976Full.HSTransStar
public import CFSG.GF2Type.Aschbacher1976Full.HSTransY

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint

theorem hsPartTrans_of_fin (hFin : FinStmt) : HSPartTrans :=
  hsPartTrans_of_inputs embedStmt_holds (starStmt_of_twoBases twoBasesStmt_holds) hFin
    yStructStmt_holds

theorem leafZ4Q8Sq_of_bad_fin
    (hBad : HSPartBad) (hFin : FinStmt) : Asc76LeafZ4Q8Sq :=
  leafZ4Q8Sq_of_cases hsPartA_holds hsPartCard_holds hBad (hsPartTrans_of_fin hFin) hsPartC_holds
      hsPartE_holds

end CFSG.GF2Type.Aschbacher1976Full.HS
