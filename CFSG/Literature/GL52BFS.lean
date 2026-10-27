module

public import CFSG.Literature.GL52Lookup

public section

namespace CFSG.Literature.GL52

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

@[expose] def enumTables (gs : List G) (L : List (List ℤ)) : List Table :=
  L.map (wordT 31 (letterT (genTables gs) (genInvTables gs)))

@[expose] def enumOK (gs : List G) (L : List (List ℤ)) : Bool :=
  (enumTables gs L).any (fun T => tblEq 31 T (idT 31)) &&
    (enumTables gs L).all fun T => (genTables gs).all fun X =>
      (enumTables gs L).any fun U => tblEq 31 (compT 31 T X) U

end CFSG.Literature.GL52
