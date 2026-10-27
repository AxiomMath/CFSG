module

public import CFSG.CGT.A8S.RelData
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CGT.A8S

open CFSG.CosetTable

@[expose] def collRelA8 (k : Fin 7) : A8Word :=
  (5, true) :: nWordA8 ++ (5, true) :: invA8 nWordA8 ++ (5, true) :: invA8 (wrongWordA8 k)

@[expose] def collRelsA8 (k : Fin 7) : List A8Word :=
  relsN0A8.map liftW5 ++ thetaRelsA8 ++ [collRelA8 k]

@[expose] def subWA8 : List A8Word := (subsetOf 6 (List.range 5)).map fun x => [(x, true)]

@[expose] def collapseCheckA8 (k : Fin 7) : Bool :=
  checkHLT (presParams (collRelsA8 k) subWA8) 400 1

end CFSG.CGT.A8S
