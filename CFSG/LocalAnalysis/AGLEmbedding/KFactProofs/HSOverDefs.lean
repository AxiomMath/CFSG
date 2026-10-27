module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2PermSound
public import CFSG.RankThree.Native.HSMcLSmallData
public import Certificates.Data.HSOverWords
public import Certificates.Data.HSFiveLocalP

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.RankThree.Native CFSG.AGLEmbedding.FusD2 Certificates.HSOver Certificates.MaxD2Heis

@[expose] noncomputable def hsOAB : List (Equiv.Perm (Fin 100)) := [hs100A, hs100B]

@[expose] noncomputable def hsOABU : List (Equiv.Perm (Fin 100)) := [hs100A, hs100B, hs100U]

@[expose] noncomputable def hsOU0 : Equiv.Perm (Fin 100) := wordVal hsOAB hsFiveUW
@[expose] noncomputable def hsOV0 : Equiv.Perm (Fin 100) := wordVal hsOAB hsFiveVW
@[expose] noncomputable def hsOT0 : Equiv.Perm (Fin 100) := wordVal hsOAB hsFiveTW
@[expose] noncomputable def hsOS0 : Equiv.Perm (Fin 100) := wordVal hsOAB hsFiveSW
@[expose] noncomputable def hsOGA : Equiv.Perm (Fin 100) := wordVal hsOAB hsOverGAW
@[expose] noncomputable def hsOGB : Equiv.Perm (Fin 100) := wordVal hsOAB hsOverGBW
@[expose] noncomputable def hsOW0 : Equiv.Perm (Fin 100) := wordVal hsOABU hsOverW0W
@[expose] noncomputable def hsOT : Equiv.Perm (Fin 100) := wordVal hsOAB hsOverTW
@[expose] noncomputable def hsOW : Equiv.Perm (Fin 100) := wordVal hsOAB hsOverWW
@[expose] noncomputable def hsOX : Equiv.Perm (Fin 100) := wordVal hsOAB hsOverXW
@[expose] noncomputable def hsOY : Equiv.Perm (Fin 100) := wordVal hsOAB hsOverYW
@[expose] noncomputable def hsOE1 : Equiv.Perm (Fin 100) := wordVal hsOAB hsOverE1W
@[expose] noncomputable def hsOE2 : Equiv.Perm (Fin 100) := wordVal hsOAB hsOverE2W
@[expose] noncomputable def hsOC : Equiv.Perm (Fin 100) := wordVal hsOAB hsOverCW

@[expose] def hsOR0 : Subgroup (Equiv.Perm (Fin 100)) := Subgroup.closure {hsOU0, hsOV0}
@[expose] def hsON0 : Subgroup (Equiv.Perm (Fin 100)) :=
  Subgroup.closure {hsOU0, hsOV0, hsOT0, hsOS0}
@[expose] def hsOUA2 : Subgroup (Equiv.Perm (Fin 100)) :=
  Subgroup.closure {hsOU0, hsOV0, hsOT0, hsOS0, hsOGA}
@[expose] def hsOUB2 : Subgroup (Equiv.Perm (Fin 100)) :=
  Subgroup.closure {hsOU0, hsOV0, hsOT0, hsOS0, hsOGB}
@[expose] def hsOUA : Subgroup (Equiv.Perm (Fin 100)) := Subgroup.closure {hsOX, hsOY}
@[expose] def hsONU : Subgroup (Equiv.Perm (Fin 100)) := Subgroup.closure {hsOU0, hsOV0, hsOT}

end CFSG.AGLEmbeddingD2
