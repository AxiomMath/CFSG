module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4CheckInputs
public import CFSG.Sporadic.Schreier.J4SData

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4

open CFSG.Sporadic.GLQ CFSG.Sporadic.J4Schreier

structure RowData where
  p : ℕ
  m : ℕ
  n : ℕ
  nregs : ℕ
  slp : String
  rz : ℕ
  ru : ℕ
  gens : List ℕ
  cols : List ℕ
  par : List ℕ
  gen : List ℕ
  sep : ℕ
  piCycles : List (List (Fin 24))
  ce : ℕ
  gam : ℕ

namespace RowData

@[expose] def col (D : RowData) (j : ℕ) : ℕ := D.cols.getD j 0

@[expose] def piPerm (D : RowData) : Equiv.Perm (Fin 24) :=
  CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs.permOfCycles D.piCycles

end RowData

@[expose] def duadSwap : Equiv.Perm (Fin 24) := Equiv.swap 4 11

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4
