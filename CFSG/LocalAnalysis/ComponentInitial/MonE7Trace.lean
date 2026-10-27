module

public import CFSG.YGroups.Defs

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.MonE7

open CFSG.YGroups (wordFG)
open CFSG.Certificates.CosetEnumeration (evalWord)
open Classical

structure TraceState where
  count : ℕ
  ids : List (ℕ × ℕ)
  edges : List (ℕ × ℕ × ℕ)

end CFSG.LocalAnalysis.ComponentInitial.MonE7
