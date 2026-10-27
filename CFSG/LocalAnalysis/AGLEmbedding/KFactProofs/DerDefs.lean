module

public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.RankThree.Asc83Table.Native

structure Der where
  reg : Nat
  ord : Nat
  w : Word
deriving Inhabited

@[expose] def Der.facts (d : Der) : List MFact := [.ord d.reg d.ord, .eq [(d.reg, 1)] d.w]

@[expose] def derWf (av : List Nat) : List Der → Bool
  | [] => true
  | d :: ds => d.w.all (fun a => av.contains a.1) && derWf (d.reg :: av) ds

end CFSG.AGLEmbedding.R3
