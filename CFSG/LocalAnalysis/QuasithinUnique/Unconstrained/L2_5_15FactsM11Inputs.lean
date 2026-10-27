module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Words
public import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.QuasithinUnique.Unc25K1
open CFSG.Sporadic.Mathieu

abbrev M11G : Type := ↥CFSG.Blueprint.NativeSporadic.M11

@[expose] def evG (w : List Bool) : M11G := evB m11a m11b w

@[expose] def tWords : List (List Bool) :=
  [[],
    [true, false, true, false, true, false, true, true, true, false, true, false, true, true,
      true, false, true, true],
    [true, false, true, true, false, true, true, true, false, true, true, false, true, true,
      true, false, true, false, true, false],
    [true, false, true, false, true, true, false, true, true, false, true, false, true, false,
      true, true, false, true, true, false],
    [true, false, true, true, false, true, true, false, true, false, true, false, true, false,
      true, false, true, true, false, true, true],
    [true, true, false, true, true, false, true, false, true, false, true, true, true, false,
      true, false, true, true, true, false, true, false],
    [true, false, true, false, true, false, true, true, false, true, true, false, true, false,
      true, false, true, true, false, true, false, true, true, false],
    [true, false, true, true, false, true, false, true, false, true, true, false, true, false,
      true, true, false, true, false, true, false, true, false, true],
    [true, false, true, true, true, false, true, false, true, true, false, true, false, true,
      true, false, true, true, false, true, false]]

@[expose] def WsM : List (List Bool) :=
  [[], [false], [true, true], [false, false], [false, true, false, false],
    [true, true, false, true], [false, false, true, false], [true, false, true, true], [true]]

@[expose] def TlM : List M11G := tWords.map evG

@[expose] def aM : M11G := evG [true, false, true, false, true, false, true, true, true, false, true, false,
  true, true, true, false, true, true]

@[expose] def bM : M11G := evG [true, false, true, true, true, false, true, false, true, true, false, true,
  false, true, true, false, true, true, false, true, false]

@[expose] def PlM : List (M11G × M11G) :=
  (TlM.product TlM).filter
    (fun p => decide (p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ (p.1 * p.2) ^ 2 ≠ 1 ∧ (p.1 * p.2) ^ 4 = 1))

@[expose] def TlP : List (Equiv.Perm (Fin 11)) := TlM.map Subtype.val

end CFSG.QuasithinUnique.Unc25K1
