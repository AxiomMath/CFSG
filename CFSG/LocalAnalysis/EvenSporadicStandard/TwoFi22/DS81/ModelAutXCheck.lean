module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueFCCheck

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

set_option compiler.extract_closed false

@[expose] def axFixOK (act : Array (Array Nat)) (q : Nat → Bool) (fam : List (List Nat)) : Bool :=
  fam.all fun Z => Z.all q || decide (Z.length * fcFix act Z ≤ 2 ^ 8)

@[expose] def axCore (ms : Array (Array Nat)) (qs : Array Bool) (fam : List (List Nat))
    (act tab : Array (Array Nat)) (e : Nat) : Bool :=
  decide (ms.size = 2 ^ 8) && ms.all fcColsLt && fcDistinct ms && tab.all (·.all (· < ms.size)) &&
    decide (e < ms.size) && fam.contains [e] && fcExtOK tab e ms.size fam &&
    axFixOK act (fun k => qs[k]!) fam

@[expose] def axCheck (ms : Array (Array Nat)) (qs : Array Bool) (fam : List (List Nat)) : Bool :=
  let act := ms.map fcAct
  axCore ms qs fam act (fcMul ms act) (fcIdx ms idCols)

@[expose] def axWordCols (gc : Array (Array Nat)) (w : List Nat) : Array Nat :=
  w.foldr (fun k acc => compose gc[k]! acc) idCols

@[expose] def axWordsOK (gc : Array (Array Nat)) (qs : Array Bool) (ws : Array (List Nat))
    (ms : Array (Array Nat)) : Bool :=
  gc.all fcColsLt && decide (ws.size = ms.size) &&
    (List.range ms.size).all fun j =>
      ws[j]!.all (· < gc.size) && fcMatEq (axWordCols gc ws[j]!) ms[j]! &&
        (!qs[j]! || ws[j]!.all (· < 9))

end CFSG.EvenSporadicStandard.TwoFi22.DS81
