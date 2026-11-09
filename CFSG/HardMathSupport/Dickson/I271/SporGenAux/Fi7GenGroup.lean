module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7GenData
public import CFSG.Sporadic.Fi24.Simple

public section

namespace CFSG.HardMathSupport.Dickson.I271.Fi7

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative

@[expose] def fi7Layout (_ : Unit := ()) : Bool :=
  let D := fi24SevenData
  let E := fi7Extra ()
  let Ws := D.words ++ E
  decide (D.words.size = 1087) && decide (E.size = 119) &&
    (D.words[0]! == [1]) && (D.words[1]! == [2]) &&
    (D.conj[91]!.1 == 1) && (D.conj[77]!.1 == 1) &&
    (E[0]! == D.conj[91]!.2.map lt2w) && (E[1]! == D.conj[77]!.2.map lt2w) &&
    (E[2]! == [-1090, 1088, 1090]) && (E[3]! == [-1090, 1089, 1090]) &&
    (E[4]! == [-1091, 1088, 1091]) && (E[5]! == [-1091, 1089, 1091]) &&
    ((List.range 112).all fun r => (Ws[1093 + r]!).all fun z =>
      decide (3 ≤ z.natAbs) && (isGen7 (z.natAbs - 3) ||
        (decide (1093 ≤ z.natAbs - 3) && decide (z.natAbs - 3 < 1093 + r)))) &&
    (E[118]! == [1087, 1085, 1086, 1086])

@[expose] noncomputable def g17 (j : ℕ) : CFSG.Sporadic.Fi24.J :=
  CFSG.Sporadic.Fi23.slpG CFSG.Sporadic.Fi24.genG (fi24SevenData.words ++ fi7Extra ()) j

structure Fi7Group : Prop where
  layout : fi7Layout () = true
  wa : g17 1203 = g17 0
  wb : g17 1204 = g17 1
  comm85 : g17 1085 * g17 67 = g17 67 * g17 1085
  comm86 : g17 1086 * g17 67 = g17 67 * g17 1086
  comm82 : g17 1082 * g17 66 = g17 66 * g17 1082
  comm83 : g17 1083 * g17 66 = g17 66 * g17 1083
  comm84 : g17 1084 * g17 66 = g17 66 * g17 1084
  pow4 : g17 1205 ^ 4 = 1
  pow2 : g17 1205 ^ 2 ≠ 1

end CFSG.HardMathSupport.Dickson.I271.Fi7
