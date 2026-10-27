module

public import Certificates.Data.SmithECheck
public import Certificates.Data.SMod20BasicC8

public section

namespace CFSG.SmithE

@[expose] def c8Step (s x : Nat) : Nat :=
  let y := applyCols tvArr[c8Pts[s / 2]!]! x
  if s % 2 == 1 then y ^^^ x else y

@[expose] def c8Path (p : List Nat) (x : Nat) : Nat := p.foldl (fun x s => c8Step s x) x

@[expose] def tvWordApply (w : List Nat) (x : Nat) : Nat :=
  w.foldl (fun x r => applyCols tvArr[r]! x) x

@[expose] def rigW (e : Nat) : Nat := applyCols tvArr[0]! e ^^^ e

@[expose] def chkC8Pts : Bool :=
  c8Pts.size == 45 && c8Pts.all fun r =>
    decide (r < 693) && commuteB tvArr[r]! tvArr[0]! && commuteB tvArr[r]! tvArr[1]!

@[expose] def chkC8Fix : Bool :=
  (List.range (2 ^ 20)).all fun c =>
    (applyCols tvArr[0]! c == c && applyCols tvArr[1]! c == c) == decide (c < 256)

@[expose] def chkC8Restr : Bool :=
  (List.range 693).all fun s => let Ts := tvArr[s]!
    !(commuteB Ts tvArr[0]! && commuteB Ts tvArr[1]!) || c8Pts.all fun r =>
      !((List.range 8).all fun b => Ts[b]! == tvArr[r]![b]!) || s == r

@[expose] def chkC8Irr : Bool :=
  decide (c8Root < 256) && c8Root != 0 && c8Back.size == 256 && c8Fwd.size == 8 &&
    (List.range 256).all (fun d => d == 0 ||
      ((c8Back[d]!).all (fun s => decide (s < 90)) && c8Path c8Back[d]! d == c8Root)) &&
    (List.range 8).all fun b =>
      (c8Fwd[b]!).1.all (fun s => decide (s < 90)) &&
        (c8Fwd[b]!).2.all (fun s => decide (s < 90)) &&
        (c8Path (c8Fwd[b]!).1 c8Root ^^^ c8Path (c8Fwd[b]!).2 c8Root) == 2 ^ b

@[expose] def chkRigid : Bool :=
  rigW rigE0 != 0 &&
    rigS.all (fun s => c8Pts.contains s && applyCols tvArr[s]! (rigW rigE0) == rigW rigE0) &&
    (List.range (2 ^ 20)).all (fun e => let v := rigW e
      !(rigS.all fun s => applyCols tvArr[s]! v == v) || v == 0 || v == rigW rigE0) &&
    rigWords.size == 12 && rigCoef.size == 20 &&
    rigWords.all (fun w => w.all fun r => c8Pts.contains r || r == 0 || r == 1) &&
    (List.range 20).all fun m =>
      applyCols ((rigWords.map fun w => tvWordApply w (rigW rigE0)) ++
        #[1, 2, 4, 8, 16, 32, 64, 128]) rigCoef[m]! == 2 ^ m

end CFSG.SmithE
