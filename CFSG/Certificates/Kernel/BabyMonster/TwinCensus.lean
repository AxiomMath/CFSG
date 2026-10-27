module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinGen
public import CFSG.Certificates.Kernel.BabyMonster.TwinGen

namespace CFSG.KC.BM.Twin

open CFSG.KC.Eval

public meta def natOfBytes (b : ByteArray) (lo hi : Nat) : Nat := Id.run do
  let n := hi - lo
  let mut ws : Array UInt64 := Array.replicate ((n + 7) / 8) 0
  for i in [0:n] do
    ws := ws.modify (i / 8) (· ||| (b[lo + i]!.toUInt64 <<< (8 * (i % 8)).toUInt64))
  return natOfWords ws 0 ws.size

public meta def census (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let #[Val.nat sL, Val.nat hL, Val.nat sD, Val.nat hD, ts, rs] := args | throw "census: arguments"
  let Ts ← nats "Ts" ts
  let reps ← nats "reps" rs
  unless Ts.size == 12 do throw s!"{Ts.size} tables"
  let tab : Array (Array UInt32) := Ts.map fun T =>
    (Array.range 256).map fun b => ((T >>> (32 * b)) &&& 4294967295).toUInt32
  let mul (k v : Nat) : Nat :=
    (tab[3 * k]![v &&& 255]! ^^^ tab[3 * k + 1]![(v >>> 8) &&& 255]! ^^^ tab[3 * k + 2]![v >>> 16]!).toNat
  let N := 1 <<< 22
  let mut lab : ByteArray := ⟨Array.replicate N 0⟩
  let mut dt : ByteArray := ⟨Array.replicate N 0⟩
  let mut q : Array Nat := Array.mkEmpty N
  for (r, i) in reps.zipIdx do
    let a := (i + 1).toUInt8
    lab := lab.set! r a
    q := q.push r
    let mut h := q.size - 1
    while h < q.size do
      let u := q[h]!
      h := h + 1
      let du := dt[u]! >>> 2
      for t in [0:4] do
        let v := mul t u
        if v != 0 && lab[v]! == 0 then
          lab := lab.set! v a
          dt := dt.set! v (4 * (du + 1) + t.toUInt8)
          q := q.push v
  let mut lb : ByteArray := ⟨Array.replicate (N / 2) 0⟩
  for i in [0:N / 2] do
    lb := lb.set! i (lab[2 * i]! ||| (lab[2 * i + 1]! <<< 4))
  let LB := (Array.range 256).map fun c => natOfBytes lb (8192 * c) (8192 * (c + 1))
  let DT := (Array.range 512).map fun c => natOfBytes dt (8192 * c) (8192 * (c + 1))
  return (← outNats `LB sL hL LB) ++ (← outNats `DT sD hD DT)

end CFSG.KC.BM.Twin
