module

public import Certificates.Data.J4M2.QStruct

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A CFSG.Quasithin.J4M2

@[expose] def cTab : Array V2 := frTable cMat

@[expose] def cMat2 : Array V2 := mulT cMat cTab

@[expose] def codeF (f : Bool × Nat × Nat) : Nat := (f.2.2 * 2 + (if f.1 then 1 else 0)) * 4096 + f.2.1

@[expose] def decodeF (n : Nat) : Bool × Nat × Nat := (decide (n / 4096 % 2 = 1), (n % 4096, n / 8192))

@[expose] def kRows (f : Bool × Nat × Nat) : Array V2 :=
  (List.range f.2.2).foldl (fun acc _ => mulT acc cTab) (qProd f.2.1 f.1)

@[expose] def kTab : Array (Array V2) := ((List.range 24576).map fun n => kRows (decodeF n)).toArray

@[expose] def cMask (c : Nat) : Nat :=
  (List.range 12).foldl (fun m k => if c.testBit k then m ^^^ (cNormData[k]!).1 else m) 0

@[expose] def hasForm (X : Array V2) (c i : Nat) : Bool :=
  decide (c < 4096) && decide (i < 3) &&
    (eqRows X kTab[codeF (false, c, i)]! || eqRows X kTab[codeF (true, c, i)]!)

@[expose] def chkClosure : Bool :=
  kTab.size == 24576 && kTab.all wfR &&
    (List.range 24576).all fun n =>
      let f := decodeF n
      let T := frTable kTab[n]!
      (List.range 12).all (fun j =>
        hasForm (mulT qM[j]! T) (f.2.1 ^^^ 2 ^ j) f.2.2 &&
          hasForm (mulT qI[j]! T) (f.2.1 ^^^ 2 ^ j) f.2.2) &&
        hasForm (mulT cMat T) (cMask f.2.1) ((f.2.2 + 1) % 3) &&
        hasForm (mulT cMat2 T) (cMask (cMask f.2.1)) ((f.2.2 + 2) % 3)

@[expose] def k3F : List (Bool × Nat × Nat) :=
  [false, true].flatMap fun e =>
    [(0, 0), (503, 0), (739, 2), (788, 2), (1160, 1), (1407, 1), (2581, 1), (3042, 1),
      (3198, 2), (3465, 2), (3741, 0), (3946, 0)].map fun ci => (e, ci.1, ci.2)

@[expose] def k3Mats : List (Array V2) := k3F.map fun f => kTab[codeF f]!

@[expose] def k3Tabs : List (Array V2) := k3Mats.map frTable

@[expose] def inK3 (X : Array V2) : Bool := k3Mats.any fun Y => eqRows X Y

@[expose] def normK3 (M Mi : Array V2) : Bool :=
  let TI := frTable Mi
  k3Tabs.all fun TX => inK3 (mulT (mulT M TX) TI)

@[expose] def chkNorm : Bool :=
  (List.range 24576).all fun n =>
    let M := kTab[n]!
    let Mi := invRows M
    wfR Mi && eqRows (mulT M (frTable Mi)) idRows &&
      (!normK3 M Mi || decide (decodeF n ∈ k3F))

@[expose] def mRows : Array V2 :=
  [15, 29, 1, 7, 9, 11].foldl (fun acc n => mulT acc gtabs[n]!) idRows

@[expose] def chkM : Bool :=
  let Mi := invRows mRows
  wfR mRows && wfR Mi && eqRows (mulT mRows (frTable Mi)) idRows && normK3 mRows Mi &&
    normK3 Mi mRows

@[expose] def kCheck : Bool := chkClosure && chkNorm && chkM

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck
