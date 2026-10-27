module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4FusYData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowTests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Data

public section

namespace CFSG.ComponentClassification.AS81.FusY

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.ComponentClassification.AS81.Q47

@[expose] def codeTab (n : ℕ) (reps : List (Array ℕ)) (z : Array ℕ) (L : List (Array ℕ)) :
    Array Bool :=
  Array.ofFn fun w : Fin 64 => inLN n L reps[w.val]! || inLN n L (mulN n reps[w.val]! z)

@[expose] def cosetCheck (n : ℕ) (qs : List (Array ℕ)) (e : Array ℕ) (L : List (Array ℕ)) :
    Bool :=
  qs.all fun q => !(eqA n (mulN n (mulN n e q) (mulN n e q)) (idA n)) || inLN n L (mulN n e q)

@[expose] def orbitCheck (K : List (Array ℕ)) (tab : Array Bool) : Bool :=
  (List.range 64).all fun v => v == 0 || q47Form[v]! != 0 || K.any fun k => tab[k[v]!]!

@[expose] def invCheck (K : List (Array ℕ)) (t : Array ℕ) (w : List ℕ) : Bool :=
  (List.range K.length).all fun i =>
    eqA 64 K[i]! (idA 64) || !(eqA 64 (mulN 64 K[i]! K[i]!) (idA 64)) ||
      (decide (w[i]! < K.length) && eqA 64 (conjA 64 K[w[i]!]! K[i]!) t)

@[expose] def modelFusCheck (n : ℕ) (Qg Eg Fg reps : List (Array ℕ)) (z : Array ℕ) (k₀ : ℕ)
    (Eb : List (Array ℕ)) (KE KF : List (List (Array ℕ))) (W : List (List ℕ)) : Bool :=
  let L := eltsN n (Eg ++ Fg)
  enumCheckN n (Eg ++ Fg) 256 && !(eqA 64 Eb[k₀]! (idA 64)) &&
    cosetCheck n (eltsN n Qg) Eg[k₀]! L &&
    (List.range 2).all fun i => (List.range 2).all fun j =>
      orbitCheck (eltsN 64 (KE[i]! ++ KF[j]!)) (codeTab n reps z L) &&
        invCheck (eltsN 64 (KE[i]! ++ KF[j]!)) Eb[k₀]! W[2 * i + j]!

@[expose] def fusYCheck : Bool :=
  modelFusCheck 16 heSylQ16 heSylE16 heSylF16 q47Rep16 heSylZ16 4 q47Eb16 q47KE16 q47KF16
      fusYWK16 &&
    modelFusCheck 32 heAutQ32 heAutE32 heAutF32 q47Rep32 heAutZ32 1 q47Eb32 q47KE32 q47KF32
      fusYWK32

end CFSG.ComponentClassification.AS81.FusY
