module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowTests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowData

public section

namespace CFSG.ComponentClassification.AS81.HeSylow

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.ComponentClassification.GrSLit.HeldFix

@[expose] def interCountN (n : ℕ) (es qs : List (Array ℕ)) (k l : ℕ) : Bool :=
  ((eltsN n es).filter (inLN n (eltsN n qs))).length == k &&
    ((eltsN n es).filter fun t => !(inLN n (eltsN n qs) t)).length == l

@[expose] def centQN (n : ℕ) (gs qs : List (Array ℕ)) (z : Array ℕ) : Bool :=
  (eltsN n gs).all fun x => !(qs.all (commN n x)) || inZN n z x

@[expose] def heSylowQECheck : Bool :=
  interCountN 16 heSylE16 heSylQ16 16 48 && interCountN 16 heSylF16 heSylQ16 16 48 &&
    centQN 16 heSyl16 heSylQ16 heSylZ16 &&
    interCountN 32 heAutE32 heAutQ32 16 48 && interCountN 32 heAutF32 heAutQ32 16 48 &&
    centQN 32 hfT0Tabs32.toList heAutQ32 heAutZ32

end CFSG.ComponentClassification.AS81.HeSylow
