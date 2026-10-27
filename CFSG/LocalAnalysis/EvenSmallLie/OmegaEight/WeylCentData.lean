module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylFrameData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def dFixCheck : Bool :=
  allLt 112 fun r => (List.range 256).any fun m =>
    framePop m % 2 == 0 && m != 0 && (signArrs[m]!)[r]! == r

@[expose] def sOrbitCheck : Bool :=
  (List.range 240).all fun r => decide (r < 112) || (List.range 256).any fun m =>
    framePop m % 2 == 0 && (signArrs[m]!)[112]! == r

@[expose] def frameReflCheck : Bool :=
  allLt 8 fun i => (List.range 128).any fun a => (List.range 128).any fun b =>
    (reflArrs[112 + a]!)[112 + b]! == keyPts.getD i 0

@[expose] def wt2FixCheck : Bool :=
  (List.range 256).all fun m => !(framePop m % 2 == 0) || m == 0 ||
    ((fixCount 240 signArrs[m]! == 60) == (framePop m == 2))

@[expose] def tripleCheck : Bool :=
  (List.range 256).all fun a => !(framePop a == 2) || (List.range 256).all fun b =>
    !(framePop b == 2 && framePop (a ^^^ b) == 2) || (List.range 256).all fun c =>
      !(framePop c == 2 && framePop (a ^^^ c) == 2 && framePop (b ^^^ c) == 2 &&
        c != (a ^^^ b)) || (List.range 8).any fun k => a.testBit k && b.testBit k && c.testBit k

@[expose] def pairCheck2 : Bool :=
  (List.range 256).all fun a => !(framePop a == 2) || (List.range 256).all fun b =>
    !(framePop b == 2 && framePop (a ^^^ b) == 2) || (List.range 8).all fun k =>
      (List.range 8).all fun l =>
        !(a.testBit k && b.testBit k && a.testBit l && b.testBit l) || k == l

end CFSG.EvenSmallLie.OmegaEight.Weyl
