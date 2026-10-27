module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen13.Data

public section

namespace CFSG.AGLEmbedding.Norton.MON11_13

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.Gen13

@[expose] def thirteenEligibleCheck (_ : Unit) : Bool :=
  let c := Native.mkCtx ()
  let va := aV ()
  let vb := bV ()
  let vw := wV ()
  agreeC c va vb vw (gen13W0 ++ thirteenX) (thirteenX ++ gen13W0) &&
  agreeC c va vb vw (gen13W1 ++ thirteenX) (thirteenX ++ gen13W1) &&
  agreeC c va vb vw (thirteenK ++ thirteenZ) (thirteenZ ++ thirteenK) &&
  agreeC c va vb vw (gen13W5 ++ thirteenZ) (thirteenZ ++ gen13W5) &&
  agreeC c va vb vw (gen13W6 ++ thirteenZ) (thirteenZ ++ gen13W6) &&
  agreeC c va vb vw (gen13W7 ++ thirteenZ) (thirteenZ ++ gen13W7) &&
  agreeC c va vb vw (thirteenT0 ++ thirteenZ) (thirteenZ ++ thirteenT0)

end CFSG.AGLEmbedding.Norton.MON11_13
