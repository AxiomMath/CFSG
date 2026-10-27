module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen11.Data

public section

namespace CFSG.AGLEmbedding.Norton.MON11_13

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.Gen11

@[expose] def elevenEligibleCheck (_ : Unit) : Bool :=
  let c := Native.mkCtx ()
  let va := aV ()
  let vb := bV ()
  let vw := wV ()
  agreeC c va vb vw (powL 11 gen11W0) [] &&
  agreeC c va vb vw (powL 11 gen11W1) [] &&
  agreeC c va vb vw (gen11W0 ++ gen11W1) (gen11W1 ++ gen11W0) &&
  agreeC c va vb vw (gen11W0 ++ gen11W2) (gen11W2 ++ powL 6 gen11W0 ++ powL 3 gen11W1) &&
  agreeC c va vb vw (gen11W0 ++ gen11W3) (gen11W3 ++ powL 4 gen11W1) &&
  agreeC c va vb vw (gen11W0 ++ gen11W4) (gen11W4 ++ powL 3 gen11W0) &&
  agreeC c va vb vw (gen11W0 ++ thirteenT0) (thirteenT0 ++ gen11W0) &&
  (EdgeNoncomm.moveCheck gen11W0 va || EdgeNoncomm.moveCheck gen11W0 vb ||
    EdgeNoncomm.moveCheck gen11W0 vw)

end CFSG.AGLEmbedding.Norton.MON11_13
