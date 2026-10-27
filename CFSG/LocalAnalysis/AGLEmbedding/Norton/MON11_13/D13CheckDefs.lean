module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.GenD13.Data

public section

namespace CFSG.AGLEmbedding.Norton.MON11_13

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.GenD13

@[expose] def d13Ag (w₁ w₂ : List Native.Gen) : Bool :=
  agreeC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) w₁ w₂

@[expose] def d13OrderCheck (_ : Unit) : Bool :=
  let c := Native.mkCtx ()
  let va := aV ()
  let vb := bV ()
  let vw := wV ()
  agreeC c va vb vw (powL 13 genD13W0) [] &&
  agreeC c va vb vw (powL 13 genD13W2) [] &&
  agreeC c va vb vw (powL 13 genD13W1) []

@[expose] def d13CommCheck (_ : Unit) : Bool :=
  let c := Native.mkCtx ()
  let va := aV ()
  let vb := bV ()
  let vw := wV ()
  agreeC c va vb vw (genD13W0 ++ genD13W1) (genD13W1 ++ genD13W0) &&
  agreeC c va vb vw (genD13W2 ++ genD13W1) (genD13W1 ++ genD13W2) &&
  agreeC c va vb vw (genD13W0 ++ genD13W2) (powL 4 genD13W1 ++ genD13W2 ++ genD13W0) &&
  EdgeNoncomm.moveCheck genD13W1 va &&
  agreeC c va vb vw genD13W8 (powL 3 genD13W4)

@[expose] def d13X1xCheck (_ : Unit) : Bool :=
  d13Ag (genD13W0 ++ genD13W3)
    (genD13W3 ++ powL 6 genD13W0 ++ powL 10 genD13W2 ++ powL 11 genD13W1)

@[expose] def d13X1yCheck (_ : Unit) : Bool :=
  d13Ag (genD13W2 ++ genD13W3)
    (genD13W3 ++ powL 1 genD13W0 ++ powL 7 genD13W2 ++ powL 3 genD13W1)

@[expose] def d13X2xCheck (_ : Unit) : Bool :=
  d13Ag (genD13W0 ++ genD13W4)
    (genD13W4 ++ powL 7 genD13W0 ++ powL 7 genD13W2 ++ powL 8 genD13W1)

@[expose] def d13X2yCheck (_ : Unit) : Bool :=
  d13Ag (genD13W2 ++ genD13W4)
    (genD13W4 ++ powL 5 genD13W0 ++ powL 7 genD13W2 ++ powL 6 genD13W1)

@[expose] def d13ANorm1Check (_ : Unit) : Bool :=
  let c := Native.mkCtx ()
  let va := aV ()
  let vb := bV ()
  let vw := wV ()
  agreeC c va vb vw (genD13W1 ++ genD13W5) (genD13W5 ++ powL 12 genD13W1) &&
  agreeC c va vb vw (genD13W2 ++ genD13W5) (genD13W5 ++ powL 12 genD13W1 ++ powL 12 genD13W2)

@[expose] def d13ANorm2Check (_ : Unit) : Bool :=
  let c := Native.mkCtx ()
  let va := aV ()
  let vb := bV ()
  let vw := wV ()
  agreeC c va vb vw (genD13W1 ++ genD13W6) (genD13W6 ++ powL 12 genD13W2) &&
  agreeC c va vb vw (genD13W2 ++ genD13W6) (genD13W6 ++ powL 1 genD13W1)

@[expose] def d13ANorm4Check (_ : Unit) : Bool :=
  let c := Native.mkCtx ()
  let va := aV ()
  let vb := bV ()
  let vw := wV ()
  agreeC c va vb vw (genD13W1 ++ genD13W7) (genD13W7 ++ powL 12 genD13W1) &&
  agreeC c va vb vw (genD13W2 ++ genD13W7) (genD13W7 ++ powL 10 genD13W1 ++ powL 8 genD13W2)

end CFSG.AGLEmbedding.Norton.MON11_13
