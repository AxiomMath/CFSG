module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenWords
public import CFSG.YGroups.Y443.Native.BrayWords

public section

namespace CFSG.AGLEmbedding.Norton.MON11_13

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native

@[expose] def eqWordsC (c : Native.Ctx) (w₁ w₂ : List Native.Gen) (v : Native.DVec) : Bool :=
  w₁.all Native.Gen.validB && w₂.all Native.Gen.validB &&
    (Native.evalWordC c w₁ v).eqv (Native.evalWordC c w₂ v)

@[expose] def eqWords3C (c : Native.Ctx) (w₁ w₂ : List Native.Gen) : Bool :=
  eqWordsC c w₁ w₂ (aV ()) && eqWordsC c w₁ w₂ (bV ()) && eqWordsC c w₁ w₂ (wV ())

theorem eqWords3C_mkCtx (w₁ w₂ : List Native.Gen) :
    eqWords3C (Native.mkCtx ()) w₁ w₂ = eqWords3 w₁ w₂ := rfl

@[expose] def neXC (c : Native.Ctx) (w₁ w₂ : List Native.Gen) (v : Native.DVec) (p : ℕ) : Bool :=
  w₁.all Native.Gen.validB && w₂.all Native.Gen.validB &&
    diffX (Native.evalWordC c w₁ v) (Native.evalWordC c w₂ v) p

theorem neXC_mkCtx (w₁ w₂ : List Native.Gen) (v : Native.DVec) (p : ℕ) :
    neXC (Native.mkCtx ()) w₁ w₂ v p = neX w₁ w₂ v p := rfl

@[expose] def thirteenP : ℕ := 576

@[expose] def thirteenOrderCheck (_ : Unit) : Bool :=
  let c := Native.mkCtx ()
  eqWords3C c (powL 13 thirteenX) []

@[expose] def thirteenRelCheck (_ : Unit) : Bool :=
  let c := Native.mkCtx ()
  eqWords3C c (thirteenX ++ thirteenXi) [] &&
  eqWords3C c (thirteenK ++ thirteenKi) [] &&
  eqWords3C c (thirteenYi ++ thirteenXi ++ thirteenY ++ thirteenX) thirteenZ &&
  eqWords3C c (thirteenX ++ thirteenZ) (thirteenZ ++ thirteenX) &&
  eqWords3C c (thirteenK ++ thirteenZ) (thirteenZ ++ thirteenK) &&
  eqWords3C c (thirteenT0 ++ thirteenX ++ thirteenT0) thirteenXi &&
  eqWords3C c (thirteenT0 ++ thirteenK) (thirteenK ++ thirteenT0) &&
  eqWords3C c (thirteenT0 ++ thirteenT0) [] &&
  neXC c thirteenZ [] (bV ()) thirteenP

end CFSG.AGLEmbedding.Norton.MON11_13
