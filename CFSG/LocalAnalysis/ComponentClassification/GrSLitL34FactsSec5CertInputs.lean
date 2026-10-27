module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover2CertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def h0w : List ℕ := [2, 0, 0, 1, 0, 1, 0, 2]

@[expose] def h0OK : Bool :=
  comp 42 (comp 42 (wordTab h0w) (wordTab h0w)) (wordTab h0w) == idTab 42 &&
    (List.range 16).all fun k => k == 0 ||
      (!(comp 42 (wordTab h0w) (wordTab (tg k)) == comp 42 (wordTab (tg k)) (wordTab h0w)) &&
        !(comp 42 (wordTab h0w) (wordTab (tg (4 * k))) ==
          comp 42 (wordTab (tg (4 * k))) (wordTab h0w)))

@[expose] def z0CommOK : Bool :=
  comp 42 (wordTab (tg 1)) (wordTab (tg 16)) ==
      comp 42 (comp 42 (wordTab (tg 4)) (wordTab (tg 16))) (wordTab (tg 1)) &&
    comp 42 (wordTab (tg 1)) (wordTab (tg 24)) ==
      comp 42 (comp 42 (wordTab (tg 8)) (wordTab (tg 24))) (wordTab (tg 1))

@[expose] def unitZ0OK : Bool :=
  comp 42 r₄T (wordTab (tg 4)) == comp 42 (wordTab (tg 4)) r₄T &&
    !(comp 42 r₄T (wordTab (tg 8)) == comp 42 (wordTab (tg 8)) r₄T) &&
    !(comp 42 r₄T (wordTab (tg 12)) == comp 42 (wordTab (tg 12)) r₄T) &&
    comp 42 r₄T (wordTab (tg 8)) == comp 42 (comp 42 (wordTab (tg 8)) (wordTab (tg 4))) r₄T

@[expose] def bit12OK : Bool := [0, 1, 2].all fun κ => commBit κ 1 2 false

@[expose] def centROK : Bool :=
  (enumBFS 42 gTabs 241920).tabs.toList.all fun t =>
    !((wordTabs wT₀).toList.all fun g => comp 42 t g == comp 42 g t) ||
      [0, 4, 8, 12].any fun k => t == wordTab (tg k)

@[noinline, expose] def sec5OK : Bool := h0OK && z0CommOK && unitZ0OK && bit12OK && centROK

end CFSG.ComponentClassification.GrSLit.L34Facts
