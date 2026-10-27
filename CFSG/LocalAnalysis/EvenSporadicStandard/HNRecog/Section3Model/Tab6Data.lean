module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.OrbitRowDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog.Section3

@[expose] def tab6Row0 : OrbRow where
  conj := [6, 3, 6, 7]
  m := 80
  n := 384
  stab := [[(1, 10)], [(1, 5), (2, 1), (1, 5), (2, 1)], [(1, 2), (2, 2), (1, 8), (2, 1)],
           [(1, 3), (2, 1), (1, 7), (2, 2)], [(1, 9), (2, 2), (1, 6), (2, 2)],
           [(1, 2), (2, 3), (1, 1), (2, 3), (1, 11)]]

@[expose] def tab6Row1 : OrbRow where
  conj := [3, 6, 4, 5, 3]
  m := 30
  n := 1024
  stab := [[(2, 2)], [(1, 1), (2, 3), (1, 1), (2, 3)], [(2, 1), (1, 5), (2, 3)],
           [(1, 4), (2, 1), (1, 11)]]

@[expose] def tab6Row2 : OrbRow where
  conj := [7, 2, 6, 2]
  m := 640
  n := 48
  stab := [[(2, 1), (1, 7), (2, 2), (1, 3)], [(1, 11), (2, 1), (1, 1)],
           [(1, 1), (2, 2), (1, 9), (2, 3), (1, 5)]]

@[expose] def tab6Row3 : OrbRow where
  conj := [5, 7, 6, 3, 4, 7, 2, 6, 2, 3]
  m := 480
  n := 64
  stab := [[(2, 2), (1, 3), (2, 1), (1, 7)],
           [(1, 2), (2, 1), (1, 2), (2, 1), (1, 1), (2, 3), (1, 3), (2, 1)],
           [(1, 2), (2, 2), (1, 8), (2, 2)], [(2, 3), (1, 3), (2, 1), (1, 7), (2, 3)],
           [(1, 2), (2, 3), (1, 11), (2, 3), (1, 6), (2, 1)]]

@[expose] def tab6Row4 : OrbRow where
  conj := [7, 2, 3, 7, 1, 6]
  m := 960
  n := 32
  stab := [[(2, 3), (1, 5), (2, 1), (1, 5)], [(2, 1), (1, 1), (2, 2), (1, 14)],
           [(1, 1), (2, 1), (1, 1), (2, 3), (1, 1), (2, 3), (1, 11)],
           [(1, 6), (2, 3), (1, 2), (2, 3), (1, 7), (2, 3), (1, 1), (2, 1)]]

@[expose] def tab6Row5 : OrbRow where
  conj := [2, 3, 1, 4, 3, 5, 1, 3, 6]
  m := 128
  n := 240
  stab := [[(1, 1), (2, 3), (1, 5)], [(1, 1), (2, 2), (1, 2), (2, 2), (1, 3)]]

@[expose] def tab6Row6 : OrbRow where
  conj := [2, 1, 6, 2]
  m := 1536
  n := 20
  stab := [[(1, 2), (2, 1), (1, 1), (2, 1), (1, 4), (2, 2)],
           [(1, 1), (2, 1), (1, 1), (2, 1), (1, 2), (2, 1), (1, 1), (2, 1), (1, 11)],
           [(1, 1), (2, 1), (1, 2), (2, 3), (1, 2), (2, 1), (1, 18), (2, 3)]]

@[expose] def tab6Row7 : OrbRow where
  conj := [2, 7, 5, 2]
  m := 1920
  n := 16
  stab := [[(1, 3), (2, 3), (1, 1), (2, 1), (1, 8), (2, 2)],
           [(2, 1), (1, 1), (2, 2), (1, 8), (2, 2), (1, 6), (2, 1)],
           [(1, 6), (2, 3), (1, 6), (2, 3), (1, 7), (2, 1)]]

@[expose] def tab6W0 : List ℕ :=
  [3, 7, 5, 6, 5, 7, 5, 7, 2, 7, 1, 5, 2, 3, 1, 6, 3, 7, 3, 1, 7, 2, 3]

@[expose] def tab6W1 : List ℕ :=
  [5, 6, 1, 2, 3, 7, 5, 6, 5, 7, 3, 2, 1, 7, 2, 7, 3, 1, 7, 3, 5, 7, 3]

@[expose] def tab6W3 : List ℕ :=
  [6, 5, 7, 6, 1, 7, 4, 2, 1, 6, 3, 6, 1, 2, 5, 6, 1]

@[expose] def tab6W4 : List ℕ :=
  [5, 7, 1, 6, 7, 6, 1, 3, 2, 1, 6, 3, 5, 6, 2, 7, 5, 6, 5, 7, 3, 5, 6, 1, 2, 1, 6, 5, 1]

@[expose] def tab6W5 : List ℕ :=
  [7, 6, 3, 7, 1, 7, 1, 2, 3, 7, 2, 7, 2, 3, 7, 5, 6, 5, 7, 3, 6, 1, 2, 1, 1, 6, 5, 6]

@[expose] def tab6W6 : List ℕ :=
  [1, 2, 6, 7, 3, 4, 1, 2, 1, 5, 6, 3, 1, 3, 6, 7, 2, 7, 2, 3, 1, 5]

@[expose] def tab6W7 : List ℕ :=
  [7, 2, 5, 6, 1, 5, 7, 3, 1, 2, 5, 3, 7, 2, 7, 1, 5, 3, 6, 7, 2, 7, 2, 3]

@[expose] def tab6Img2 : List (DihedralGroup 4 × Sym 3) :=
  [(DihedralGroup.sr (3 : ZMod 4), (Equiv.swap (0 : Fin 3) 2 : Sym 3)),
   (DihedralGroup.sr (2 : ZMod 4), (Equiv.swap (0 : Fin 3) 2 * Equiv.swap (2 : Fin 3) 1 : Sym 3)),
   (DihedralGroup.r (0 : ZMod 4), (Equiv.swap (0 : Fin 3) 2 : Sym 3))]

@[expose] def tab6Img4 : List (Elem2 2 × DihedralGroup 4) :=
  [(Multiplicative.ofAdd (![0, 1] : Fin 2 → ZMod 2), DihedralGroup.r (2 : ZMod 4)),
   (Multiplicative.ofAdd (![1, 0] : Fin 2 → ZMod 2), DihedralGroup.r (0 : ZMod 4)),
   (Multiplicative.ofAdd (![0, 0] : Fin 2 → ZMod 2), DihedralGroup.sr (1 : ZMod 4)),
   (Multiplicative.ofAdd (![1, 1] : Fin 2 → ZMod 2), DihedralGroup.r (3 : ZMod 4))]

@[expose] def tab6Img6 : List (Z 2 × DihedralGroup 5) :=
  [(Multiplicative.ofAdd (1 : ZMod 2), DihedralGroup.sr (4 : ZMod 5)),
   (Multiplicative.ofAdd (0 : ZMod 2), DihedralGroup.r (1 : ZMod 5)),
   (Multiplicative.ofAdd (0 : ZMod 2), DihedralGroup.sr (4 : ZMod 5))]

@[expose] def tab6Img7 : List (Z 2 × DihedralGroup 4) :=
  [(Multiplicative.ofAdd (0 : ZMod 2), DihedralGroup.r (3 : ZMod 4)),
   (Multiplicative.ofAdd (1 : ZMod 2), DihedralGroup.sr (0 : ZMod 4)),
   (Multiplicative.ofAdd (1 : ZMod 2), DihedralGroup.r (0 : ZMod 4))]

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
