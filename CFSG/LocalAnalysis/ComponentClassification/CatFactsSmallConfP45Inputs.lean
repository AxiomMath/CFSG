module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfProps
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks2
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks

public section

namespace CFSG.ComponentClassification.CatFactsSmall.PSp43

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.ComponentClassification.GSThmB

local notation "PX" => Equiv.Perm (Fin 45)

@[expose] def cfZ : PX := List.formPerm [0, 15] * List.formPerm [1, 34] *
    List.formPerm [2, 40] * List.formPerm [3, 12] * List.formPerm [4, 41] *
    List.formPerm [5, 33] * List.formPerm [7, 32] * List.formPerm [8, 39] *
    List.formPerm [10, 43] * List.formPerm [11, 31] * List.formPerm [13, 28] *
    List.formPerm [14, 37] * List.formPerm [17, 30] * List.formPerm [18, 44] *
    List.formPerm [19, 36] * List.formPerm [20, 24] * List.formPerm [21, 25] *
    List.formPerm [22, 26] * List.formPerm [23, 35] * List.formPerm [27, 38]

@[expose] def cfTau : PX := s045 * (g045⁻¹ * s045 * g045)

@[expose] def cfHgens : List PX := q0gens ++ [g045]

@[expose] def cfQH : RawSchreierDatum 45 :=
  certificate (by decide) (cfHgens.map tab) [[2, 4], [3, 4]] #v[1, 3] (by decide)

@[expose] def cfRx : PX := List.formPerm [0, 12, 20, 27] *
    List.formPerm [1, 44, 5, 39, 23, 30, 28, 7] *
    List.formPerm [2, 19, 41, 11, 21, 22, 14, 43] * List.formPerm [3, 24, 38, 15] *
    List.formPerm [4, 10, 25, 36, 37, 31, 40, 26] * List.formPerm [6, 29, 9, 42] *
    List.formPerm [8, 34, 17, 33, 32, 35, 18, 13]

@[expose] def cfRgens : List PX := cfHgens ++ [cfRx]

@[expose] def cfQR : RawSchreierDatum 45 :=
  certificate (by decide) (cfRgens.map tab) [[2, 4], [3, 4]] #v[1, 3] (by decide)

@[expose] def cfTzu : PX := List.formPerm [0, 38, 24, 3] *
    List.formPerm [1, 31, 4, 17] * List.formPerm [2, 8, 33, 26] *
    List.formPerm [5, 19, 40, 7] * List.formPerm [6, 42] * List.formPerm [9, 29] *
    List.formPerm [10, 37, 18, 23] * List.formPerm [11, 14, 30, 35] *
    List.formPerm [12, 15, 27, 20] * List.formPerm [13, 36, 21, 32] *
    List.formPerm [22, 25, 39, 28] * List.formPerm [34, 43, 41, 44]

@[expose] def cfTzv : PX := List.formPerm [0, 15] * List.formPerm [1, 35] *
    List.formPerm [2, 25] * List.formPerm [3, 12] * List.formPerm [4, 14] *
    List.formPerm [5, 13] * List.formPerm [7, 8] * List.formPerm [10, 11] *
    List.formPerm [17, 44] * List.formPerm [18, 30] * List.formPerm [19, 26] *
    List.formPerm [20, 24] * List.formPerm [21, 40] * List.formPerm [22, 36] *
    List.formPerm [23, 34] * List.formPerm [27, 38] * List.formPerm [28, 33] *
    List.formPerm [31, 43] * List.formPerm [32, 39] * List.formPerm [37, 41]

@[expose] def cfK0 : PX := List.formPerm [0, 3, 24, 38] *
    List.formPerm [1, 17, 4, 31] * List.formPerm [2, 26, 33, 8] *
    List.formPerm [5, 7, 40, 19] * List.formPerm [6, 42] * List.formPerm [9, 29] *
    List.formPerm [10, 23, 18, 37] * List.formPerm [11, 35, 30, 14] *
    List.formPerm [12, 20, 27, 15] * List.formPerm [13, 32, 21, 36] *
    List.formPerm [22, 28, 39, 25] * List.formPerm [34, 44, 41, 43]

@[expose] def cfR1 : PX := List.formPerm [0, 38, 15, 27] *
    List.formPerm [1, 25, 34, 21] * List.formPerm [2, 23, 40, 35] *
    List.formPerm [3, 24, 12, 20] * List.formPerm [4, 13, 41, 28] *
    List.formPerm [5, 37, 33, 14] * List.formPerm [7, 22, 32, 26] *
    List.formPerm [8, 36, 39, 19] * List.formPerm [10, 44, 43, 18] *
    List.formPerm [11, 17, 31, 30] * List.formPerm [29, 42]

@[expose] def cfS1 : PX := List.formPerm [1, 2] * List.formPerm [4, 5] *
    List.formPerm [7, 8] * List.formPerm [10, 11] * List.formPerm [13, 14] *
    List.formPerm [17, 18] * List.formPerm [19, 22] * List.formPerm [20, 24] *
    List.formPerm [21, 23] * List.formPerm [25, 35] * List.formPerm [26, 36] *
    List.formPerm [27, 38] * List.formPerm [28, 37] * List.formPerm [29, 42] *
    List.formPerm [30, 44] * List.formPerm [31, 43] * List.formPerm [32, 39] *
    List.formPerm [33, 41] * List.formPerm [34, 40]

@[expose] def cfR2 : PX := List.formPerm [0, 12, 15, 3] *
    List.formPerm [1, 14, 35, 4] * List.formPerm [2, 13, 25, 5] *
    List.formPerm [6, 9] * List.formPerm [7, 10, 8, 11] *
    List.formPerm [17, 22, 44, 36] * List.formPerm [18, 19, 30, 26] *
    List.formPerm [20, 27, 24, 38] * List.formPerm [21, 33, 40, 28] *
    List.formPerm [23, 41, 34, 37] * List.formPerm [31, 32, 43, 39]

@[expose] def cfS2 : PX := List.formPerm [0, 15] * List.formPerm [1, 34] *
    List.formPerm [2, 40] * List.formPerm [4, 37] * List.formPerm [5, 28] *
    List.formPerm [6, 9] * List.formPerm [7, 31] * List.formPerm [8, 43] *
    List.formPerm [10, 39] * List.formPerm [11, 32] * List.formPerm [13, 33] *
    List.formPerm [14, 41] * List.formPerm [17, 26] * List.formPerm [18, 36] *
    List.formPerm [19, 44] * List.formPerm [21, 25] * List.formPerm [22, 30] *
    List.formPerm [23, 35] * List.formPerm [27, 38]

@[expose] def cfQD1 : RawSchreierDatum 45 :=
  certificate (by decide) [tab cfR1, tab cfS1] [] #v[1] (by decide)

@[expose] def cfQD2 : RawSchreierDatum 45 :=
  certificate (by decide) [tab cfR2, tab cfS2] [] #v[1] (by decide)

@[expose] def cfQD12 : RawSchreierDatum 45 :=
  certificate (by decide) [tab cfR1, tab cfS1, tab cfR2, tab cfS2] [[1, 1, 4], [2, 1, 3, 3]]
    #v[1, 3] (by decide)

@[expose] def cfF1a : PX := List.formPerm [0, 15] * List.formPerm [1, 34] *
    List.formPerm [2, 40] * List.formPerm [4, 37] * List.formPerm [5, 28] *
    List.formPerm [6, 9] * List.formPerm [7, 31] * List.formPerm [8, 43] *
    List.formPerm [10, 39] * List.formPerm [11, 32] * List.formPerm [13, 33] *
    List.formPerm [14, 41] * List.formPerm [17, 26] * List.formPerm [18, 36] *
    List.formPerm [19, 44] * List.formPerm [21, 25] * List.formPerm [22, 30] *
    List.formPerm [23, 35] * List.formPerm [27, 38]

@[expose] def cfF1b : PX := List.formPerm [0, 15] * List.formPerm [1, 35] *
    List.formPerm [2, 25] * List.formPerm [3, 12] * List.formPerm [4, 14] *
    List.formPerm [5, 13] * List.formPerm [7, 8] * List.formPerm [10, 11] *
    List.formPerm [17, 44] * List.formPerm [18, 30] * List.formPerm [19, 26] *
    List.formPerm [20, 24] * List.formPerm [21, 40] * List.formPerm [22, 36] *
    List.formPerm [23, 34] * List.formPerm [27, 38] * List.formPerm [28, 33] *
    List.formPerm [31, 43] * List.formPerm [32, 39] * List.formPerm [37, 41]

@[expose] def cfF1c : PX := List.formPerm [1, 2] * List.formPerm [4, 5] *
    List.formPerm [7, 8] * List.formPerm [10, 11] * List.formPerm [13, 14] *
    List.formPerm [17, 18] * List.formPerm [19, 22] * List.formPerm [20, 24] *
    List.formPerm [21, 23] * List.formPerm [25, 35] * List.formPerm [26, 36] *
    List.formPerm [27, 38] * List.formPerm [28, 37] * List.formPerm [29, 42] *
    List.formPerm [30, 44] * List.formPerm [31, 43] * List.formPerm [32, 39] *
    List.formPerm [33, 41] * List.formPerm [34, 40]

@[expose] def cfF1d : PX := List.formPerm [3, 12] * List.formPerm [4, 14] *
    List.formPerm [5, 13] * List.formPerm [6, 9] * List.formPerm [7, 11] *
    List.formPerm [8, 10] * List.formPerm [17, 22] * List.formPerm [18, 19] *
    List.formPerm [20, 24] * List.formPerm [26, 30] * List.formPerm [28, 33] *
    List.formPerm [31, 32] * List.formPerm [36, 44] * List.formPerm [37, 41] *
    List.formPerm [39, 43]

@[expose] def cfF1 : List PX := [cfF1a, cfF1b, cfF1c, cfF1d]

@[expose] def cfF2a : PX := List.formPerm [0, 15] * List.formPerm [1, 34] *
    List.formPerm [2, 40] * List.formPerm [4, 37] * List.formPerm [5, 28] *
    List.formPerm [6, 9] * List.formPerm [7, 31] * List.formPerm [8, 43] *
    List.formPerm [10, 39] * List.formPerm [11, 32] * List.formPerm [13, 33] *
    List.formPerm [14, 41] * List.formPerm [17, 26] * List.formPerm [18, 36] *
    List.formPerm [19, 44] * List.formPerm [21, 25] * List.formPerm [22, 30] *
    List.formPerm [23, 35] * List.formPerm [27, 38]

@[expose] def cfF2b : PX := List.formPerm [0, 15] * List.formPerm [1, 35] *
    List.formPerm [2, 25] * List.formPerm [3, 12] * List.formPerm [4, 14] *
    List.formPerm [5, 13] * List.formPerm [7, 8] * List.formPerm [10, 11] *
    List.formPerm [17, 44] * List.formPerm [18, 30] * List.formPerm [19, 26] *
    List.formPerm [20, 24] * List.formPerm [21, 40] * List.formPerm [22, 36] *
    List.formPerm [23, 34] * List.formPerm [27, 38] * List.formPerm [28, 33] *
    List.formPerm [31, 43] * List.formPerm [32, 39] * List.formPerm [37, 41]

@[expose] def cfF2c : PX := List.formPerm [3, 12] * List.formPerm [4, 14] *
    List.formPerm [5, 13] * List.formPerm [6, 9] * List.formPerm [7, 11] *
    List.formPerm [8, 10] * List.formPerm [17, 22] * List.formPerm [18, 19] *
    List.formPerm [20, 24] * List.formPerm [26, 30] * List.formPerm [28, 33] *
    List.formPerm [31, 32] * List.formPerm [36, 44] * List.formPerm [37, 41] *
    List.formPerm [39, 43]

@[expose] def cfF2d : PX := List.formPerm [0, 38] * List.formPerm [1, 23] *
    List.formPerm [2, 25] * List.formPerm [3, 20] * List.formPerm [4, 41] *
    List.formPerm [6, 9] * List.formPerm [7, 44] * List.formPerm [8, 17] *
    List.formPerm [10, 22] * List.formPerm [11, 36] * List.formPerm [12, 24] *
    List.formPerm [14, 37] * List.formPerm [15, 27] * List.formPerm [18, 32] *
    List.formPerm [19, 31] * List.formPerm [21, 40] * List.formPerm [26, 43] *
    List.formPerm [30, 39] * List.formPerm [34, 35]

@[expose] def cfF2 : List PX := [cfF2a, cfF2b, cfF2c, cfF2d]

@[expose] def cfF3a : PX := List.formPerm [1, 2] * List.formPerm [4, 5] *
    List.formPerm [7, 8] * List.formPerm [10, 11] * List.formPerm [13, 14] *
    List.formPerm [17, 18] * List.formPerm [19, 22] * List.formPerm [20, 24] *
    List.formPerm [21, 23] * List.formPerm [25, 35] * List.formPerm [26, 36] *
    List.formPerm [27, 38] * List.formPerm [28, 37] * List.formPerm [29, 42] *
    List.formPerm [30, 44] * List.formPerm [31, 43] * List.formPerm [32, 39] *
    List.formPerm [33, 41] * List.formPerm [34, 40]

@[expose] def cfF3b : PX := List.formPerm [0, 15] * List.formPerm [1, 35] *
    List.formPerm [2, 25] * List.formPerm [3, 12] * List.formPerm [4, 14] *
    List.formPerm [5, 13] * List.formPerm [7, 8] * List.formPerm [10, 11] *
    List.formPerm [17, 44] * List.formPerm [18, 30] * List.formPerm [19, 26] *
    List.formPerm [20, 24] * List.formPerm [21, 40] * List.formPerm [22, 36] *
    List.formPerm [23, 34] * List.formPerm [27, 38] * List.formPerm [28, 33] *
    List.formPerm [31, 43] * List.formPerm [32, 39] * List.formPerm [37, 41]

@[expose] def cfF3c : PX := List.formPerm [0, 15] * List.formPerm [1, 34] *
    List.formPerm [2, 40] * List.formPerm [3, 12] * List.formPerm [4, 41] *
    List.formPerm [5, 33] * List.formPerm [7, 32] * List.formPerm [8, 39] *
    List.formPerm [10, 43] * List.formPerm [11, 31] * List.formPerm [13, 28] *
    List.formPerm [14, 37] * List.formPerm [17, 30] * List.formPerm [18, 44] *
    List.formPerm [19, 36] * List.formPerm [20, 24] * List.formPerm [21, 25] *
    List.formPerm [22, 26] * List.formPerm [23, 35] * List.formPerm [27, 38]

@[expose] def cfF3d : PX := List.formPerm [0, 12] * List.formPerm [1, 33] *
    List.formPerm [2, 41] * List.formPerm [3, 15] * List.formPerm [4, 40] *
    List.formPerm [5, 34] * List.formPerm [7, 32] * List.formPerm [8, 39] *
    List.formPerm [10, 31] * List.formPerm [11, 43] * List.formPerm [13, 23] *
    List.formPerm [14, 21] * List.formPerm [17, 44] * List.formPerm [18, 30] *
    List.formPerm [20, 27] * List.formPerm [24, 38] * List.formPerm [25, 37] *
    List.formPerm [28, 35] * List.formPerm [29, 42]

@[expose] def cfF3 : List PX := [cfF3a, cfF3b, cfF3c, cfF3d]

@[expose] def cfFgens : List PX := cfF1 ++ cfF2 ++ cfF3

@[expose] def cfQF1 : RawSchreierDatum 45 :=
  certificate (by decide) (cfF1.map tab) [[4]] #v[1, 3] (by decide)

@[expose] def cfQF2 : RawSchreierDatum 45 :=
  certificate (by decide) (cfF2.map tab) [] #v[7] (by decide)

@[expose] def cfQF3 : RawSchreierDatum 45 :=
  certificate (by decide) (cfF3.map tab) [] #v[1] (by decide)

@[expose] def cfQRz : RawSchreierDatum 45 :=
  certificate (by decide) (cfFgens.map tab) [[4], [1, 2, 8]] #v[1, 3] (by decide)

@[expose] def cfEgensa : PX := List.formPerm [0, 3] * List.formPerm [1, 4] *
    List.formPerm [2, 5] * List.formPerm [7, 8] * List.formPerm [12, 15] *
    List.formPerm [13, 25] * List.formPerm [14, 35] * List.formPerm [19, 26] *
    List.formPerm [20, 27] * List.formPerm [21, 28] * List.formPerm [22, 36] *
    List.formPerm [23, 37] * List.formPerm [24, 38] * List.formPerm [32, 39] *
    List.formPerm [33, 40] * List.formPerm [34, 41]

@[expose] def cfEgensb : PX := List.formPerm [0, 27] * List.formPerm [1, 34] *
    List.formPerm [3, 20] * List.formPerm [4, 41] * List.formPerm [7, 22] *
    List.formPerm [8, 36] * List.formPerm [10, 44] * List.formPerm [11, 17] *
    List.formPerm [12, 24] * List.formPerm [14, 37] * List.formPerm [15, 38] *
    List.formPerm [18, 43] * List.formPerm [19, 39] * List.formPerm [23, 35] *
    List.formPerm [26, 32] * List.formPerm [30, 31]

@[expose] def cfEgensc : PX := List.formPerm [0, 12] * List.formPerm [1, 14] *
    List.formPerm [2, 13] * List.formPerm [3, 15] * List.formPerm [4, 35] *
    List.formPerm [5, 25] * List.formPerm [10, 11] * List.formPerm [17, 44] *
    List.formPerm [18, 30] * List.formPerm [20, 38] * List.formPerm [21, 33] *
    List.formPerm [23, 41] * List.formPerm [24, 27] * List.formPerm [28, 40] *
    List.formPerm [31, 43] * List.formPerm [34, 37]

@[expose] def cfEgensd : PX := List.formPerm [1, 23] * List.formPerm [2, 21] *
    List.formPerm [4, 37] * List.formPerm [5, 28] * List.formPerm [7, 39] *
    List.formPerm [8, 32] * List.formPerm [10, 31] * List.formPerm [11, 43] *
    List.formPerm [13, 33] * List.formPerm [14, 41] * List.formPerm [17, 18] *
    List.formPerm [19, 22] * List.formPerm [25, 40] * List.formPerm [26, 36] *
    List.formPerm [30, 44] * List.formPerm [34, 35]

@[expose] def cfEgens : List PX := [cfEgensa, cfEgensb, cfEgensc, cfEgensd]

@[expose] def cfQE : RawSchreierDatum 45 :=
  certificate (by decide) (cfEgens.map tab) [[4]] #v[0, 1] (by decide)

@[expose] def cfOzWa : PX := List.formPerm [0, 27] * List.formPerm [1, 35] *
    List.formPerm [2, 21] * List.formPerm [3, 20] * List.formPerm [4, 14] *
    List.formPerm [5, 28] * List.formPerm [7, 19] * List.formPerm [8, 26] *
    List.formPerm [10, 30] * List.formPerm [11, 18] * List.formPerm [12, 24] *
    List.formPerm [13, 33] * List.formPerm [15, 38] * List.formPerm [17, 43] *
    List.formPerm [22, 39] * List.formPerm [23, 34] * List.formPerm [25, 40] *
    List.formPerm [31, 44] * List.formPerm [32, 36] * List.formPerm [37, 41]

@[expose] def cfOzKa : PX := List.formPerm [0, 4, 22, 18, 27, 41, 7, 43] *
    List.formPerm [1, 19, 10, 24, 34, 39, 44, 12] * List.formPerm [2, 40, 28, 21] *
    List.formPerm [3, 37, 32, 30, 20, 14, 26, 31] * List.formPerm [5, 25, 13, 33] *
    List.formPerm [6, 16, 42, 9] * List.formPerm [8, 11, 38, 35, 36, 17, 15, 23]

@[expose] def cfOzWb : PX := List.formPerm [0, 15] * List.formPerm [1, 35] *
    List.formPerm [2, 25] * List.formPerm [3, 12] * List.formPerm [4, 14] *
    List.formPerm [5, 13] * List.formPerm [7, 8] * List.formPerm [10, 11] *
    List.formPerm [17, 44] * List.formPerm [18, 30] * List.formPerm [19, 26] *
    List.formPerm [20, 24] * List.formPerm [21, 40] * List.formPerm [22, 36] *
    List.formPerm [23, 34] * List.formPerm [27, 38] * List.formPerm [28, 33] *
    List.formPerm [31, 43] * List.formPerm [32, 39] * List.formPerm [37, 41]

@[expose] def cfOzKb : PX := List.formPerm [0, 31, 37, 19, 28] *
    List.formPerm [1, 7, 2, 24, 44] * List.formPerm [3, 17, 34, 39, 5] *
    List.formPerm [4, 26, 13, 12, 30] * List.formPerm [6, 42, 9, 29, 16] *
    List.formPerm [8, 40, 27, 10, 23] * List.formPerm [11, 35, 32, 33, 15] *
    List.formPerm [14, 22, 21, 38, 43] * List.formPerm [18, 41, 36, 25, 20]

@[expose] def cfOzWc : PX := List.formPerm [0, 12] * List.formPerm [1, 41] *
    List.formPerm [2, 33] * List.formPerm [3, 15] * List.formPerm [4, 34] *
    List.formPerm [5, 40] * List.formPerm [7, 39] * List.formPerm [8, 32] *
    List.formPerm [10, 43] * List.formPerm [11, 31] * List.formPerm [13, 21] *
    List.formPerm [14, 23] * List.formPerm [17, 30] * List.formPerm [18, 44] *
    List.formPerm [19, 22] * List.formPerm [20, 38] * List.formPerm [24, 27] *
    List.formPerm [25, 28] * List.formPerm [26, 36] * List.formPerm [35, 37]

@[expose] def cfOzKc : PX := List.formPerm [0, 13] * List.formPerm [1, 22] *
    List.formPerm [2, 38] * List.formPerm [3, 25] * List.formPerm [4, 36] *
    List.formPerm [5, 24] * List.formPerm [7, 23] * List.formPerm [8, 37] *
    List.formPerm [9, 42] * List.formPerm [11, 18] * List.formPerm [12, 28] *
    List.formPerm [14, 32] * List.formPerm [15, 21] * List.formPerm [16, 29] *
    List.formPerm [19, 34] * List.formPerm [20, 40] * List.formPerm [26, 41] *
    List.formPerm [27, 33] * List.formPerm [31, 44] * List.formPerm [35, 39]

@[expose] def cfOzWd : PX := List.formPerm [0, 3] * List.formPerm [1, 37] *
    List.formPerm [2, 28] * List.formPerm [4, 23] * List.formPerm [5, 21] *
    List.formPerm [7, 32] * List.formPerm [8, 39] * List.formPerm [10, 31] *
    List.formPerm [11, 43] * List.formPerm [12, 15] * List.formPerm [13, 40] *
    List.formPerm [14, 34] * List.formPerm [17, 18] * List.formPerm [19, 36] *
    List.formPerm [20, 27] * List.formPerm [22, 26] * List.formPerm [24, 38] *
    List.formPerm [25, 33] * List.formPerm [30, 44] * List.formPerm [35, 41]

@[expose] def cfOzKd : PX := List.formPerm [0, 34, 26] *
    List.formPerm [1, 19, 27, 41, 32, 3] * List.formPerm [2, 10, 28, 43, 33, 17] *
    List.formPerm [4, 39, 20] * List.formPerm [5, 44, 21, 18, 40, 11] *
    List.formPerm [6, 29] * List.formPerm [7, 12, 35] *
    List.formPerm [8, 24, 14, 22, 15, 23] * List.formPerm [9, 16, 42] *
    List.formPerm [13, 31] * List.formPerm [25, 30] * List.formPerm [36, 38, 37]

@[expose] def cfOzWe : PX := List.formPerm [0, 20] * List.formPerm [1, 14] *
    List.formPerm [2, 28] * List.formPerm [3, 27] * List.formPerm [4, 35] *
    List.formPerm [5, 21] * List.formPerm [7, 26] * List.formPerm [8, 19] *
    List.formPerm [10, 30] * List.formPerm [11, 18] * List.formPerm [12, 38] *
    List.formPerm [13, 40] * List.formPerm [15, 24] * List.formPerm [17, 43] *
    List.formPerm [22, 32] * List.formPerm [23, 41] * List.formPerm [25, 33] *
    List.formPerm [31, 44] * List.formPerm [34, 37] * List.formPerm [36, 39]

@[expose] def cfOzKe : PX := List.formPerm [0, 3] * List.formPerm [2, 8] *
    List.formPerm [5, 7] * List.formPerm [9, 29] * List.formPerm [10, 18] *
    List.formPerm [11, 43] * List.formPerm [12, 20] * List.formPerm [13, 36] *
    List.formPerm [14, 34] * List.formPerm [15, 27] * List.formPerm [17, 31] *
    List.formPerm [19, 40] * List.formPerm [21, 32] * List.formPerm [22, 25] *
    List.formPerm [24, 38] * List.formPerm [26, 33] * List.formPerm [28, 39] *
    List.formPerm [30, 44] * List.formPerm [35, 41]

@[expose] def cfOzWf : PX := List.formPerm [0, 24] * List.formPerm [1, 37] *
    List.formPerm [2, 13] * List.formPerm [3, 38] * List.formPerm [4, 23] *
    List.formPerm [5, 25] * List.formPerm [7, 22] * List.formPerm [8, 36] *
    List.formPerm [10, 17] * List.formPerm [11, 44] * List.formPerm [12, 27] *
    List.formPerm [14, 34] * List.formPerm [15, 20] * List.formPerm [18, 31] *
    List.formPerm [19, 39] * List.formPerm [21, 33] * List.formPerm [26, 32] *
    List.formPerm [28, 40] * List.formPerm [30, 43] * List.formPerm [35, 41]

@[expose] def cfOzKf : PX := List.formPerm [0, 3, 15, 38] *
    List.formPerm [1, 43, 26, 33, 23, 11, 36, 13] *
    List.formPerm [2, 34, 44, 19, 21, 35, 30, 22] *
    List.formPerm [4, 31, 32, 5, 37, 10, 8, 28] * List.formPerm [6, 9, 29, 42] *
    List.formPerm [7, 40, 41, 17, 39, 25, 14, 18] * List.formPerm [12, 20, 27, 24]

@[expose] def cfOzWg : PX := List.formPerm [0, 38] * List.formPerm [1, 23] *
    List.formPerm [2, 25] * List.formPerm [3, 24] * List.formPerm [4, 37] *
    List.formPerm [5, 13] * List.formPerm [7, 36] * List.formPerm [8, 22] *
    List.formPerm [10, 17] * List.formPerm [11, 44] * List.formPerm [12, 20] *
    List.formPerm [14, 41] * List.formPerm [15, 27] * List.formPerm [18, 31] *
    List.formPerm [19, 32] * List.formPerm [21, 40] * List.formPerm [26, 39] *
    List.formPerm [28, 33] * List.formPerm [30, 43] * List.formPerm [34, 35]

@[expose] def cfOzKg : PX := List.formPerm [0, 4, 40, 17] *
    List.formPerm [1, 25, 31, 27] * List.formPerm [2, 11, 3, 37] *
    List.formPerm [5, 43, 24, 14] * List.formPerm [6, 16, 42, 29] *
    List.formPerm [7, 19] * List.formPerm [8, 22, 26, 39] *
    List.formPerm [10, 15, 34, 13] * List.formPerm [12, 35, 28, 44] *
    List.formPerm [18, 38, 41, 33] * List.formPerm [20, 23, 21, 30]

@[expose] def cfOzWh : PX := List.formPerm [0, 20] * List.formPerm [1, 41] *
    List.formPerm [2, 5] * List.formPerm [3, 27] * List.formPerm [4, 34] *
    List.formPerm [7, 36] * List.formPerm [8, 22] * List.formPerm [10, 44] *
    List.formPerm [11, 17] * List.formPerm [12, 38] * List.formPerm [13, 25] *
    List.formPerm [14, 23] * List.formPerm [15, 24] * List.formPerm [18, 43] *
    List.formPerm [19, 32] * List.formPerm [21, 28] * List.formPerm [26, 39] *
    List.formPerm [30, 31] * List.formPerm [33, 40] * List.formPerm [35, 37]

@[expose] def cfOzKh : PX := List.formPerm [0, 17, 2, 14, 7] *
    List.formPerm [1, 39, 3, 11, 40] * List.formPerm [4, 19, 24, 10, 25] *
    List.formPerm [5, 37, 26, 12, 18] * List.formPerm [6, 29, 42, 9, 16] *
    List.formPerm [8, 27, 31, 13, 41] * List.formPerm [15, 43, 33, 34, 36] *
    List.formPerm [20, 30, 28, 23, 32] * List.formPerm [21, 35, 22, 38, 44]

@[expose] def cfOzWi : PX := List.formPerm [0, 15] * List.formPerm [1, 34] *
    List.formPerm [2, 40] * List.formPerm [3, 12] * List.formPerm [4, 41] *
    List.formPerm [5, 33] * List.formPerm [7, 32] * List.formPerm [8, 39] *
    List.formPerm [10, 43] * List.formPerm [11, 31] * List.formPerm [13, 28] *
    List.formPerm [14, 37] * List.formPerm [17, 30] * List.formPerm [18, 44] *
    List.formPerm [19, 36] * List.formPerm [20, 24] * List.formPerm [21, 25] *
    List.formPerm [22, 26] * List.formPerm [23, 35] * List.formPerm [27, 38]

@[expose] def cfOzKi : PX := List.formPerm [0, 20, 15, 24] *
    List.formPerm [1, 5, 34, 33] * List.formPerm [2, 41, 40, 4] *
    List.formPerm [3, 27, 12, 38] * List.formPerm [7, 22, 32, 26] *
    List.formPerm [8, 36, 39, 19] * List.formPerm [10, 17, 43, 30] *
    List.formPerm [11, 44, 31, 18] * List.formPerm [13, 23, 28, 35] *
    List.formPerm [14, 25, 37, 21] * List.formPerm [29, 42]

@[expose] def cfOzWj : PX := List.formPerm [0, 24] * List.formPerm [1, 4] *
    List.formPerm [2, 33] * List.formPerm [3, 38] * List.formPerm [5, 40] *
    List.formPerm [7, 19] * List.formPerm [8, 26] * List.formPerm [10, 18] *
    List.formPerm [11, 30] * List.formPerm [12, 27] * List.formPerm [13, 21] *
    List.formPerm [14, 35] * List.formPerm [15, 20] * List.formPerm [17, 31] *
    List.formPerm [22, 39] * List.formPerm [23, 37] * List.formPerm [25, 28] *
    List.formPerm [32, 36] * List.formPerm [34, 41] * List.formPerm [43, 44]

@[expose] def cfOzKj : PX := List.formPerm [0, 8, 38, 19] * List.formPerm [1, 37] *
    List.formPerm [2, 30, 40, 11] * List.formPerm [3, 36, 24, 39] *
    List.formPerm [4, 14] * List.formPerm [5, 31, 33, 17] * List.formPerm [6, 29] *
    List.formPerm [7, 15, 26, 27] * List.formPerm [9, 16] *
    List.formPerm [10, 21, 18, 25] * List.formPerm [12, 32, 20, 22] *
    List.formPerm [13, 44, 28, 43] * List.formPerm [23, 34] * List.formPerm [35, 41]

@[expose] def cfOz : List (PX × PX) := [(cfOzWa, cfOzKa), (cfOzWb, cfOzKb), (cfOzWc, cfOzKc),
    (cfOzWd, cfOzKd), (cfOzWe, cfOzKe), (cfOzWf, cfOzKf), (cfOzWg, cfOzKg), (cfOzWh, cfOzKh),
    (cfOzWi, cfOzKi), (cfOzWj, cfOzKj)]

@[expose] def cfOztWa : PX := List.formPerm [0, 3] * List.formPerm [1, 4] *
    List.formPerm [2, 5] * List.formPerm [7, 8] * List.formPerm [12, 15] *
    List.formPerm [13, 25] * List.formPerm [14, 35] * List.formPerm [19, 26] *
    List.formPerm [20, 27] * List.formPerm [21, 28] * List.formPerm [22, 36] *
    List.formPerm [23, 37] * List.formPerm [24, 38] * List.formPerm [32, 39] *
    List.formPerm [33, 40] * List.formPerm [34, 41]

@[expose] def cfOztKa : PX := List.formPerm [0, 4, 22, 18, 27, 41, 7, 43] *
    List.formPerm [1, 19, 10, 24, 34, 39, 44, 12] * List.formPerm [2, 40, 28, 21] *
    List.formPerm [3, 37, 32, 30, 20, 14, 26, 31] * List.formPerm [5, 25, 13, 33] *
    List.formPerm [6, 16, 42, 9] * List.formPerm [8, 11, 38, 35, 36, 17, 15, 23]

@[expose] def cfOztWb : PX := List.formPerm [0, 27] * List.formPerm [1, 34] *
    List.formPerm [3, 20] * List.formPerm [4, 41] * List.formPerm [7, 22] *
    List.formPerm [8, 36] * List.formPerm [10, 44] * List.formPerm [11, 17] *
    List.formPerm [12, 24] * List.formPerm [14, 37] * List.formPerm [15, 38] *
    List.formPerm [18, 43] * List.formPerm [19, 39] * List.formPerm [23, 35] *
    List.formPerm [26, 32] * List.formPerm [30, 31]

@[expose] def cfOztKb : PX := List.formPerm [0, 31, 37, 19, 28] *
    List.formPerm [1, 7, 2, 24, 44] * List.formPerm [3, 17, 34, 39, 5] *
    List.formPerm [4, 26, 13, 12, 30] * List.formPerm [6, 42, 9, 29, 16] *
    List.formPerm [8, 40, 27, 10, 23] * List.formPerm [11, 35, 32, 33, 15] *
    List.formPerm [14, 22, 21, 38, 43] * List.formPerm [18, 41, 36, 25, 20]

@[expose] def cfOztWc : PX := List.formPerm [0, 12] * List.formPerm [1, 14] *
    List.formPerm [2, 13] * List.formPerm [3, 15] * List.formPerm [4, 35] *
    List.formPerm [5, 25] * List.formPerm [10, 11] * List.formPerm [17, 44] *
    List.formPerm [18, 30] * List.formPerm [20, 38] * List.formPerm [21, 33] *
    List.formPerm [23, 41] * List.formPerm [24, 27] * List.formPerm [28, 40] *
    List.formPerm [31, 43] * List.formPerm [34, 37]

@[expose] def cfOztKc : PX := List.formPerm [0, 34, 26] *
    List.formPerm [1, 19, 27, 41, 32, 3] * List.formPerm [2, 10, 28, 43, 33, 17] *
    List.formPerm [4, 39, 20] * List.formPerm [5, 44, 21, 18, 40, 11] *
    List.formPerm [6, 29] * List.formPerm [7, 12, 35] *
    List.formPerm [8, 24, 14, 22, 15, 23] * List.formPerm [9, 16, 42] *
    List.formPerm [13, 31] * List.formPerm [25, 30] * List.formPerm [36, 38, 37]

@[expose] def cfOztWd : PX := List.formPerm [1, 23] * List.formPerm [2, 21] *
    List.formPerm [4, 37] * List.formPerm [5, 28] * List.formPerm [7, 39] *
    List.formPerm [8, 32] * List.formPerm [10, 31] * List.formPerm [11, 43] *
    List.formPerm [13, 33] * List.formPerm [14, 41] * List.formPerm [17, 18] *
    List.formPerm [19, 22] * List.formPerm [25, 40] * List.formPerm [26, 36] *
    List.formPerm [30, 44] * List.formPerm [34, 35]

@[expose] def cfOztKd : PX := List.formPerm [0, 3] * List.formPerm [2, 8] *
    List.formPerm [5, 7] * List.formPerm [9, 29] * List.formPerm [10, 18] *
    List.formPerm [11, 43] * List.formPerm [12, 20] * List.formPerm [13, 36] *
    List.formPerm [14, 34] * List.formPerm [15, 27] * List.formPerm [17, 31] *
    List.formPerm [19, 40] * List.formPerm [21, 32] * List.formPerm [22, 25] *
    List.formPerm [24, 38] * List.formPerm [26, 33] * List.formPerm [28, 39] *
    List.formPerm [30, 44] * List.formPerm [35, 41]

@[expose] def cfOztWe : PX := List.formPerm [0, 38] * List.formPerm [2, 40] *
    List.formPerm [3, 24] * List.formPerm [5, 33] * List.formPerm [7, 26] *
    List.formPerm [8, 19] * List.formPerm [10, 18] * List.formPerm [11, 30] *
    List.formPerm [12, 20] * List.formPerm [13, 28] * List.formPerm [15, 27] *
    List.formPerm [17, 31] * List.formPerm [21, 25] * List.formPerm [22, 32] *
    List.formPerm [36, 39] * List.formPerm [43, 44]

@[expose] def cfOztKe : PX := List.formPerm [0, 14, 15, 34, 24, 23] *
    List.formPerm [1, 38, 41, 27, 35, 3] * List.formPerm [2, 30, 32] *
    List.formPerm [4, 20] * List.formPerm [5, 18, 26] * List.formPerm [6, 9, 29] *
    List.formPerm [7, 28, 10, 36, 33, 17] * List.formPerm [8, 40, 44, 22, 21, 11] *
    List.formPerm [12, 37] * List.formPerm [13, 31, 39] * List.formPerm [16, 42] *
    List.formPerm [19, 25, 43]

@[expose] def cfOzt : List (PX × PX) := [(cfOztWa, cfOztKa), (cfOztWb, cfOztKb), (cfOztWc,
    cfOztKc), (cfOztWd, cfOztKd), (cfOztWe, cfOztKe)]

@[expose] def cfCls1W : List (List ℤ) :=
    [[], [1], [2], [2, 3], [2, 1], [1, 2], [2, 2], [1, 2, 3], [2, 3, 2], [1, 2, 2], [2, 2, 2], [1,
    2, 3, 2], [2, 3, 2, 3], [1, 2, 2, 3], [2, 3, 2, 2], [2, 2, 2, 2], [2, 2, 2, 3], [2, 3, 2, 1],
    [1, 2, 2, 2], [2, 1, 2, 2, 3], [2, 3, 2, 2, 3], [2, 3, 2, 1, 3], [1, 2, 3, 2, 2], [2, 2, 2, 2,
    1], [2, 1, 2, 2, 1], [2, 3, 2, 1, 2], [2, 3, 2, 2, 2], [1, 2, 2, 2, 2], [1, 2, 2, 2, 2, 3], [2,
    1, 2, 2, 2, 3], [2, 1, 2, 2, 2, 1], [1, 2, 3, 2, 2, 2], [2, 1, 2, 2, 3, 2], [2, 3, 2, 1, 3, 2],
    [1, 2, 2, 2, 2, 1], [2, 1, 2, 2, 2, 3, 2]]

@[expose] def cfCls2W : List (List ℤ) :=
    [[], [1], [2], [2, 3], [2, 1], [1, 2], [2, 2], [1, 2, 3], [2, 3, 2], [1, 2, 2], [2, 2, 2], [1,
    2, 3, 2], [2, 3, 2, 3], [1, 2, 2, 3], [2, 3, 2, 2], [2, 2, 2, 2], [2, 2, 2, 3], [2, 2, 2, 1],
    [2, 3, 2, 1], [1, 2, 2, 2], [2, 1, 2, 2, 3], [2, 3, 2, 2, 3], [2, 2, 2, 1, 2], [1, 2, 2, 2, 1],
    [2, 3, 2, 1, 3], [1, 2, 3, 2, 2], [2, 2, 2, 2, 1], [2, 1, 2, 2, 1], [2, 2, 2, 1, 3], [2, 3, 2,
    2, 1], [2, 3, 2, 1, 2], [2, 3, 2, 2, 2], [2, 2, 2, 3, 2], [2, 2, 2, 2, 3], [1, 2, 2, 2, 2], [2,
    3, 2, 3, 2], [1, 2, 2, 2, 3], [1, 2, 2, 2, 2, 3], [2, 1, 2, 2, 2, 3], [1, 2, 3, 2, 1, 2], [1,
    2, 3, 2, 1, 3], [1, 2, 2, 2, 1, 3], [2, 2, 2, 3, 2, 1], [2, 1, 2, 2, 2, 1], [2, 2, 2, 3, 2, 2],
    [2, 3, 2, 3, 2, 1], [2, 2, 2, 2, 3, 2], [2, 3, 2, 3, 2, 2], [1, 2, 3, 2, 2, 2], [2, 3, 2, 3, 2,
    3], [2, 2, 2, 1, 2, 2], [2, 1, 2, 2, 3, 2], [2, 3, 2, 2, 1, 2], [2, 3, 2, 1, 2, 2], [2, 2, 2,
    1, 3, 2], [2, 3, 2, 1, 3, 2], [2, 2, 2, 3, 2, 3], [1, 2, 2, 2, 1, 2], [2, 3, 2, 2, 3, 2], [1,
    2, 2, 2, 2, 1], [1, 2, 2, 2, 3, 2], [2, 2, 2, 2, 1, 2], [2, 2, 2, 1, 3, 2, 2], [2, 1, 2, 2, 3,
    2, 3], [2, 1, 2, 2, 2, 3, 2], [1, 2, 2, 2, 3, 2, 3], [2, 3, 2, 1, 3, 2, 2], [2, 3, 2, 2, 3, 2,
    2], [2, 2, 2, 1, 3, 2, 3], [2, 2, 2, 1, 3, 2, 1], [1, 2, 2, 2, 2, 1, 2], [2, 3, 2, 2, 1, 2, 2],
    [2, 3, 2, 2, 3, 2, 3], [2, 2, 2, 3, 2, 2, 2], [2, 3, 2, 2, 1, 2, 1], [2, 2, 2, 3, 2, 1, 2], [1,
    2, 2, 2, 1, 2, 2], [1, 2, 2, 2, 3, 2, 1], [2, 2, 2, 1, 2, 2, 1], [2, 2, 2, 3, 2, 2, 3], [2, 1,
    2, 2, 3, 2, 1], [2, 3, 2, 3, 2, 2, 3], [2, 2, 2, 2, 1, 2, 1], [2, 3, 2, 1, 2, 2, 1], [2, 1, 2,
    2, 3, 2, 2], [2, 1, 2, 2, 1, 2, 2], [2, 3, 2, 3, 2, 2, 2], [2, 1, 2, 2, 1, 3, 2], [2, 2, 2, 3,
    2, 1, 3], [2, 2, 2, 2, 1, 2, 3], [1, 2, 3, 2, 2, 1, 2], [2, 2, 2, 3, 2, 3, 2], [2, 3, 2, 3, 2,
    1, 3], [2, 2, 2, 2, 3, 2, 2], [2, 2, 2, 2, 3, 2, 1], [2, 3, 2, 2, 3, 2, 1], [2, 2, 2, 1, 2, 2,
    3], [2, 2, 2, 2, 1, 2, 2], [2, 2, 2, 1, 2, 2, 2], [1, 2, 2, 2, 3, 2, 2], [2, 3, 2, 1, 2, 2, 3],
    [2, 3, 2, 1, 3, 2, 1], [2, 3, 2, 1, 2, 2, 2], [2, 3, 2, 3, 2, 3, 2], [2, 3, 2, 3, 2, 1, 2], [1,
    2, 2, 2, 2, 3, 2, 2], [2, 2, 2, 1, 2, 2, 1, 2], [2, 2, 2, 2, 3, 2, 3, 2], [2, 2, 2, 1, 2, 2, 2,
    3], [2, 3, 2, 3, 2, 1, 3, 2], [2, 3, 2, 1, 3, 2, 2, 2], [2, 3, 2, 2, 3, 2, 3, 2], [2, 3, 2, 1,
    3, 2, 3, 2], [1, 2, 3, 2, 1, 2, 2, 3], [2, 2, 2, 2, 3, 2, 2, 3], [2, 2, 2, 3, 2, 1, 2, 1], [2,
    3, 2, 3, 2, 1, 2, 3], [2, 2, 2, 2, 1, 2, 2, 2], [2, 3, 2, 1, 2, 2, 1, 3], [1, 2, 3, 2, 1, 3, 2,
    1], [2, 3, 2, 1, 2, 2, 2, 2], [2, 2, 2, 2, 3, 2, 2, 2], [2, 1, 2, 2, 2, 3, 2, 1], [2, 3, 2, 3,
    2, 2, 2, 3], [1, 2, 3, 2, 3, 2, 3, 2], [2, 2, 2, 3, 2, 2, 3, 2], [1, 2, 2, 2, 3, 2, 2, 3], [2,
    3, 2, 3, 2, 3, 2, 2], [2, 1, 2, 2, 3, 2, 2, 3], [2, 2, 2, 1, 2, 2, 2, 2], [2, 3, 2, 3, 2, 1, 2,
    2], [2, 2, 2, 3, 2, 3, 2, 2], [1, 2, 2, 2, 1, 3, 2, 1], [2, 2, 2, 3, 2, 1, 3, 2], [2, 3, 2, 1,
    2, 2, 2, 1], [2, 2, 2, 1, 2, 2, 3, 2], [2, 1, 2, 2, 2, 1, 2, 2], [1, 2, 2, 2, 1, 2, 2, 2], [2,
    2, 2, 3, 2, 3, 2, 3], [1, 2, 2, 2, 3, 2, 2, 2], [2, 2, 2, 2, 1, 2, 2, 3], [2, 3, 2, 1, 2, 2, 2,
    3], [1, 2, 3, 2, 2, 1, 2, 1], [2, 2, 2, 2, 1, 2, 3, 2], [2, 3, 2, 3, 2, 2, 2, 1], [2, 3, 2, 1,
    2, 2, 3, 2], [2, 3, 2, 2, 1, 2, 2, 3], [2, 1, 2, 2, 3, 2, 2, 2], [2, 3, 2, 2, 1, 2, 2, 1], [2,
    3, 2, 3, 2, 3, 2, 3], [2, 3, 2, 2, 1, 2, 1, 2], [1, 2, 2, 2, 2, 3, 2, 1], [2, 2, 2, 2, 1, 2, 1,
    2], [2, 3, 2, 3, 2, 1, 2, 1], [2, 1, 2, 2, 1, 2, 2, 2], [2, 3, 2, 3, 2, 2, 3, 2], [1, 2, 3, 2,
    3, 2, 1, 3], [2, 3, 2, 2, 1, 3, 2, 1], [2, 3, 2, 2, 3, 2, 2, 2], [2, 2, 2, 3, 2, 1, 2, 2], [2,
    1, 2, 2, 3, 2, 1, 2], [2, 2, 2, 1, 3, 2, 2, 2], [2, 3, 2, 1, 2, 2, 1, 2], [1, 2, 2, 2, 3, 2, 1,
    2], [1, 2, 2, 2, 1, 2, 2, 1], [2, 2, 2, 1, 3, 2, 2, 1], [2, 3, 2, 1, 3, 2, 2, 1], [1, 2, 2, 2,
    2, 1, 2, 2], [1, 2, 2, 2, 3, 2, 1, 3], [2, 2, 2, 3, 2, 2, 2, 1], [2, 2, 2, 1, 2, 2, 1, 3], [1,
    2, 2, 2, 3, 2, 3, 2], [2, 2, 2, 1, 2, 2, 2, 1], [2, 2, 2, 2, 1, 2, 2, 1], [2, 2, 2, 3, 2, 2, 2,
    3], [1, 2, 2, 2, 1, 2, 2, 3], [2, 2, 2, 3, 2, 1, 2, 3], [2, 3, 2, 2, 3, 2, 2, 3], [2, 1, 2, 2,
    2, 3, 2, 2, 2], [2, 1, 2, 2, 1, 2, 2, 3, 2], [2, 3, 2, 3, 2, 1, 2, 2, 2], [2, 1, 2, 2, 2, 3, 2,
    2, 3], [2, 2, 2, 2, 3, 2, 2, 2, 2], [1, 2, 2, 2, 1, 2, 2, 3, 2], [1, 2, 2, 2, 3, 2, 2, 2, 3],
    [2, 3, 2, 1, 2, 3, 2, 2, 1], [1, 2, 2, 2, 2, 3, 2, 2, 3], [2, 3, 2, 1, 2, 3, 2, 2, 2], [1, 2,
    2, 2, 1, 2, 2, 1, 2], [2, 3, 2, 1, 2, 2, 2, 1, 2], [2, 1, 2, 2, 3, 2, 1, 3, 2], [1, 2, 3, 2, 3,
    2, 2, 2, 3], [2, 2, 2, 1, 2, 2, 1, 2, 2], [2, 2, 2, 2, 1, 2, 3, 2, 1], [2, 3, 2, 2, 1, 2, 3, 2,
    3], [1, 2, 3, 2, 1, 2, 2, 2, 1], [2, 3, 2, 2, 1, 3, 2, 1, 2], [2, 2, 2, 2, 1, 2, 1, 2, 2], [2,
    3, 2, 1, 2, 2, 1, 2, 3], [2, 2, 2, 2, 3, 2, 2, 3, 2], [2, 2, 2, 1, 2, 2, 1, 2, 3], [2, 3, 2, 2,
    1, 2, 2, 1, 2], [1, 2, 2, 2, 1, 2, 2, 2, 2], [2, 2, 2, 3, 2, 2, 2, 3, 2], [1, 2, 3, 2, 3, 2, 3,
    2, 3], [1, 2, 2, 2, 1, 3, 2, 2, 2], [2, 2, 2, 2, 1, 2, 3, 2, 3], [2, 1, 2, 2, 1, 3, 2, 2, 2],
    [2, 1, 2, 2, 3, 2, 2, 3, 2], [2, 2, 2, 1, 2, 2, 3, 2, 2], [2, 2, 2, 1, 3, 2, 2, 2, 3], [2, 2,
    2, 3, 2, 1, 3, 2, 1], [1, 2, 3, 2, 3, 2, 1, 2, 2], [1, 2, 2, 2, 3, 2, 3, 2, 2], [2, 3, 2, 3, 2,
    1, 3, 2, 3], [1, 2, 2, 2, 3, 2, 1, 2, 2], [2, 1, 2, 2, 3, 2, 2, 2, 1], [1, 2, 3, 2, 1, 3, 2, 2,
    1], [2, 3, 2, 3, 2, 3, 2, 2, 3], [2, 3, 2, 1, 2, 3, 2, 2, 3], [2, 3, 2, 1, 3, 2, 2, 2, 3], [1,
    2, 2, 2, 1, 3, 2, 2, 1], [2, 3, 2, 3, 2, 2, 2, 3, 2], [1, 2, 3, 2, 1, 2, 2, 2, 2], [2, 3, 2, 3,
    2, 1, 2, 1, 3], [2, 3, 2, 3, 2, 2, 3, 2, 2], [1, 2, 2, 2, 1, 2, 2, 1, 3], [1, 2, 2, 2, 3, 2, 2,
    2, 1], [2, 2, 2, 1, 2, 2, 2, 2, 3], [2, 1, 2, 2, 1, 2, 2, 1, 3], [2, 3, 2, 1, 2, 2, 3, 2, 1],
    [2, 3, 2, 1, 2, 2, 2, 2, 1], [2, 3, 2, 2, 3, 2, 2, 2, 2], [2, 3, 2, 3, 2, 3, 2, 2, 2], [2, 2,
    2, 3, 2, 1, 2, 2, 2], [1, 2, 2, 2, 1, 2, 2, 2, 1], [2, 2, 2, 2, 1, 2, 3, 2, 2], [2, 2, 2, 2, 1,
    2, 2, 2, 1], [2, 2, 2, 3, 2, 3, 2, 2, 2], [2, 2, 2, 1, 2, 2, 2, 1, 2], [2, 3, 2, 3, 2, 1, 3, 2,
    2], [2, 2, 2, 2, 1, 2, 1, 2, 3], [2, 3, 2, 2, 1, 2, 3, 2, 2], [2, 3, 2, 1, 3, 2, 2, 2, 2], [2,
    2, 2, 3, 2, 1, 3, 2, 2], [1, 2, 3, 2, 3, 2, 1, 2, 1], [2, 2, 2, 2, 1, 2, 2, 1, 3], [2, 3, 2, 3,
    2, 1, 2, 1, 2], [2, 3, 2, 3, 2, 3, 2, 2, 1], [2, 3, 2, 1, 2, 2, 1, 3, 2], [1, 2, 2, 2, 3, 2, 1,
    2, 3], [2, 3, 2, 1, 3, 2, 2, 1, 2], [2, 2, 2, 3, 2, 1, 3, 2, 3], [2, 1, 2, 2, 3, 2, 1, 2, 3],
    [2, 3, 2, 1, 2, 2, 1, 2, 1], [1, 2, 3, 2, 3, 2, 3, 2, 2], [2, 3, 2, 1, 2, 2, 2, 1, 3], [2, 2,
    2, 1, 2, 2, 2, 1, 3], [2, 2, 2, 1, 2, 2, 3, 2, 3], [2, 2, 2, 1, 3, 2, 2, 2, 1], [2, 2, 2, 3, 2,
    1, 2, 1, 3], [2, 2, 2, 3, 2, 2, 3, 2, 2], [1, 2, 2, 2, 3, 2, 1, 3, 2], [2, 2, 2, 1, 2, 2, 1, 3,
    2], [2, 3, 2, 3, 2, 1, 3, 2, 1], [2, 3, 2, 1, 2, 2, 2, 2, 3], [2, 3, 2, 1, 3, 2, 2, 2, 1], [2,
    3, 2, 1, 2, 2, 3, 2, 2], [2, 2, 2, 3, 2, 3, 2, 3, 2], [2, 3, 2, 3, 2, 3, 2, 3, 2], [2, 3, 2, 3,
    2, 1, 2, 3, 2], [2, 2, 2, 2, 1, 2, 2, 1, 2], [1, 2, 2, 2, 2, 3, 2, 2, 2], [2, 2, 2, 3, 2, 3, 2,
    2, 1], [2, 2, 2, 3, 2, 1, 2, 1, 2], [1, 2, 2, 2, 2, 1, 2, 2, 3], [2, 2, 2, 3, 2, 3, 2, 2, 3],
    [1, 2, 2, 2, 2, 1, 2, 2, 1], [1, 2, 2, 2, 3, 2, 2, 3, 2], [2, 3, 2, 2, 1, 2, 2, 1, 3], [2, 2,
    2, 1, 2, 2, 3, 2, 1], [1, 2, 2, 2, 3, 2, 3, 2, 3], [2, 2, 2, 1, 3, 2, 2, 2, 2], [2, 3, 2, 1, 2,
    2, 3, 2, 3], [2, 2, 2, 1, 3, 2, 2, 1, 2], [2, 2, 2, 3, 2, 1, 2, 3, 2], [2, 2, 2, 1, 2, 2, 2, 2,
    1], [2, 2, 2, 1, 2, 2, 1, 2, 1], [2, 1, 2, 2, 3, 2, 1, 2, 3, 2], [2, 1, 2, 2, 3, 2, 1, 2, 2,
    2], [2, 3, 2, 1, 2, 2, 1, 2, 1, 3], [2, 3, 2, 2, 1, 3, 2, 2, 2, 1], [1, 2, 3, 2, 3, 2, 3, 2, 2,
    3], [2, 3, 2, 2, 1, 2, 2, 1, 2, 2], [2, 1, 2, 2, 3, 2, 2, 3, 2, 2], [2, 3, 2, 3, 2, 2, 2, 1, 3,
    2], [1, 2, 3, 2, 1, 3, 2, 2, 2, 3], [2, 1, 2, 2, 2, 1, 2, 3, 2, 3], [2, 2, 2, 3, 2, 2, 3, 2, 2,
    3], [2, 2, 2, 1, 2, 2, 2, 2, 3, 2], [2, 3, 2, 2, 1, 2, 3, 2, 2, 1], [2, 1, 2, 2, 1, 3, 2, 2, 2,
    1], [2, 3, 2, 3, 2, 1, 2, 1, 2, 2], [2, 2, 2, 2, 3, 2, 3, 2, 1, 2], [2, 3, 2, 3, 2, 2, 2, 3, 2,
    3], [2, 1, 2, 2, 1, 2, 2, 1, 2, 3], [2, 2, 2, 3, 2, 3, 2, 3, 2, 2], [1, 2, 3, 2, 1, 2, 2, 2, 1,
    2], [2, 3, 2, 3, 2, 1, 3, 2, 2, 2], [1, 2, 2, 2, 1, 2, 2, 1, 2, 1], [2, 3, 2, 3, 2, 3, 2, 2, 1,
    2], [2, 2, 2, 2, 1, 2, 2, 1, 2, 1], [2, 3, 2, 2, 3, 2, 3, 2, 2, 2], [1, 2, 2, 2, 3, 2, 1, 3, 2,
    1], [2, 3, 2, 3, 2, 1, 2, 3, 2, 2], [2, 3, 2, 2, 1, 2, 2, 1, 2, 3], [2, 2, 2, 3, 2, 3, 2, 2, 1,
    2], [2, 2, 2, 3, 2, 2, 2, 3, 2, 1], [2, 3, 2, 2, 1, 2, 3, 2, 2, 2], [2, 2, 2, 1, 3, 2, 2, 1, 2,
    3], [2, 3, 2, 1, 3, 2, 2, 2, 1, 3], [1, 2, 3, 2, 1, 2, 2, 3, 2, 1], [1, 2, 2, 2, 3, 2, 1, 2, 1,
    2], [2, 3, 2, 2, 1, 3, 2, 3, 2, 3], [2, 3, 2, 2, 1, 3, 2, 1, 2, 1], [2, 2, 2, 1, 2, 2, 2, 1, 2,
    3], [2, 2, 2, 3, 2, 3, 2, 2, 1, 3], [2, 2, 2, 3, 2, 3, 2, 2, 3, 2], [2, 3, 2, 1, 3, 2, 2, 1, 2,
    2], [2, 2, 2, 3, 2, 2, 3, 2, 2, 1], [2, 1, 2, 2, 2, 1, 2, 2, 1, 2], [2, 3, 2, 2, 1, 2, 3, 2, 2,
    3], [2, 3, 2, 3, 2, 3, 2, 2, 2, 1], [2, 3, 2, 2, 3, 2, 3, 2, 2, 3], [2, 3, 2, 3, 2, 1, 3, 2, 1,
    3], [2, 2, 2, 1, 2, 2, 1, 3, 2, 2], [2, 3, 2, 1, 2, 2, 1, 2, 2, 1], [1, 2, 2, 2, 2, 1, 2, 2, 1,
    2], [2, 3, 2, 1, 2, 2, 3, 2, 1, 2], [1, 2, 3, 2, 2, 1, 2, 2, 1, 3], [2, 3, 2, 1, 2, 2, 3, 2, 1,
    3], [2, 3, 2, 3, 2, 1, 2, 1, 2, 1], [2, 1, 2, 2, 3, 2, 3, 2, 3, 2], [2, 2, 2, 2, 1, 2, 1, 2, 2,
    2], [2, 2, 2, 2, 3, 2, 2, 2, 2, 3], [2, 2, 2, 3, 2, 3, 2, 2, 2, 1], [2, 2, 2, 3, 2, 3, 2, 2, 2,
    2], [2, 3, 2, 1, 2, 2, 1, 3, 2, 3], [2, 2, 2, 2, 1, 2, 3, 2, 2, 3], [2, 1, 2, 2, 3, 2, 1, 3, 2,
    2], [2, 3, 2, 1, 2, 3, 2, 2, 2, 1], [1, 2, 2, 2, 1, 2, 2, 3, 2, 1], [1, 2, 2, 2, 1, 2, 2, 3, 2,
    2], [1, 2, 2, 2, 3, 2, 1, 2, 1, 3], [2, 3, 2, 2, 1, 3, 2, 1, 3, 2], [1, 2, 2, 2, 1, 2, 2, 1, 3,
    2], [2, 1, 2, 2, 3, 2, 3, 2, 2, 2], [2, 3, 2, 2, 3, 2, 2, 2, 2, 1], [1, 2, 3, 2, 3, 2, 1, 2, 1,
    3], [2, 3, 2, 3, 2, 1, 2, 2, 2, 3], [2, 2, 2, 3, 2, 1, 3, 2, 2, 3], [2, 2, 2, 3, 2, 1, 3, 2, 2,
    2], [1, 2, 2, 2, 3, 2, 1, 2, 2, 2], [1, 2, 2, 2, 1, 3, 2, 2, 2, 1], [1, 2, 2, 2, 3, 2, 2, 3, 2,
    2], [2, 2, 2, 2, 1, 2, 2, 1, 2, 2], [1, 2, 3, 2, 2, 3, 2, 2, 2, 2], [1, 2, 2, 2, 3, 2, 1, 3, 2,
    2], [2, 3, 2, 1, 2, 2, 1, 2, 1, 2], [2, 1, 2, 2, 1, 3, 2, 2, 2, 2], [1, 2, 2, 2, 1, 2, 2, 1, 2,
    3], [2, 1, 2, 2, 3, 2, 2, 2, 3, 2], [2, 3, 2, 2, 1, 3, 2, 3, 2, 2], [2, 3, 2, 1, 2, 3, 2, 1, 2,
    2], [2, 3, 2, 1, 3, 2, 2, 1, 2, 3], [2, 3, 2, 3, 2, 1, 2, 2, 2, 1], [2, 2, 2, 3, 2, 2, 3, 2, 2,
    2], [2, 3, 2, 3, 2, 2, 3, 2, 2, 3], [2, 1, 2, 2, 3, 2, 3, 2, 2, 1], [2, 1, 2, 2, 3, 2, 1, 2, 1,
    2], [2, 2, 2, 1, 3, 2, 2, 2, 1, 3], [2, 2, 2, 3, 2, 1, 3, 2, 1, 2], [2, 2, 2, 3, 2, 1, 3, 2, 1,
    3], [2, 3, 2, 2, 3, 2, 2, 2, 2, 3], [2, 3, 2, 2, 1, 2, 2, 1, 2, 1], [1, 2, 3, 2, 3, 2, 1, 3, 2,
    1], [2, 2, 2, 3, 2, 3, 2, 2, 2, 3], [2, 2, 2, 3, 2, 1, 2, 1, 2, 2], [2, 2, 2, 3, 2, 1, 2, 1, 2,
    1], [2, 2, 2, 3, 2, 1, 2, 1, 3, 2], [2, 3, 2, 1, 3, 2, 2, 2, 1, 2], [2, 3, 2, 3, 2, 3, 2, 2, 2,
    3], [2, 2, 2, 1, 2, 2, 2, 2, 1, 3], [2, 3, 2, 3, 2, 1, 3, 2, 3, 2], [1, 2, 2, 2, 1, 2, 2, 2, 2,
    3], [2, 3, 2, 1, 3, 2, 2, 2, 2, 3], [1, 2, 2, 2, 1, 2, 2, 2, 2, 1], [2, 3, 2, 1, 2, 2, 2, 1, 2,
    3], [2, 2, 2, 1, 3, 2, 2, 1, 2, 2], [2, 2, 2, 3, 2, 1, 2, 2, 2, 2], [2, 1, 2, 2, 1, 2, 2, 2, 2,
    3], [1, 2, 2, 2, 3, 2, 3, 2, 2, 2], [2, 2, 2, 1, 2, 2, 3, 2, 1, 3], [2, 3, 2, 1, 2, 2, 3, 2, 2,
    2], [2, 2, 2, 1, 2, 2, 3, 2, 1, 2], [1, 2, 2, 2, 3, 2, 1, 3, 2, 3], [2, 1, 2, 2, 3, 2, 1, 3, 2,
    3], [2, 3, 2, 1, 2, 2, 2, 1, 2, 2], [1, 2, 2, 2, 3, 2, 3, 2, 2, 1], [2, 3, 2, 3, 2, 1, 2, 2, 2,
    2], [2, 3, 2, 3, 2, 1, 3, 2, 2, 3], [2, 2, 2, 1, 2, 2, 1, 2, 1, 2], [2, 3, 2, 1, 2, 2, 2, 2, 1,
    3], [2, 3, 2, 2, 3, 2, 3, 2, 1, 2], [2, 3, 2, 3, 2, 3, 2, 3, 2, 3], [2, 2, 2, 1, 2, 2, 1, 2, 1,
    3], [2, 3, 2, 1, 2, 2, 2, 2, 3, 2], [2, 2, 2, 2, 1, 2, 2, 1, 2, 3], [2, 2, 2, 1, 2, 2, 3, 2, 2,
    1], [2, 2, 2, 2, 1, 2, 3, 2, 2, 1], [2, 3, 2, 3, 2, 2, 3, 2, 2, 2], [2, 3, 2, 3, 2, 3, 2, 3, 2,
    2], [2, 2, 2, 3, 2, 1, 2, 2, 2, 3], [2, 2, 2, 1, 2, 2, 3, 2, 2, 2], [2, 3, 2, 3, 2, 1, 2, 1, 3,
    2], [2, 2, 2, 1, 2, 2, 1, 2, 2, 2], [1, 2, 2, 2, 3, 2, 3, 2, 3, 2], [2, 2, 2, 3, 2, 1, 2, 2, 2,
    1], [2, 2, 2, 2, 1, 2, 1, 2, 2, 1], [2, 2, 2, 2, 3, 2, 2, 2, 2, 1], [2, 2, 2, 3, 2, 1, 2, 3, 2,
    2], [1, 2, 2, 2, 1, 2, 2, 3, 2, 3], [2, 3, 2, 3, 2, 2, 3, 2, 2, 1], [2, 2, 2, 3, 2, 3, 2, 3, 2,
    3], [1, 2, 2, 2, 1, 2, 2, 2, 1, 2], [2, 3, 2, 1, 2, 2, 1, 2, 2, 2], [2, 3, 2, 3, 2, 1, 3, 2, 1,
    2], [2, 2, 2, 1, 2, 2, 2, 1, 2, 2], [2, 2, 2, 3, 2, 1, 2, 2, 2, 1, 2], [2, 3, 2, 2, 3, 2, 3, 2,
    1, 2, 2], [2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2], [2, 2, 2, 2, 1, 2, 3, 2, 2, 2, 1], [2, 3, 2, 1, 2,
    1, 2, 2, 2, 2, 1], [2, 3, 2, 1, 3, 2, 3, 2, 2, 2, 3], [2, 2, 2, 3, 2, 2, 3, 2, 2, 1, 3], [2, 2,
    2, 2, 1, 2, 3, 2, 2, 1, 2], [1, 2, 3, 2, 3, 2, 3, 2, 2, 2, 1], [1, 2, 2, 2, 3, 2, 1, 2, 1, 2,
    2], [2, 3, 2, 3, 2, 2, 2, 1, 3, 2, 1], [1, 2, 3, 2, 1, 3, 2, 2, 2, 2, 3], [2, 3, 2, 1, 2, 3, 2,
    3, 2, 2, 1], [2, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2], [2, 3, 2, 1, 2, 2, 1, 2, 1, 3, 2], [1, 2, 3, 2,
    3, 2, 1, 3, 2, 3, 2], [2, 3, 2, 2, 1, 3, 2, 2, 1, 2, 2], [2, 3, 2, 1, 2, 3, 2, 2, 1, 2, 3], [2,
    1, 2, 2, 1, 2, 2, 3, 2, 1, 3], [2, 3, 2, 2, 1, 3, 2, 1, 3, 2, 2], [2, 3, 2, 3, 2, 2, 2, 3, 2,
    3, 2], [2, 3, 2, 2, 1, 3, 2, 1, 2, 1, 3], [2, 3, 2, 1, 2, 2, 2, 2, 1, 3, 2], [2, 2, 2, 1, 2, 2,
    1, 2, 1, 3, 2], [2, 3, 2, 1, 3, 2, 2, 2, 2, 3, 2], [2, 3, 2, 2, 1, 2, 1, 2, 2, 3, 2], [2, 2, 2,
    2, 3, 2, 2, 3, 2, 3, 2], [2, 2, 2, 3, 2, 3, 2, 3, 2, 2, 3], [2, 2, 2, 3, 2, 2, 3, 2, 2, 1, 2],
    [1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 2], [2, 2, 2, 1, 2, 2, 3, 2, 2, 3, 2], [2, 3, 2, 3, 2, 1, 2, 2,
    2, 1, 3], [1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3], [2, 2, 2, 3, 2, 1, 2, 3, 2, 2, 3], [1, 2, 2, 2, 3,
    2, 3, 2, 3, 2, 3], [1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 2], [1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 3], [2, 2,
    2, 2, 1, 2, 1, 2, 2, 2, 2], [2, 3, 2, 3, 2, 2, 3, 2, 2, 1, 3], [2, 1, 2, 2, 3, 2, 2, 3, 2, 2,
    1], [1, 2, 3, 2, 3, 2, 1, 2, 1, 3, 2], [2, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2], [1, 2, 3, 2, 1, 2, 2,
    3, 2, 1, 2], [2, 3, 2, 2, 1, 2, 1, 2, 2, 2, 2], [2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 3], [2, 3, 2, 3,
    2, 1, 2, 2, 2, 3, 2], [2, 2, 2, 3, 2, 1, 2, 3, 2, 2, 1], [2, 3, 2, 3, 2, 1, 2, 2, 2, 1, 2], [2,
    2, 2, 1, 3, 2, 2, 2, 1, 2, 2], [2, 2, 2, 3, 2, 1, 2, 3, 2, 2, 2], [1, 2, 3, 2, 3, 2, 3, 2, 2,
    2, 3], [1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 2], [2, 3, 2, 1, 2, 2, 1, 2, 2, 1, 2], [1, 2, 2, 2, 2, 1,
    2, 2, 1, 2, 1], [1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 3], [1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 3], [2, 2, 2,
    1, 2, 2, 2, 1, 2, 2, 3], [2, 2, 2, 1, 2, 2, 2, 1, 2, 3, 2], [2, 3, 2, 1, 2, 2, 3, 2, 2, 2, 1],
    [1, 2, 3, 2, 3, 2, 3, 2, 2, 1, 2], [2, 2, 2, 3, 2, 1, 2, 2, 2, 3, 2], [2, 3, 2, 1, 2, 2, 1, 2,
    2, 2, 3], [2, 3, 2, 1, 2, 2, 3, 2, 1, 3, 2], [2, 1, 2, 2, 3, 2, 3, 2, 3, 2, 3], [1, 2, 2, 2, 2,
    3, 2, 2, 2, 2, 3], [2, 2, 2, 2, 3, 2, 3, 2, 1, 2, 2], [2, 3, 2, 3, 2, 2, 3, 2, 2, 2, 2], [2, 1,
    2, 2, 3, 2, 3, 2, 3, 2, 2], [1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2], [2, 1, 2, 2, 3, 2, 1, 3, 2, 2,
    3], [2, 3, 2, 3, 2, 2, 3, 2, 2, 1, 2], [1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 2], [2, 1, 2, 2, 2, 1, 2,
    2, 1, 2, 1], [2, 3, 2, 2, 1, 2, 2, 1, 2, 1, 3], [2, 2, 2, 3, 2, 3, 2, 3, 2, 2, 1], [1, 2, 2, 2,
    3, 2, 2, 3, 2, 2, 1], [2, 2, 2, 1, 2, 2, 3, 2, 1, 3, 2], [2, 3, 2, 1, 2, 2, 2, 1, 2, 2, 2], [1,
    2, 2, 2, 3, 2, 3, 2, 3, 2, 2], [1, 2, 2, 2, 3, 2, 3, 2, 2, 2, 1], [2, 3, 2, 1, 2, 2, 2, 1, 2,
    2, 3], [2, 3, 2, 2, 1, 2, 2, 1, 2, 2, 2], [1, 2, 2, 2, 3, 2, 3, 2, 2, 2, 3], [2, 3, 2, 1, 2, 2,
    2, 1, 2, 3, 2], [2, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3], [2, 3, 2, 1, 2, 2, 3, 2, 2, 2, 3], [1, 2, 2,
    2, 1, 2, 2, 2, 1, 2, 2], [2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2], [2, 2, 2, 3, 2, 3, 2, 2, 3, 2, 3],
    [2, 3, 2, 3, 2, 1, 2, 3, 2, 2, 1], [2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2], [1, 2, 2, 2, 3, 2, 1, 3,
    2, 1, 3], [2, 2, 2, 3, 2, 3, 2, 2, 2, 3, 2, 3], [1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 2, 1], [2, 2, 2,
    1, 2, 2, 2, 1, 2, 3, 2, 3], [2, 3, 2, 2, 1, 3, 2, 1, 2, 1, 3, 2], [1, 2, 3, 2, 1, 2, 2, 2, 1,
    2, 2, 3], [1, 2, 3, 2, 3, 2, 2, 3, 2, 2, 1, 2], [2, 3, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2], [1, 2, 2,
    2, 1, 2, 2, 1, 2, 1, 3, 2], [2, 3, 2, 2, 1, 2, 2, 1, 2, 2, 2, 3], [2, 1, 2, 2, 1, 2, 2, 1, 2,
    2, 2, 3]]

@[expose] def cfICls1W : List (List ℤ) :=
    [[], [2], [1], [1, 2], [2, 2], [2, 1], [1, 2, 2], [2, 1, 2], [2, 2, 2], [1, 2, 2, 1], [2, 1, 2,
    1], [2, 1, 2, 2], [2, 2, 2, 2], [2, 2, 2, 1], [1, 2, 2, 2], [2, 2, 2, 1, 2], [1, 2, 2, 2, 1],
    [1, 2, 2, 1, 2], [2, 1, 2, 1, 2], [2, 2, 2, 2, 1], [1, 2, 2, 2, 2], [2, 1, 2, 2, 1], [2, 1, 2,
    2, 2], [1, 2, 2, 1, 2, 1], [2, 1, 2, 2, 2, 2], [2, 1, 2, 1, 2, 2], [1, 2, 2, 2, 1, 2], [2, 1,
    2, 2, 2, 1], [2, 2, 2, 1, 2, 1], [1, 2, 2, 2, 2, 1], [2, 1, 2, 2, 1, 2], [2, 1, 2, 1, 2, 1],
    [2, 2, 2, 1, 2, 2], [1, 2, 2, 1, 2, 2], [2, 1, 2, 2, 1, 2, 1], [1, 2, 2, 1, 2, 1, 2], [2, 1, 2,
    2, 1, 2, 2], [2, 1, 2, 1, 2, 2, 2], [2, 2, 2, 1, 2, 1, 2], [2, 1, 2, 1, 2, 1, 2], [1, 2, 2, 2,
    1, 2, 1], [2, 2, 2, 2, 1, 2, 2], [1, 2, 2, 1, 2, 2, 2], [2, 1, 2, 1, 2, 2, 1], [2, 2, 2, 1, 2,
    2, 2], [1, 2, 2, 2, 1, 2, 2], [1, 2, 2, 1, 2, 2, 1], [2, 2, 2, 1, 2, 2, 1], [2, 1, 2, 1, 2, 2,
    1, 2], [2, 1, 2, 1, 2, 2, 2, 2], [2, 2, 2, 1, 2, 1, 2, 2], [2, 1, 2, 2, 1, 2, 2, 2], [1, 2, 2,
    1, 2, 2, 1, 2], [2, 1, 2, 1, 2, 2, 2, 1], [2, 2, 2, 2, 1, 2, 2, 2], [2, 1, 2, 2, 1, 2, 1, 2],
    [2, 1, 2, 2, 1, 2, 2, 1], [2, 1, 2, 1, 2, 1, 2, 2], [1, 2, 2, 1, 2, 1, 2, 2], [2, 2, 2, 1, 2,
    1, 2, 1], [1, 2, 2, 2, 1, 2, 2, 1], [1, 2, 2, 1, 2, 2, 2, 2], [1, 2, 2, 2, 1, 2, 2, 2], [1, 2,
    2, 2, 1, 2, 1, 2], [1, 2, 2, 1, 2, 1, 2, 1], [2, 2, 2, 1, 2, 2, 2, 1], [2, 2, 2, 2, 1, 2, 2,
    1], [2, 2, 2, 1, 2, 2, 2, 1, 2], [1, 2, 2, 1, 2, 2, 1, 2, 2], [1, 2, 2, 2, 1, 2, 2, 1, 2], [1,
    2, 2, 1, 2, 1, 2, 1, 2], [1, 2, 2, 2, 1, 2, 1, 2, 2], [2, 2, 2, 2, 1, 2, 2, 2, 2], [2, 2, 2, 1,
    2, 1, 2, 2, 2], [2, 1, 2, 1, 2, 2, 2, 1, 2], [2, 1, 2, 2, 1, 2, 1, 2, 1], [2, 1, 2, 1, 2, 1, 2,
    2, 1], [1, 2, 2, 2, 1, 2, 2, 2, 2], [2, 1, 2, 1, 2, 1, 2, 2, 2], [1, 2, 2, 1, 2, 2, 1, 2, 1],
    [2, 1, 2, 2, 2, 1, 2, 2, 1], [2, 1, 2, 2, 1, 2, 2, 1, 2], [2, 1, 2, 2, 1, 2, 2, 2, 2], [2, 1,
    2, 1, 2, 2, 1, 2, 1], [2, 1, 2, 2, 1, 2, 2, 2, 1], [1, 2, 2, 2, 2, 1, 2, 2, 2], [1, 2, 2, 1, 2,
    1, 2, 2, 2], [1, 2, 2, 1, 2, 1, 2, 2, 1], [2, 1, 2, 1, 2, 2, 1, 2, 2], [1, 2, 2, 2, 1, 2, 2, 2,
    1], [1, 2, 2, 1, 2, 1, 2, 2, 2, 2], [2, 1, 2, 1, 2, 2, 2, 1, 2, 2], [1, 2, 2, 2, 2, 1, 2, 2, 2,
    2], [1, 2, 2, 1, 2, 2, 1, 2, 1, 2], [1, 2, 2, 1, 2, 1, 2, 1, 2, 2], [2, 2, 2, 2, 1, 2, 2, 2, 1,
    2], [2, 1, 2, 2, 1, 2, 2, 2, 2, 1], [1, 2, 2, 2, 1, 2, 2, 1, 2, 1], [2, 2, 2, 1, 2, 1, 2, 2, 2,
    1], [1, 2, 2, 1, 2, 2, 1, 2, 2, 2], [1, 2, 2, 2, 2, 1, 2, 2, 2, 1], [1, 2, 2, 1, 2, 1, 2, 2, 2,
    1], [2, 2, 2, 1, 2, 2, 2, 1, 2, 1], [1, 2, 2, 2, 1, 2, 2, 1, 2, 2], [2, 2, 2, 2, 1, 2, 2, 2, 2,
    1], [2, 1, 2, 1, 2, 2, 1, 2, 2, 2], [1, 2, 2, 2, 2, 1, 2, 2, 1, 2], [2, 1, 2, 2, 1, 2, 2, 1, 2,
    2], [2, 1, 2, 1, 2, 2, 1, 2, 1, 2], [1, 2, 2, 1, 2, 1, 2, 1, 2, 1], [2, 2, 2, 1, 2, 1, 2, 2, 2,
    2], [2, 1, 2, 1, 2, 1, 2, 2, 2, 1], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2], [1, 2, 2, 1, 2, 2, 1, 2, 2,
    1], [2, 1, 2, 1, 2, 1, 2, 2, 1, 2], [2, 1, 2, 2, 1, 2, 2, 2, 1, 2], [2, 1, 2, 1, 2, 2, 1, 2, 2,
    1], [1, 2, 2, 2, 1, 2, 2, 2, 1, 2], [2, 1, 2, 2, 1, 2, 2, 1, 2, 1], [2, 2, 2, 1, 2, 2, 2, 1, 2,
    2], [2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2], [1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2], [1, 2, 2, 2, 2, 1, 2,
    2, 1, 2, 2], [2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1], [2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2], [2, 2, 2, 2,
    1, 2, 2, 2, 2, 1, 2], [2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2], [2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1], [1,
    2, 2, 2, 1, 2, 2, 1, 2, 2, 1], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2], [1, 2, 2, 2, 1, 2, 2, 2, 2,
    1, 2], [2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1], [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2], [1, 2, 2, 1, 2, 1,
    2, 2, 1, 2, 1], [2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1], [2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2], [2, 1, 2,
    2, 1, 2, 1, 2, 2, 2, 1], [2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2], [2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2],
    [2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2], [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1], [2, 1, 2, 1, 2, 2, 1, 2,
    1, 2, 2], [2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2], [2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2], [2, 1, 2, 2, 1,
    2, 2, 2, 1, 2, 2], [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2], [2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1], [2, 2,
    2, 1, 2, 2, 2, 1, 2, 2, 2], [1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2], [1, 2, 2, 1, 2, 1, 2, 2, 2, 2,
    1], [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2], [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2], [1, 2, 2, 2, 1, 2, 2,
    1, 2, 1, 2], [2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2], [2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2], [2, 1,
    2, 1, 2, 2, 1, 2, 2, 2, 1, 2], [2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2], [1, 2, 2, 2, 1, 2, 1, 2,
    2, 1, 2, 1], [2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1], [2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2], [1, 2,
    2, 2, 1, 2, 2, 1, 2, 1, 2, 2], [2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2], [1, 2, 2, 1, 2, 1, 2, 1,
    2, 1, 2, 2], [1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1], [1, 2,
    2, 2, 1, 2, 1, 2, 2, 1, 2, 2], [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1], [2, 1, 2, 2, 2, 1, 2, 2,
    2, 1, 2, 1], [1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1], [2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2], [1, 2,
    2, 2, 1, 2, 1, 2, 2, 2, 2, 1], [2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2], [1, 2, 2, 2, 1, 2, 2, 1,
    2, 1, 2, 1], [2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2], [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2], [2, 1,
    2, 1, 2, 2, 1, 2, 2, 1, 2, 1], [1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2], [2, 1, 2, 1, 2, 2, 1, 2,
    1, 2, 2, 1], [2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2], [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2], [1, 2,
    2, 1, 2, 1, 2, 2, 2, 1, 2, 2], [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2], [2, 1, 2, 2, 2, 1, 2, 2,
    2, 1, 2, 2], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2], [1, 2,
    2, 1, 2, 1, 2, 1, 2, 1, 2, 1], [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2], [1, 2, 2, 1, 2, 2, 1, 2,
    2, 1, 2, 1], [2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2], [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2], [2,
    2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2], [2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1], [2, 1, 2, 1, 2,
    2, 1, 2, 2, 1, 2, 1, 2], [1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1], [2, 2, 2, 1, 2, 1, 2, 2, 2,
    2, 1, 2, 2], [1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2], [2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2],
    [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2], [1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1], [1, 2, 2, 2,
    1, 2, 2, 1, 2, 1, 2, 2, 2], [2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2], [2, 2, 2, 2, 1, 2, 2, 2,
    2, 1, 2, 2, 1], [2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2], [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2,
    1], [1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2], [2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2], [1, 2, 2,
    1, 2, 2, 1, 2, 2, 2, 2, 1, 2], [2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1], [1, 2, 2, 1, 2, 2, 1,
    2, 2, 1, 2, 2, 2], [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2], [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2,
    2, 2], [2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2], [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2], [2, 1,
    2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1], [2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2], [1, 2, 2, 1, 2, 2,
    1, 2, 1, 2, 2, 1, 2], [2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2], [2, 2, 2, 2, 1, 2, 2, 2, 1, 2,
    1, 2, 2], [1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1], [2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2], [1,
    2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1], [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1], [2, 1, 2, 2, 1,
    2, 2, 1, 2, 1, 2, 2, 1], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2], [1, 2, 2, 1, 2, 2, 1, 2, 2,
    2, 2, 1, 2, 2], [2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2], [1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1,
    2, 2, 2], [2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2,
    2], [2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1], [1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2], [2,
    1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2], [1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2], [1, 2, 2,
    1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1], [2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2], [2, 2, 2, 1, 2,
    1, 2, 2, 2, 1, 2, 2, 2, 1], [1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2], [1, 2, 2, 2, 2, 1, 2,
    2, 1, 2, 2, 1, 2, 2], [2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2], [1, 2, 2, 2, 1, 2, 2, 1, 2,
    1, 2, 2, 2, 2], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1], [2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1,
    2, 2, 2], [2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2], [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2,
    2], [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2], [1,
    2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2], [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2], [1, 2, 2,
    2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2], [2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2], [1, 2, 2,
    1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2], [1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2], [2, 1, 2,
    2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2], [1, 2, 2,
    1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2], [1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2], [1, 2, 2,
    2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2], [1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2], [1, 2, 2,
    1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2], [2, 1, 2,
    1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2], [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1], [1, 2, 2,
    1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2], [2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1], [1,
    2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2], [2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2],
    [1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2,
    1], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1], [1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2,
    2, 2, 2, 1]]

@[expose] def cfICls2W : List (List ℤ) :=
    [[], [2], [2, 2], [2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 1], [2, 2, 2, 1, 2], [2, 2, 2, 2, 1], [2,
    2, 2, 1, 2, 1], [2, 2, 2, 2, 1, 2], [2, 2, 2, 1, 2, 2], [2, 2, 2, 2, 1, 2, 1], [2, 2, 2, 1, 2,
    1, 2], [2, 2, 2, 1, 2, 2, 1], [2, 2, 2, 1, 2, 2, 1, 2], [2, 2, 2, 1, 2, 1, 2, 2], [2, 2, 2, 2,
    1, 2, 1, 2], [2, 2, 2, 1, 2, 1, 2, 1], [2, 2, 2, 1, 2, 1, 2, 1, 2], [2, 2, 2, 1, 2, 2, 1, 2,
    2], [2, 2, 2, 2, 1, 2, 1, 2, 2], [2, 2, 2, 1, 2, 1, 2, 2, 2], [2, 2, 2, 1, 2, 2, 1, 2, 1], [2,
    2, 2, 1, 2, 2, 1, 2, 1, 2], [2, 2, 2, 1, 2, 1, 2, 1, 2, 1], [2, 2, 2, 2, 1, 2, 1, 2, 2, 2], [2,
    2, 2, 1, 2, 1, 2, 2, 2, 2], [2, 2, 2, 1, 2, 1, 2, 1, 2, 2], [2, 2, 2, 1, 2, 2, 1, 2, 2, 2], [2,
    2, 2, 2, 1, 2, 1, 2, 2, 1], [2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1], [2, 2, 2, 1, 2, 2, 1, 2, 1, 2,
    2], [2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2], [2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1], [2, 2, 2, 2, 1, 2, 1,
    2, 2, 2, 2], [2, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2], [2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1], [2, 2, 2, 1,
    2, 2, 1, 2, 1, 2, 2, 2], [2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2], [2, 2, 2, 1, 2, 2, 1, 2, 1, 2,
    2, 1], [2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2], [2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2], [2, 2, 2,
    1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1], [2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2], [2, 2, 2, 1, 2,
    2, 1, 2, 1, 2, 2, 1, 2, 2, 2]]

@[expose] def cfCls1 : List PX := cfCls1W.map fun w => tab (evalCodes [tab x45, tab y45, tab f45] w)

@[expose] def cfCls2 : List PX := cfCls2W.map fun w => tab (evalCodes [tab x45, tab y45, tab f45] w)

@[expose] def cfICls1 : List PX := cfICls1W.map fun w => tab (evalCodes [tab x45, tab y45] w)

@[expose] def cfICls2 : List PX := cfICls2W.map fun w => tab (evalCodes [tab x45, tab y45] w)

@[expose] def cfCls1C : List PX := cfCls1.map fun k => tab (k⁻¹ * s045 * k)

@[expose] def cfCls2C : List PX := cfCls2.map fun k => tab (k⁻¹ * (s045 * cfZ * cfTau) * k)

@[expose] def cfICls1C : List PX := cfICls1.map fun k => tab (k⁻¹ * cfZ * k)

@[expose] def cfICls2C : List PX := cfICls2.map fun k => tab (k⁻¹ * (cfZ * cfTau) * k)

@[expose] def cfCE : PX := List.formPerm [0, 15] * List.formPerm [1, 35] *
    List.formPerm [2, 25] * List.formPerm [3, 12] * List.formPerm [4, 14] *
    List.formPerm [5, 13] * List.formPerm [7, 8] * List.formPerm [10, 11] *
    List.formPerm [17, 44] * List.formPerm [18, 30] * List.formPerm [19, 26] *
    List.formPerm [20, 24] * List.formPerm [21, 40] * List.formPerm [22, 36] *
    List.formPerm [23, 34] * List.formPerm [27, 38] * List.formPerm [28, 33] *
    List.formPerm [31, 43] * List.formPerm [32, 39] * List.formPerm [37, 41]

@[expose] def cfE1 : PX := List.formPerm [0, 12] * List.formPerm [1, 14] *
    List.formPerm [2, 13] * List.formPerm [3, 15] * List.formPerm [4, 35] *
    List.formPerm [5, 25] * List.formPerm [10, 11] * List.formPerm [17, 44] *
    List.formPerm [18, 30] * List.formPerm [20, 38] * List.formPerm [21, 33] *
    List.formPerm [23, 41] * List.formPerm [24, 27] * List.formPerm [28, 40] *
    List.formPerm [31, 43] * List.formPerm [34, 37]

@[expose] def cfEe : PX := List.formPerm [1, 2] * List.formPerm [3, 12] *
    List.formPerm [4, 13] * List.formPerm [5, 14] * List.formPerm [6, 9] *
    List.formPerm [7, 10] * List.formPerm [8, 11] * List.formPerm [17, 19] *
    List.formPerm [18, 22] * List.formPerm [21, 23] * List.formPerm [25, 35] *
    List.formPerm [26, 44] * List.formPerm [27, 38] * List.formPerm [28, 41] *
    List.formPerm [29, 42] * List.formPerm [30, 36] * List.formPerm [31, 39] *
    List.formPerm [32, 43] * List.formPerm [33, 37] * List.formPerm [34, 40]

@[expose] def cfEn1 : PX := List.formPerm [0, 34, 26] *
    List.formPerm [1, 19, 27, 41, 32, 3] * List.formPerm [2, 10, 28, 43, 33, 17] *
    List.formPerm [4, 39, 20] * List.formPerm [5, 44, 21, 18, 40, 11] *
    List.formPerm [6, 29] * List.formPerm [7, 12, 35] *
    List.formPerm [8, 24, 14, 22, 15, 23] * List.formPerm [9, 16, 42] *
    List.formPerm [13, 31] * List.formPerm [25, 30] * List.formPerm [36, 38, 37]

@[expose] def cfEn2 : PX := List.formPerm [0, 21, 44, 34, 22] *
    List.formPerm [1, 36, 38, 33, 30] * List.formPerm [2, 10, 41, 32, 12] *
    List.formPerm [3, 25, 17, 35, 7] * List.formPerm [4, 39, 20, 13, 31] *
    List.formPerm [5, 18, 23, 8, 24] * List.formPerm [6, 42, 9, 16, 29] *
    List.formPerm [11, 14, 26, 15, 40] * List.formPerm [19, 27, 28, 43, 37]

@[expose] def cfBa : PX := List.formPerm [0, 15] * List.formPerm [1, 35] *
    List.formPerm [2, 25] * List.formPerm [3, 12] * List.formPerm [4, 14] *
    List.formPerm [5, 13] * List.formPerm [7, 8] * List.formPerm [10, 11] *
    List.formPerm [17, 44] * List.formPerm [18, 30] * List.formPerm [19, 26] *
    List.formPerm [20, 24] * List.formPerm [21, 40] * List.formPerm [22, 36] *
    List.formPerm [23, 34] * List.formPerm [27, 38] * List.formPerm [28, 33] *
    List.formPerm [31, 43] * List.formPerm [32, 39] * List.formPerm [37, 41]

@[expose] def cfBb : PX := List.formPerm [0, 15] * List.formPerm [1, 34] *
    List.formPerm [2, 40] * List.formPerm [3, 12] * List.formPerm [4, 41] *
    List.formPerm [5, 33] * List.formPerm [7, 32] * List.formPerm [8, 39] *
    List.formPerm [10, 43] * List.formPerm [11, 31] * List.formPerm [13, 28] *
    List.formPerm [14, 37] * List.formPerm [17, 30] * List.formPerm [18, 44] *
    List.formPerm [19, 36] * List.formPerm [20, 24] * List.formPerm [21, 25] *
    List.formPerm [22, 26] * List.formPerm [23, 35] * List.formPerm [27, 38]

@[expose] def cfBc : PX := List.formPerm [1, 23] * List.formPerm [2, 21] *
    List.formPerm [4, 37] * List.formPerm [5, 28] * List.formPerm [7, 39] *
    List.formPerm [8, 32] * List.formPerm [10, 31] * List.formPerm [11, 43] *
    List.formPerm [13, 33] * List.formPerm [14, 41] * List.formPerm [17, 18] *
    List.formPerm [19, 22] * List.formPerm [25, 40] * List.formPerm [26, 36] *
    List.formPerm [30, 44] * List.formPerm [34, 35]

@[expose] def cfB : List PX := [cfBa, cfBb, cfBc]

end CFSG.ComponentClassification.CatFactsSmall.PSp43
