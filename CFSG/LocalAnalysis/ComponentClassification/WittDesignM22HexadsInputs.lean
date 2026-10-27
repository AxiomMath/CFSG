module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignSteiner3
public import CFSG.Monster.B.Classical.PlaneData
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Monster.B.Classical.PlaneData
public import Certificates.Certificate2195

public section

namespace CFSG.ComponentClassification.WittDesign

open scoped Pointwise
open CFSG.Sporadic.Mathieu CFSG.Monster.B.Classical.Plane

@[expose] def hexadList : List (Finset (Fin 22)) :=
  [{0, 1, 2, 9, 17, 19}, {0, 1, 3, 6, 14, 20}, {0, 1, 4, 5, 13, 18}, {0, 1, 7, 8, 16, 21},
    {0, 1, 10, 11, 12, 15}, {0, 2, 3, 7, 12, 13}, {0, 2, 4, 11, 20, 21}, {0, 2, 5, 6, 8, 15},
    {0, 2, 10, 14, 16, 18}, {0, 3, 4, 8, 10, 17}, {0, 3, 5, 9, 11, 16}, {0, 3, 15, 18, 19, 21},
    {0, 4, 6, 12, 16, 19}, {0, 4, 7, 9, 14, 15}, {0, 5, 7, 10, 19, 20}, {0, 5, 12, 14, 17, 21},
    {0, 6, 7, 11, 17, 18}, {0, 6, 9, 10, 13, 21}, {0, 8, 9, 12, 18, 20}, {0, 8, 11, 13, 14, 19},
    {0, 13, 15, 16, 17, 20}, {1, 2, 3, 5, 10, 21}, {1, 2, 4, 8, 12, 14}, {1, 2, 6, 11, 13, 16},
    {1, 2, 7, 15, 18, 20}, {1, 3, 4, 7, 11, 19}, {1, 3, 8, 9, 13, 15}, {1, 3, 12, 16, 17, 18},
    {1, 4, 6, 15, 17, 21}, {1, 4, 9, 10, 16, 20}, {1, 5, 6, 7, 9, 12}, {1, 5, 8, 11, 17, 20},
    {1, 5, 14, 15, 16, 19}, {1, 6, 8, 10, 18, 19}, {1, 7, 10, 13, 14, 17}, {1, 9, 11, 14, 18, 21},
    {1, 12, 13, 19, 20, 21}, {2, 3, 4, 6, 9, 18}, {2, 3, 8, 16, 19, 20}, {2, 3, 11, 14, 15, 17},
    {2, 4, 5, 7, 16, 17}, {2, 4, 10, 13, 15, 19}, {2, 5, 9, 13, 14, 20}, {2, 5, 11, 12, 18, 19},
    {2, 6, 7, 14, 19, 21}, {2, 6, 10, 12, 17, 20}, {2, 7, 8, 9, 10, 11}, {2, 8, 13, 17, 18, 21},
    {2, 9, 12, 15, 16, 21}, {3, 4, 5, 12, 15, 20}, {3, 4, 13, 14, 16, 21}, {3, 5, 6, 13, 17, 19},
    {3, 5, 7, 8, 14, 18}, {3, 6, 7, 10, 15, 16}, {3, 6, 8, 11, 12, 21}, {3, 7, 9, 17, 20, 21},
    {3, 9, 10, 12, 14, 19}, {3, 10, 11, 13, 18, 20}, {4, 5, 6, 10, 11, 14}, {4, 5, 8, 9, 19, 21},
    {4, 6, 7, 8, 13, 20}, {4, 7, 10, 12, 18, 21}, {4, 8, 11, 15, 16, 18}, {4, 9, 11, 12, 13, 17},
    {4, 14, 17, 18, 19, 20}, {5, 6, 16, 18, 20, 21}, {5, 7, 11, 13, 15, 21},
    {5, 8, 10, 12, 13, 16}, {5, 9, 10, 15, 17, 18}, {6, 8, 9, 14, 16, 17}, {6, 9, 11, 15, 19, 20},
    {6, 12, 13, 14, 15, 18}, {7, 8, 12, 15, 17, 19}, {7, 9, 13, 16, 18, 19},
    {7, 11, 12, 14, 16, 20}, {8, 10, 14, 15, 20, 21}, {10, 11, 16, 17, 19, 21}]

@[expose] def hexadMasks : List ℕ := hexadList.map mask

@[expose] def hexad0 : Finset (Fin 22) := {0, 1, 2, 9, 17, 19}

@[expose] def interBits (m m' : ℕ) : ℕ :=
  ((List.finRange 22).filter fun i : Fin 22 => m.testBit i && m'.testBit i).length

end CFSG.ComponentClassification.WittDesign
