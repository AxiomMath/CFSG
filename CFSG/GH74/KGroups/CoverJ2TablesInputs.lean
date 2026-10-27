module

public import Mathlib
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative

public section

namespace CFSG.GH74.KGroups.J2

open CFSG.ComponentClassification.J2Cover.Models
@[expose] def uList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 4), (0, 11), (0, 18), (0, 23), (0, 32), (0, 37), (0, 40), (0, 46), (0, 48), (0, 57), (0, 62), (0, 70), (0, 80), (0, 81), (0, 83), (0, 85), (0, 86), (0, 88), (0, 93), (0, 94), (0, 95), (0, 108), (0, 115), (0, 116), (0, 117), (0, 119), (0, 120), (0, 122), (0, 123), (0, 124), (1, 0), (1, 1), (1, 4), (1, 11), (1, 18), (1, 23), (1, 32), (1, 37), (1, 40), (1, 46), (1, 48), (1, 57), (1, 62), (1, 70), (1, 80), (1, 81), (1, 83), (1, 85), (1, 86), (1, 88), (1, 93), (1, 94), (1, 95), (1, 108), (1, 115), (1, 116), (1, 117), (1, 119), (1, 120), (1, 122), (1, 123), (1, 124)]

@[expose] def nElt : ℕ × ℕ := (1, 4)

@[expose] def mulM (p q : ℕ × ℕ) : ℕ × ℕ :=
  ((p.1 + q.1 + (if bitAt fRows p.2 q.2 then 1 else 0)) % 2, mulIdx p.2 q.2)

end CFSG.GH74.KGroups.J2
