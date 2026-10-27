module

public import CFSG.ClassicalInvolution.Q3.Q3MTFinal
public import CFSG.ClassicalInvolution.Q3.Q3MTShapeA
public import CFSG.ClassicalInvolution.Q3.Q3MTShapeB
public import CFSG.ClassicalInvolution.Q3.Q3MTM11
public import CFSG.ClassicalInvolution.Q3.Q3MTLarge
public import CFSG.ClassicalInvolution.Q3.Q3MTG2
public import CFSG.ClassicalInvolution.Q3.Q3MTTD4

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Assembly CFSG.ClassicalInvolution.Uniform


theorem muSmallShapes3 : MuSmallShapes3 where
  psl3 := smallShape3_psl3
  psl4 := smallShape3_psl4
  psl5 := smallShape3_psl5
  psu3 := smallShape3_psu3
  psu4 := smallShape3_psu4
  psu5 := psu5Shape3
  psp2 := smallShape3_psp2
  pOmegaOdd3 := smallShape3_pOmegaOdd3
  pOmegaPlus4 := smallShape3_pOmegaPlus4
  pOmegaMinus4 := smallShape3_pOmegaMinus4
  g2 := g2Shape3
  trialityD4 := trialityD4Shape3
  large := largeShape3
  m11 := m11Shape3

theorem muTable_three : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → MuTableBelowU 3 1 n :=
  muTable_three_of_shapes muSmallShapes3

end CFSG.ClassicalInvolution.Q3.Q3MT
