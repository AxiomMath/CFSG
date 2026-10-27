module

public import CFSG.ClassicalInvolution.Q3.Q3MTKind
public import CFSG.ClassicalInvolution.Uniform.U5Three2
public import CFSG.ClassicalInvolution.Uniform.U9G2

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.ClassicalInvolution.Uniform


theorem muTable_three_of_shapes (hsh : MuSmallShapes3) :
    ∀ n : ℕ, CITBelowT (.sl2 3 1) n → MuTableBelowU 3 1 n := fun _ hn =>
  muTableBelowU_three_of_shapes hn hsh (thm6TypedBelowU_three_of_citBelowT hn)
    (thm8TypedBelowU_three_of ih8G2D4EdgeU_proved ih8ThreeU_proved hn)

end CFSG.ClassicalInvolution.Q3.Q3MT
