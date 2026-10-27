module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.OrthModel

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.Sporadic.He.Native

section Orth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (e : ι ≃ Fin d)
  (Q : (ι → ZMod 2) → ZMod 2)

theorem statedOmega_le_OrthN : StatedOmega Q ≤ OrthN Q :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact (OrthN Q).mul_mem ((OrthN Q).mul_mem ((OrthN Q).mul_mem ha hb) ((OrthN Q).inv_mem ha))
      ((OrthN Q).inv_mem hb)

end Orth

end CFSG.HardMathSupport.Foote.E27
