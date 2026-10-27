module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace

public section

namespace CFSG.LinearAlgebra

open scoped TensorProduct

theorem finrank_piTensorProduct {ι F : Type*} [Fintype ι] [Field F] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)] [∀ i, Module.Finite F (V i)] :
    Module.finrank F (⨂[F] i, V i) = ∏ i, Module.finrank F (V i) := by
  classical
  rw [Module.finrank_eq_card_basis
    (Basis.piTensorProduct (fun i => Module.finBasis F (V i))), Fintype.card_pi]
  simp

end CFSG.LinearAlgebra
