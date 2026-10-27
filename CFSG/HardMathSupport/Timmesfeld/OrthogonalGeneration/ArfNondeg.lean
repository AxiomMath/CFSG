module

public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def PolarNondeg (Q : QuadraticForm (ZMod 2) V) : Prop :=
  (polarBilin Q).Nondegenerate

theorem PolarNondeg.of_forall {Q : QuadraticForm (ZMod 2) V}
    (h : ∀ v, (∀ w, polar Q v w = 0) → v = 0) : PolarNondeg Q :=
  ⟨fun v hv => h v fun w => by simpa using hv w,
    fun w hw => h w fun v => by rw [polar_comm]; simpa using hw v⟩

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
