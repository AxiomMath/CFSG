module

public import Mathlib.Algebra.Module.Submodule.Ker


public section

namespace CFSG.GroupTheory.CoprimeActionSupport.InvolutionNoInvariantsNegativeIdentity

theorem eq_neg_id {F W : Type*} [Field F] [AddCommGroup W] [Module F W] (h2 : (2 : F) ≠ 0)
    (t : Module.End F W) (ht : t * t = 1)
    (hfix : LinearMap.ker (t - LinearMap.id) = ⊥) : t = -LinearMap.id := by
  have _ := h2
  ext v
  have hmem : t v + v ∈ LinearMap.ker (t - LinearMap.id) := by
    have : t (t v) = v := by simpa using congrArg (fun f => f v) ht
    simp [LinearMap.mem_ker, this, add_comm]
  rw [hfix] at hmem
  have : t v + v = 0 := by simpa using hmem
  simpa using eq_neg_of_add_eq_zero_left this

end CFSG.GroupTheory.CoprimeActionSupport.InvolutionNoInvariantsNegativeIdentity
