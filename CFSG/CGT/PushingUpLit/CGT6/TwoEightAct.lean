module

public import Mathlib.Algebra.Group.End

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

section Act

variable {S M W : Type*} [Group S] (act : S → M → M) (h1 : ∀ m, act 1 m = m)
  (hmul : ∀ s t m, act (s * t) m = act s (act t m)) (κ : M ≃ W)

@[expose] def actPerm : S →* Equiv.Perm W where
  toFun s :=
    { toFun := fun w => κ (act s (κ.symm w))
      invFun := fun w => κ (act s⁻¹ (κ.symm w))
      left_inv := fun w => by
        simp only [Equiv.symm_apply_apply]
        rw [← hmul, inv_mul_cancel, h1, Equiv.apply_symm_apply]
      right_inv := fun w => by
        simp only [Equiv.symm_apply_apply]
        rw [← hmul, mul_inv_cancel, h1, Equiv.apply_symm_apply] }
  map_one' := by
    ext w : 1
    show κ (act 1 (κ.symm w)) = w
    rw [h1, Equiv.apply_symm_apply]
  map_mul' s t := by
    ext w : 1
    show κ (act (s * t) (κ.symm w)) = κ (act s (κ.symm (κ (act t (κ.symm w)))))
    rw [Equiv.symm_apply_apply, hmul]

theorem actPerm_apply (s : S) (m : M) : actPerm act h1 hmul κ s (κ m) = κ (act s m) := by
  show κ (act s (κ.symm (κ m))) = _
  rw [Equiv.symm_apply_apply]

end Act

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
