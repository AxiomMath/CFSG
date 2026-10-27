module

public import CFSG.LieType.Steinberg.Minuscule.Unipotent
public import CFSG.LieType.Steinberg.BruhatWeyl
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Group.Subgroup.Lattice

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

theorem e6_weyl_lt :
    ∀ (i : Fin CFSG.Blueprint.Chevalley.Tag.E6.rank) (a : Fin e6Data.d),
      e6Data.weyl a i < e6Data.d := by
  decide +kernel

theorem e6_weyl_involutive :
    ∀ (i : Fin CFSG.Blueprint.Chevalley.Tag.E6.rank) (a : Fin e6Data.d),
      e6Data.weyl (e6Data.weyl a i) i = a := by
  decide +kernel

@[expose] def e6ReflectionPerm (i : Fin CFSG.Blueprint.Chevalley.Tag.E6.rank) :
    Equiv.Perm (Fin e6Data.d) where
  toFun a := ⟨e6Data.weyl a i, e6_weyl_lt i a⟩
  invFun a := ⟨e6Data.weyl a i, e6_weyl_lt i a⟩
  left_inv a := Fin.ext (e6_weyl_involutive i a)
  right_inv a := Fin.ext (e6_weyl_involutive i a)

@[simp] theorem e6ReflectionPerm_val (i : Fin CFSG.Blueprint.Chevalley.Tag.E6.rank)
    (a : Fin e6Data.d) :
    (e6ReflectionPerm i a : ℕ) = e6Data.weyl a i := rfl

end CFSG.LieType.Steinberg.Minuscule
