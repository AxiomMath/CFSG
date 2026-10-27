module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticTransvection
public import CFSG.ClassicalGroups.Alternating.Transvections

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Module CFSG.ClassicalGroups.Alternating

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {B : LinearMap.BilinForm (ZMod 2) V}

theorem symplecticTransvection_one_eq_binarySymplecticTransvection (hB : B.IsAlt) (w : V) :
    symplecticTransvection B hB w 1 = binarySymplecticTransvection B hB w :=
  BinarySymplecticTransvection.gl_ext fun x => by
    rw [symplecticTransvection_apply, binarySymplecticTransvection_apply, one_mul]

end CFSG.LocalAnalysis.ComponentInitial
