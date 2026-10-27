module

public import CFSG.Foundations.Basic
public import CFSG.Assembly.Defs

public section

namespace CFSG.Foundations.SteinbergCA

variable {G : Type*} [Group G]

theorem component_iff (K : Subgroup G) :
    CFSG.IsComponent K ↔ CFSG.IsQuasisimple K ∧ K.IsSubnormal :=
  Iff.rfl

end CFSG.Foundations.SteinbergCA
