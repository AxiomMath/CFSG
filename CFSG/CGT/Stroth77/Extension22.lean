module

public import CFSG.CGT.Stroth77.TypePredicates

public section

namespace CFSG.CGT.Stroth77

section Group

variable {S : Type*} [Group S] {B : Subgroup S} {τ : StrothTypeIndex}

namespace StrothTypeData

@[expose] def L (D : StrothTypeData B τ) : Subgroup S :=
  Subgroup.closure ({D.uv, D.t, D.u, D.ρ} : Set S)

theorem uv_mem_L (D : StrothTypeData B τ) : D.uv ∈ D.L :=
  Subgroup.subset_closure (by simp)

theorem t_mem_L (D : StrothTypeData B τ) : D.t ∈ D.L :=
  Subgroup.subset_closure (by simp)

theorem u_mem_L (D : StrothTypeData B τ) : D.u ∈ D.L :=
  Subgroup.subset_closure (by simp)

theorem ρ_mem_L (D : StrothTypeData B τ) : D.ρ ∈ D.L :=
  Subgroup.subset_closure (by simp)

end StrothTypeData

end Group

end CFSG.CGT.Stroth77
