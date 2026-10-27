module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLevi

public section

namespace CFSG.SeitzReduction.E6Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem e6RepFrame_mem_a5LeviRoots (κ : Fin 3) : ∀ β ∈ e6RepFrame κ, β ∈ a5LeviRoots :=
  fun β hβ => ⟨(e6RepFrame_perp κ β hβ).1, (e6RepFrame_perp κ β hβ).2.1⟩

variable {K : Type} [Field K]

theorem e6Rep_mem_a5Levi (κ : Fin 3) : e6Rep K κ ∈ a5Levi K :=
  mem_a5Levi_iff.2 (coe_e6Rep_mem_rootSpan (e6RepFrame_mem_a5LeviRoots κ))

theorem exists_conj_eq_e6Rep_mem_a5Levi [Finite K] [CharP K 2] {y : adjointGroup .E6 K}
    (hy : orderOf y = 2) :
    ∃ (κ : Fin 3) (c : adjointGroup .E6 K), c * y * c⁻¹ = e6Rep K κ ∧ e6Rep K κ ∈ a5Levi K ∧
      orderOf (e6Rep K κ) = 2 := by
  obtain ⟨κ, c, hc⟩ := exists_conj_eq_e6Rep hy
  exact ⟨κ, c, hc, e6Rep_mem_a5Levi κ, orderOf_e6Rep κ⟩

end CFSG.SeitzReduction.E6Pilot
