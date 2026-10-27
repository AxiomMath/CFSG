module

public import CFSG.Foundations.Basic

public section

namespace CFSG

variable {G H : Type*} [Group G] [Group H]

theorem IsQuasisimple.of_mulEquiv (e : G ≃* H) (h : CFSG.IsQuasisimple H) :
    CFSG.IsQuasisimple G := by
  obtain ⟨hperfect, hsimple, a, b, hab⟩ := h
  let f := QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e (Subgroup.map_center_eq e)
  refine ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
    f.isSimpleGroup, f.symm a, f.symm b, fun hcomm => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg f hcomm

theorem IsQuasisimple.congr (e : G ≃* H) : CFSG.IsQuasisimple G ↔ CFSG.IsQuasisimple H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

end CFSG
