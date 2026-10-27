module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.ComponentClassification.CentralCover

open PerfectAutomorphisms

theorem centerQuotientHom_apply_mk (L : Type*) [Group L] (α : MulAut L) (g : L) :
    centerQuotientHom L α (g : L ⧸ Subgroup.center L) = (α g : L ⧸ Subgroup.center L) :=
  onCenterQuotient_apply_mk α g

theorem perfect_central_quotient_automorphism_faithful (L : Type*) [Group L]
    [Group.IsPerfect L] : Function.Injective (centerQuotientHom L) :=
  centerQuotientHom_injective L

theorem eq_one_of_forall_inv_mul_mem_center {L : Type*} [Group L] [Group.IsPerfect L]
    (α : MulAut L) (h : ∀ g, g⁻¹ * α g ∈ Subgroup.center L) : α = 1 := by
  have hid := hom_eq_id_of_central_displacement α.toMonoidHom h
  ext g
  exact congrArg (fun f : L →* L => f g) hid

end CFSG.ComponentClassification.CentralCover
