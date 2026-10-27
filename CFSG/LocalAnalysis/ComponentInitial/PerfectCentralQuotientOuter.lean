module

public import CFSG.LocalAnalysis.ComponentInitial.GroupOuter

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner centerQuotient_conj)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

variable (L : Type*) [Group L]

theorem inner_le_ker_outerOfCenterQuotient : inner L ≤ (outerOfCenterQuotient L).ker := by
  rintro _ ⟨x, rfl⟩
  rw [MonoidHom.mem_ker, outerOfCenterQuotient, MonoidHom.comp_apply, centerQuotient_conj]
  exact (QuotientGroup.eq_one_iff _).2 ⟨_, rfl⟩

@[expose] noncomputable def outerCenterQuotientHom : Outer L →* Outer (L ⧸ center L) :=
  QuotientGroup.lift (inner L) (outerOfCenterQuotient L) (inner_le_ker_outerOfCenterQuotient L)

theorem outerCenterQuotientHom_mk (a : MulAut L) :
    outerCenterQuotientHom L (QuotientGroup.mk a) =
      QuotientGroup.mk (centerQuotientHom L a) :=
  rfl

theorem outerCenterQuotientHom_injective [Group.IsPerfect L] :
    Function.Injective (outerCenterQuotientHom L) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, hx⟩ := exists_conj_eq_of_outerOfCenterQuotient_eq_one hq
  exact (QuotientGroup.eq_one_iff a).2 ⟨x, hx⟩

theorem perfect_central_quotient_Schreier [Group.IsPerfect L] :
    Function.Injective (outerCenterQuotientHom L) ∧
    (∀ a : MulAut L, outerCenterQuotientHom L (QuotientGroup.mk a) =
      QuotientGroup.mk (centerQuotientHom L a)) ∧
    (Group.IsSolvable (Outer (L ⧸ center L)) → Group.IsSolvable (Outer L)) :=
  ⟨outerCenterQuotientHom_injective L, outerCenterQuotientHom_mk L,
    fun _ => Group.isSolvable_of_isSolvable_injective (outerCenterQuotientHom_injective L)⟩

end CFSG.LocalAnalysis.ComponentInitial
