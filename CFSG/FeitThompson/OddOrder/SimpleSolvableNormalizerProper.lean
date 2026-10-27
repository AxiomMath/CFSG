module
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Foundations.SolvablePerfectTrivial
import CFSG.FeitThompson.Foundations.DerivedSubgroupCharacteristic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

theorem not_isSolvable_of_isSimpleGroup [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) :
    ¬ Group.IsSolvable G := by
  intro hs
  have hc : commutator G ≠ ⊥ := fun h => hna ((commutator_eq_bot_iff G).1 h)
  have hnormal : (commutator G).Normal := by
    rw [← closure_setOf_inv_mul_inv_mul_mul_eq_commutator]
    exact normal_closure_setOf_inv_mul_inv_mul_mul G
  have htop : commutator G = ⊤ :=
    (haveI := hnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G)).resolve_left hc
  have : Subsingleton G := subsingleton_of_isSolvable_of_commutator_eq_top G htop
  exact hna ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩

theorem normalizer_coe_lt_top_of_isSolvable [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    {A : Subgroup G} (hA : A ≠ ⊥) [Group.IsSolvable A] :
    Subgroup.normalizer (A : Set G) < ⊤ := by
  refine lt_top_iff_ne_top.2 fun h => ?_
  rcases (haveI := Subgroup.normalizer_eq_top_iff.1 h; IsSimpleGroup.eq_bot_or_eq_top_of_normal A) with
    rfl | rfl
  · exact hA rfl
  · exact not_isSolvable_of_isSimpleGroup hna
      (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := G)).toMonoidHom)
        Subgroup.topEquiv.surjective)

theorem normalizer_coe_lt_top_of_isSolvable_of_finite [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) {A : Subgroup G} (hA : A ≠ ⊥) [Group.IsSolvable A] :
    Subgroup.normalizer (A : Set G) < ⊤ :=
  normalizer_coe_lt_top_of_isSolvable hna hA

theorem exists_conj_image_ne_of_isSolvable [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    {A : Subgroup G} (hA : A ≠ ⊥) [Group.IsSolvable A] :
    ∃ g : G, (fun x => g⁻¹ * x * g) '' (A : Set G) ≠ (A : Set G) := by
  obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt (normalizer_coe_lt_top_of_isSolvable hna hA)
  refine ⟨g⁻¹, fun hgA => hg ?_⟩
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  simpa [MulAut.conj] using hgA

end CFSG.FeitThompson
