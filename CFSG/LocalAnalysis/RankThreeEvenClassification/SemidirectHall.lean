module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem semidirect_inl_left_eq {acted : Type u} {actor : Type v}
    [Group acted] [Group actor] (action : actor →* MulAut acted)
    (element : SemidirectProduct acted actor action) :
    SemidirectProduct.inl element.left = element * SemidirectProduct.inr element.right⁻¹ := by
  apply SemidirectProduct.ext <;> simp

def semidirectSubgroupEquiv {acted : Type u} {actor : Type v}
    [Group acted] [Group actor] (action : actor →* MulAut acted)
    (subgroup : Subgroup (SemidirectProduct acted actor action))
    (hactor : ∀ member : actor, SemidirectProduct.inr member ∈ subgroup) :
    subgroup ≃ subgroup.comap SemidirectProduct.inl × actor where
  toFun element :=
    (⟨element.val.left, by
      change SemidirectProduct.inl element.val.left ∈ subgroup
      rw [semidirect_inl_left_eq action]
      exact subgroup.mul_mem element.property (hactor element.val.right⁻¹)⟩, element.val.right)
  invFun pair := ⟨SemidirectProduct.inl pair.1.val * SemidirectProduct.inr pair.2,
    subgroup.mul_mem pair.1.property (hactor pair.2)⟩
  left_inv element := by
    apply Subtype.ext
    apply SemidirectProduct.ext <;> simp
  right_inv pair := by
    apply Prod.ext
    · apply Subtype.ext
      simp
    · simp

theorem semidirect_subgroup_card {acted : Type u} {actor : Type v}
    [Group acted] [Group actor] (action : actor →* MulAut acted)
    (subgroup : Subgroup (SemidirectProduct acted actor action))
    (hactor : ∀ member : actor, SemidirectProduct.inr member ∈ subgroup) :
    Nat.card subgroup = Nat.card (subgroup.comap SemidirectProduct.inl) * Nat.card actor := by
  rw [Nat.card_congr (semidirectSubgroupEquiv action subgroup hactor), Nat.card_prod]

theorem semidirect_subgroup_index {acted : Type u} {actor : Type v}
    [Group acted] [Group actor] [Finite acted] [Finite actor] (action : actor →* MulAut acted)
    (subgroup : Subgroup (SemidirectProduct acted actor action))
    (hactor : ∀ member : actor, SemidirectProduct.inr member ∈ subgroup) :
    (subgroup.comap SemidirectProduct.inl).index = subgroup.index := by
  have hfirst := (subgroup.comap (SemidirectProduct.inl : acted →*
    SemidirectProduct acted actor action)).card_mul_index
  have hsecond := subgroup.card_mul_index
  rw [semidirect_subgroup_card action subgroup hactor, SemidirectProduct.card] at hsecond
  rw [← hfirst] at hsecond
  have heq : Nat.card (subgroup.comap SemidirectProduct.inl) * subgroup.index * Nat.card actor =
      Nat.card (subgroup.comap SemidirectProduct.inl) *
        (subgroup.comap SemidirectProduct.inl).index * Nat.card actor := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hsecond
  have hcancel := mul_right_cancel₀ (Nat.card_pos (α := actor)).ne' heq
  exact (mul_left_cancel₀ (Nat.card_pos (α := subgroup.comap SemidirectProduct.inl)).ne' hcancel).symm

@[expose] def invariantSemidirectSubgroup {acted : Type u} {actor : Type v}
    [Group acted] [Group actor] (action : actor →* MulAut acted) (subgroup : Subgroup acted)
    (hinvariant : ∀ member : actor, subgroup.map (action member).toMonoidHom = subgroup) :
    Subgroup (SemidirectProduct acted actor action) where
  carrier := {element | element.left ∈ subgroup}
  one_mem' := by simp
  mul_mem' := by
    intro first second hfirst hsecond
    change (first * second).left ∈ subgroup
    rw [SemidirectProduct.mul_left]
    apply subgroup.mul_mem hfirst
    have hmem := Subgroup.mem_map_of_mem (action first.right).toMonoidHom hsecond
    rw [hinvariant first.right] at hmem
    exact hmem
  inv_mem' := by
    intro element helement
    change element⁻¹.left ∈ subgroup
    rw [SemidirectProduct.inv_left]
    have hmem := Subgroup.mem_map_of_mem (action element.right⁻¹).toMonoidHom
      (subgroup.inv_mem helement)
    rw [hinvariant element.right⁻¹] at hmem
    exact hmem

theorem invariant_semidirect_subgroup_card {acted : Type u} {actor : Type v}
    [Group acted] [Group actor] (action : actor →* MulAut acted) (subgroup : Subgroup acted)
    (hinvariant : ∀ member : actor, subgroup.map (action member).toMonoidHom = subgroup) :
    Nat.card (invariantSemidirectSubgroup action subgroup hinvariant) =
      Nat.card subgroup * Nat.card actor := by
  have hactor : ∀ member : actor, SemidirectProduct.inr member ∈
      invariantSemidirectSubgroup action subgroup hinvariant := by
    intro member
    change (SemidirectProduct.inr member : SemidirectProduct acted actor action).left ∈ subgroup
    simp
  rw [semidirect_subgroup_card action _ hactor]
  have hcomap : (invariantSemidirectSubgroup action subgroup hinvariant).comap
      SemidirectProduct.inl = subgroup := by
    ext element
    change (SemidirectProduct.inl element : SemidirectProduct acted actor action).left ∈ subgroup ↔
      element ∈ subgroup
    simp
  rw [hcomap]

theorem semidirect_comap_inl_invariant {acted : Type u} {actor : Type v}
    [Group acted] [Group actor] (action : actor →* MulAut acted)
    (subgroup : Subgroup (SemidirectProduct acted actor action))
    (hactor : ∀ member : actor, SemidirectProduct.inr member ∈ subgroup) :
    ∀ member : actor, (subgroup.comap SemidirectProduct.inl).map (action member).toMonoidHom =
      subgroup.comap SemidirectProduct.inl := by
  intro member
  apply le_antisymm
  · intro element helement
    obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp helement
    change SemidirectProduct.inl ((action member) preimage) ∈ subgroup
    rw [SemidirectProduct.inl_aut]
    exact subgroup.mul_mem (subgroup.mul_mem (hactor member) hpreimage) (hactor member⁻¹)
  · intro element helement
    have hinverse : (action member⁻¹) element ∈ subgroup.comap SemidirectProduct.inl := by
      change SemidirectProduct.inl ((action member⁻¹) element) ∈ subgroup
      rw [SemidirectProduct.inl_aut]
      exact subgroup.mul_mem (subgroup.mul_mem (hactor member⁻¹) helement) (hactor (member⁻¹)⁻¹)
    refine Subgroup.mem_map.mpr ⟨(action member⁻¹) element, hinverse, ?_⟩
    change (action member) ((action member⁻¹) element) = element
    rw [map_inv]
    exact (action member).apply_symm_apply element

end CFSG.RankThreeEvenClassification.Helpers
