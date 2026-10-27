module

public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.MappedCenter

theorem contained {G : Type*} [Group G] (ambient : Subgroup G) :
    (Subgroup.center ambient).map ambient.subtype ≤ ambient := Subgroup.map_subtype_le _

theorem centralizes {G : Type*} [Group G] (ambient : Subgroup G) :
    (Subgroup.center ambient).map ambient.subtype ≤ Subgroup.centralizer (ambient : Set G) := by
  rintro member ⟨lift, hlift, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro other hother
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hlift (⟨other, hother⟩ : ambient))

theorem conjugate_le {G : Type*} [Group G]
    (ambient subgroup : Subgroup G)
    (hcentral : subgroup ≤ (Subgroup.center ambient).map ambient.subtype)
    (actor : G) (hactor : actor ∈ Subgroup.normalizer (ambient : Set G)) :
    subgroup.map (MulAut.conj actor).toMonoidHom ≤ (Subgroup.center ambient).map ambient.subtype := by
  rintro member ⟨lift, hlift, rfl⟩
  have hliftAmbient := contained ambient (hcentral hlift)
  have hconjugate : actor * lift * actor⁻¹ ∈ ambient :=
    (Subgroup.mem_normalizer_iff.mp hactor lift).mp hliftAmbient
  refine Subgroup.mem_map.mpr ⟨⟨actor * lift * actor⁻¹, hconjugate⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  intro other
  apply Subtype.ext
  have hotherBack : actor⁻¹ * other.val * actor ∈ ambient :=
    (Subgroup.mem_normalizer_iff''.mp hactor other.val).mp other.property
  have hcommutes := Subgroup.mem_centralizer_iff.mp (centralizes ambient (hcentral hlift)) _ hotherBack
  have hmap := congrArg (fun member : G => actor * member * actor⁻¹) hcommutes
  change other.val * (actor * lift * actor⁻¹) = (actor * lift * actor⁻¹) * other.val
  convert hmap using 1 <;> group

theorem commute {G : Type*} [Group G] (ambient first second : Subgroup G)
    (hfirst : first ≤ (Subgroup.center ambient).map ambient.subtype)
    (hsecond : second ≤ (Subgroup.center ambient).map ambient.subtype) : ⁅first, second⁆ = ⊥ := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro member hmember
  apply Subgroup.mem_centralizer_iff.mpr
  intro other hother
  exact Subgroup.mem_centralizer_iff.mp (centralizes ambient (hfirst hmember)) other (contained ambient (hsecond hother))

end CFSG.ComponentClassification.MappedCenter
