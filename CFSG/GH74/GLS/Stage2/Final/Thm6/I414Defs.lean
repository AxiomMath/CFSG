module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.I414

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def IsSectionOf (S : Type*) (Y : Type*) [Group S] [Group Y] : Prop :=
  ∃ (Y1 : Subgroup Y) (f : ↥Y1 →* S), Function.Surjective f

@[expose] def HasPropS (Y : Type*) [Group Y] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsSectionOf S Y → Group.IsSolvable (Outer S)

namespace IsSectionOf

variable {H S T Y : Type*} [Group H] [Group S] [Group T] [Group Y]

theorem of_hom (i : H →* Y) (hi : Function.Injective i) (f : H →* S)
    (hf : Function.Surjective f) : IsSectionOf S Y := by
  let e : H ≃* i.range := MonoidHom.ofInjective hi
  exact ⟨i.range, f.comp e.symm.toMonoidHom, hf.comp e.symm.surjective⟩

theorem of_surjective (f : Y →* S) (hf : Function.Surjective f) : IsSectionOf S Y :=
  of_hom (MonoidHom.id Y) Function.injective_id f hf

theorem of_injective (f : S →* Y) (hf : Function.Injective f) : IsSectionOf S Y :=
  of_hom f hf (MonoidHom.id S) Function.surjective_id

theorem subgroup (U : Subgroup Y) : IsSectionOf ↥U Y :=
  of_injective U.subtype U.subtype_injective

theorem map (f : Y →* S) (U : Subgroup Y) : IsSectionOf ↥(U.map f) ↥U :=
  of_surjective (f.subgroupMap U) (f.subgroupMap_surjective U)

theorem trans (h₁ : IsSectionOf T S) (h₂ : IsSectionOf S Y) : IsSectionOf T Y := by
  obtain ⟨S1, g, hg⟩ := h₁
  obtain ⟨Y1, f, hf⟩ := h₂
  let V : Subgroup ↥Y1 := S1.comap f
  let fS : ↥V →* ↥S1 := (f.comp V.subtype).codRestrict S1 fun x => x.2
  refine of_hom (Y1.subtype.comp V.subtype)
    (Y1.subtype_injective.comp V.subtype_injective) (g.comp fS) ?_
  intro t
  obtain ⟨s, hs⟩ := hg t
  obtain ⟨y, hy⟩ := hf (s : S)
  have hyV : y ∈ V := by
    change f y ∈ S1
    rw [hy]
    exact s.2
  refine ⟨⟨y, hyV⟩, ?_⟩
  have : fS ⟨y, hyV⟩ = s := Subtype.ext hy
  simp only [MonoidHom.comp_apply, this, hs]

theorem of_le {U V : Subgroup Y} (h : U ≤ V) : IsSectionOf ↥U ↥V :=
  of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

end IsSectionOf

namespace HasPropS

variable {Y Z : Type*} [Group Y] [Group Z]

theorem of_isSectionOf (h : IsSectionOf Z Y) (hY : HasPropS Y) : HasPropS Z :=
  fun S _ _ hs hn hSZ => hY S hs hn (hSZ.trans h)

theorem of_le {U V : Subgroup Y} (h : U ≤ V) (hV : HasPropS ↥V) : HasPropS ↥U :=
  of_isSectionOf (IsSectionOf.of_le h) hV

theorem map (f : Y →* Z) (U : Subgroup Y) (hU : HasPropS ↥U) : HasPropS ↥(U.map f) :=
  of_isSectionOf (IsSectionOf.map f U) hU

end HasPropS

end CFSG.GH74.GLS.Stage2.Final.Thm6.I414
