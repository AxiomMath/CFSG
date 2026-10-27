module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.ComponentClassification.LBalance

open Subgroup

@[expose] def SchreierSections (X : Type*) [Group X] : Prop :=
  ∀ (A B : Subgroup X), B ≤ A → ∀ [(B.subgroupOf A).Normal],
    IsSimpleGroup (A ⧸ B.subgroupOf A) →
    (∃ a b : A ⧸ B.subgroupOf A, a * b ≠ b * a) →
    Group.IsSolvable (OuterAutomorphisms.Outer (A ⧸ B.subgroupOf A))

namespace SchreierSections

variable {X Y : Type*} [Group X] [Group Y]

theorem outer_solvable (hX : SchreierSections X) (A : Subgroup X) {S : Type*} [Group S]
    [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) (f : A →* S)
    (hf : Function.Surjective f) : Group.IsSolvable (OuterAutomorphisms.Outer S) := by
  let B : Subgroup X := f.ker.map A.subtype
  have hB : B.subgroupOf A = f.ker := comap_map_eq_self_of_injective A.subtype_injective _
  have : (B.subgroupOf A).Normal := by
    rw [hB]
    infer_instance
  let e : A ⧸ B.subgroupOf A ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hB).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have : IsSimpleGroup (A ⧸ B.subgroupOf A) := e.isSimpleGroup
  have hnc : ∃ a b : A ⧸ B.subgroupOf A, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hS
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have := hX A B (map_subtype_le _) inferInstance hnc
  exact OuterAutomorphisms.solvable_of_equiv e

theorem of_injective (hY : SchreierSections Y) (f : X →* Y) (hf : Function.Injective f) :
    SchreierSections X := by
  intro A B _ _ _ hnc
  let e : A ≃* A.map f := A.equivMapOfInjective f hf
  exact hY.outer_solvable (A.map f) hnc
    ((QuotientGroup.mk' (B.subgroupOf A)).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp e.symm.surjective)

theorem of_surjective (hX : SchreierSections X) (f : X →* Y) (hf : Function.Surjective f) :
    SchreierSections Y := by
  intro A B _ _ _ hnc
  let g : A.comap f →* A := (f.comp (A.comap f).subtype).codRestrict A fun x => x.2
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨x, hx⟩ := hf a
    exact ⟨⟨x, show f x ∈ A from hx ▸ a.2⟩, Subtype.ext hx⟩
  exact hX.outer_solvable (A.comap f) hnc ((QuotientGroup.mk' (B.subgroupOf A)).comp g)
    ((QuotientGroup.mk'_surjective _).comp hg)

theorem subgroup (hX : SchreierSections X) (H : Subgroup X) : SchreierSections H :=
  hX.of_injective H.subtype H.subtype_injective

theorem quotient (hX : SchreierSections X) (N : Subgroup X) [N.Normal] :
    SchreierSections (X ⧸ N) :=
  hX.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem outer_component (hX : SchreierSections X) (K : Subgroup X) (hK : IsComponent K) :
    Group.IsSolvable (OuterAutomorphisms.Outer (K ⧸ center K)) := by
  have : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
  exact hX.outer_solvable K hK.1.2.2 (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective _)

theorem outer_component_of_quotient (hX : SchreierSections X) (N : Subgroup X) [N.Normal]
    (H : Subgroup (X ⧸ N)) (K : Subgroup H) (hK : IsComponent K) :
    Group.IsSolvable (OuterAutomorphisms.Outer (K ⧸ center K)) :=
  ((hX.quotient N).subgroup H).outer_component K hK

theorem of_isKGroup
    (hS : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      Open.IsCatalogGroup S → Group.IsSolvable (OuterAutomorphisms.Outer S))
    {X : Type} [Group X] [Finite X] (hK : Open.IsKGroup X) : SchreierSections X := by
  intro A B hBA _ hsimple hnc
  exact hS _ hnc (hK A B hBA hsimple hnc)

end SchreierSections

end CFSG.ComponentClassification.LBalance
