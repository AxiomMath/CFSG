module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Equiv Equiv.Perm

section Basic

variable {Ω : Type*}

@[expose] def symOn (F : Finset Ω) : Subgroup (Perm Ω) where
  carrier := {g | ∀ x, x ∉ F → g x = x}
  one_mem' := fun x _ => rfl
  mul_mem' := fun {a b} ha hb x hx => by
    show a (b x) = x
    rw [hb x hx, ha x hx]
  inv_mem' := fun {a} ha x hx => by
    show a⁻¹ x = x
    have := ha x hx
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact this.symm

theorem mem_symOn {F : Finset Ω} {g : Perm Ω} : g ∈ symOn F ↔ ∀ x, x ∉ F → g x = x := Iff.rfl

theorem symOn_mem_iff {F : Finset Ω} {g : Perm Ω} (hg : g ∈ symOn F) (x : Ω) :
    g x ∈ F ↔ x ∈ F := by
  constructor
  · intro h
    by_contra hx
    have h1 := hg x hx
    rw [h1] at h
    exact hx h
  · intro h
    by_contra hx
    have h1 := hg (g x) hx
    exact hx (by rw [g.injective h1]; exact h)

theorem symOn_mono {F F' : Finset Ω} (h : F ⊆ F') : symOn F ≤ symOn F' :=
  fun _ hg x hx => hg x fun hxF => hx (h hxF)

@[expose] noncomputable def symOnEquiv [DecidableEq Ω] (F : Finset Ω) : Perm {x // x ∈ F} ≃* symOn F :=
  MulEquiv.ofBijective
    ((Equiv.Perm.ofSubtype (p := fun x => x ∈ F)).codRestrict (symOn F)
      (fun f x hx => Equiv.Perm.ofSubtype_apply_of_not_mem f hx))
    ⟨fun f g h => Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h), fun g => by
      refine ⟨(g : Perm Ω).subtypePerm (symOn_mem_iff g.2), Subtype.ext ?_⟩
      exact Equiv.Perm.ofSubtype_subtypePerm (symOn_mem_iff g.2)
        (fun x hx => by by_contra h; exact hx (g.2 x h))⟩

end Basic

section Alt

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def altOn (F : Finset Ω) : Subgroup (Perm Ω) := symOn F ⊓ alternatingGroup Ω

theorem mem_altOn {F : Finset Ω} {g : Perm Ω} :
    g ∈ altOn F ↔ (∀ x, x ∉ F → g x = x) ∧ sign g = 1 := by
  rw [altOn, Subgroup.mem_inf, mem_symOn, Equiv.Perm.mem_alternatingGroup]

theorem altOn_mono {F F' : Finset Ω} (h : F ⊆ F') : altOn F ≤ altOn F' :=
  inf_le_inf_right _ (symOn_mono h)

theorem altOn_le_alternatingGroup (F : Finset Ω) : altOn F ≤ alternatingGroup Ω := inf_le_right

theorem altOn_le_symOn (F : Finset Ω) : altOn F ≤ symOn F := inf_le_left

@[expose] noncomputable def altOnEquiv (F : Finset Ω) : alternatingGroup {x // x ∈ F} ≃* altOn F :=
  MulEquiv.ofBijective
    (((Equiv.Perm.ofSubtype (p := fun x => x ∈ F)).comp
        (alternatingGroup {x // x ∈ F}).subtype).codRestrict
      (altOn F) (fun f => by
        refine mem_altOn.2 ⟨fun x hx => Equiv.Perm.ofSubtype_apply_of_not_mem _ hx, ?_⟩
        show sign (Equiv.Perm.ofSubtype (f : Perm {x // x ∈ F})) = 1
        rw [Equiv.Perm.sign_ofSubtype]
        exact Equiv.Perm.mem_alternatingGroup.1 f.2))
    ⟨fun f g h => by
      apply Subtype.ext
      apply Equiv.Perm.ofSubtype_injective (p := fun x => x ∈ F)
      exact congrArg Subtype.val h, fun g => by
      have hg := mem_altOn.1 g.2
      have hs : g.1 ∈ symOn F := hg.1
      refine ⟨⟨(g : Perm Ω).subtypePerm (symOn_mem_iff hs), ?_⟩, Subtype.ext ?_⟩
      · rw [Equiv.Perm.mem_alternatingGroup]
        have := Equiv.Perm.sign_ofSubtype ((g : Perm Ω).subtypePerm (symOn_mem_iff hs))
        rw [Equiv.Perm.ofSubtype_subtypePerm (symOn_mem_iff hs)
          (fun x hx => by by_contra h; exact hx (hg.1 x h))] at this
        rw [← this]
        exact hg.2
      · exact Equiv.Perm.ofSubtype_subtypePerm (symOn_mem_iff hs)
          (fun x hx => by by_contra h; exact hx (hg.1 x h))⟩

theorem isSimpleGroup_altOn {F : Finset Ω} (hF : 5 ≤ F.card) : IsSimpleGroup (altOn F) := by
  have h : IsSimpleGroup (alternatingGroup {x // x ∈ F}) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hF)
  exact (altOnEquiv F).isSimpleGroup_congr.1 h

end Alt

end CFSG.GH74.GLS.IVK.GHInv
