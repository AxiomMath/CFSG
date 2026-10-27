module

public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Data.FunLike.Fintype

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Ident

variable {A : Type} [AddCommGroup A] {G : Type} [Group G]

@[expose] def endRing (ρ : G →* AddMonoid.End A) : Subring (AddMonoid.End A) :=
  Subring.centralizer (Set.range ρ)

theorem mem_endRing {ρ : G →* AddMonoid.End A} {φ : AddMonoid.End A} :
    φ ∈ endRing ρ ↔ ∀ g a, φ (ρ g a) = ρ g (φ a) := by
  unfold endRing
  rw [Subring.mem_centralizer_iff]
  constructor
  · intro h g a
    have := h (ρ g) ⟨g, rfl⟩
    exact (congrArg (fun f : AddMonoid.End A => f a) this).symm
  · rintro h _ ⟨g, rfl⟩
    ext a
    exact (h g a).symm

theorem endRing_injective {ρ : G →* AddMonoid.End A}
    (hsimple : ∀ N : AddSubgroup A, (∀ g, ∀ a ∈ N, ρ g a ∈ N) → N = ⊥ ∨ N = ⊤)
    {φ : AddMonoid.End A} (hφ : φ ∈ endRing ρ) (h0 : φ ≠ 0) : Function.Injective φ := by
  have hφ' := mem_endRing.mp hφ
  let N : AddSubgroup A :=
    { carrier := {a | φ a = 0}
      add_mem' := fun {a b} ha hb => by
        show φ (a + b) = 0
        rw [map_add, show φ a = 0 from ha, show φ b = 0 from hb, add_zero]
      zero_mem' := map_zero φ
      neg_mem' := fun {a} ha => by
        show φ (-a) = 0
        rw [map_neg, show φ a = 0 from ha, neg_zero] }
  have hN : ∀ g, ∀ a ∈ N, ρ g a ∈ N := by
    intro g a ha
    show φ (ρ g a) = 0
    rw [hφ' g a, show φ a = 0 from ha, map_zero]
  rcases hsimple N hN with h | h
  · intro a b hab
    have h1 : a - b ∈ N := by
      show φ (a - b) = 0
      rw [map_sub, hab, sub_self]
    rw [h] at h1
    exact sub_eq_zero.mp ((AddSubgroup.mem_bot).mp h1)
  · exfalso
    apply h0
    ext a
    have : a ∈ N := by rw [h]; trivial
    exact this

variable [Finite A] [Nontrivial A]

theorem exists_endField (ρ : G →* AddMonoid.End A)
    (hsimple : ∀ N : AddSubgroup A, (∀ g, ∀ a ∈ N, ρ g a ∈ N) → N = ⊥ ∨ N = ⊤) :
    ∃ (E : Type) (_ : Field E) (_ : Module E A) (_ : Finite E),
      (∀ (g : G) (c : E) (a : A), ρ g (c • a) = c • ρ g a) ∧
      (∀ φ : A →+ A, (∀ g a, φ (ρ g a) = ρ g (φ a)) → ∃ c : E, ∀ a, φ a = c • a) := by
  let S := endRing ρ
  have hfin : Finite S := by
    have : Finite (AddMonoid.End A) := DFunLike.finite _
    infer_instance
  have hnzd : NoZeroDivisors S := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hx, hy⟩ := hcon
    have hxi := endRing_injective hsimple x.2 (fun h => hx (Subtype.ext h))
    have hyi := endRing_injective hsimple y.2 (fun h => hy (Subtype.ext h))
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    have h1 : ((x * y : S) : AddMonoid.End A) a = 0 := by
      rw [hxy]; rfl
    have h2 : (x : AddMonoid.End A) ((y : AddMonoid.End A) a) = 0 := h1
    apply ha
    apply hyi
    apply hxi
    rw [h2, map_zero, map_zero]
  have hnt : Nontrivial S := by
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    apply ha
    have := congrArg (fun f : S => (f : AddMonoid.End A) a) h
    exact this
  have hdom : IsDomain S := {}
  let F : Field S := (Finite.isDomain_to_isField S).toField
  let M : Module S A :=
    { smul := fun c a => (c : AddMonoid.End A) a
      one_smul := fun a => rfl
      mul_smul := fun c d a => rfl
      smul_zero := fun c => map_zero _
      smul_add := fun c a b => map_add _ a b
      add_smul := fun c d a => rfl
      zero_smul := fun a => rfl }
  refine ⟨S, F, M, hfin, ?_, ?_⟩
  · intro g c a
    exact (mem_endRing.mp c.2 g a).symm
  · intro φ hφ
    exact ⟨⟨φ, mem_endRing.mpr hφ⟩, fun a => rfl⟩

end CFSG.CGT.PushingUpLit.CGT6.Diag.Ident
