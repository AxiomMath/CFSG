module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

theorem isCyclic_of_irreducible_abelian {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V] (O : Subgroup (V ≃ₗ[ZMod 2] V))
    (hab : ∀ a ∈ O, ∀ b ∈ O, a * b = b * a)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ g ∈ O, Stable g U) → U = ⊥ ∨ U = ⊤) : IsCyclic O := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V)) DFunLike.coe_injective
  haveI : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  rcases subsingleton_or_nontrivial V with hV | hV
  · haveI : Subsingleton (V ≃ₗ[ZMod 2] V) :=
      ⟨fun f g => LinearEquiv.ext fun v => Subsingleton.elim _ _⟩
    haveI : Subsingleton O := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    infer_instance
  let S : Set (Module.End (ZMod 2) V) :=
    (fun g : V ≃ₗ[ZMod 2] V => (g : V →ₗ[ZMod 2] V)) '' (O : Set (V ≃ₗ[ZMod 2] V))
  have hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨k, hk, rfl⟩
    ext v
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) (hab g hg k hk)
    simpa using this
  let A : Subalgebra (ZMod 2) (Module.End (ZMod 2) V) := Algebra.adjoin (ZMod 2) S
  letI : CommRing A :=
    Algebra.adjoinCommRingOfComm (ZMod 2) (fun a ha b hb _ => hSc a ha b hb)
  have hcommA : ∀ g ∈ O, ∀ b : A, ((g : V →ₗ[ZMod 2] V) : Module.End (ZMod 2) V) * b = b * g := by
    intro g hg b
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute b.2
      (fun c hc => (hSc _ ⟨g, hg, rfl⟩ c hc))).eq
  have hnt : Nontrivial A := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 : ((0 : A) : Module.End (ZMod 2) V) = ((1 : A) : Module.End (ZMod 2) V) :=
      congrArg Subtype.val h
    have := congrArg (fun f : Module.End (ZMod 2) V => f v) h1
    exact hv (by simpa using this.symm)
  haveI : NoZeroDivisors A := by
    refine ⟨fun {a b} hab0 => ?_⟩
    by_cases hb0 : b = 0
    · exact Or.inr hb0
    · left
      have hker : ∀ g ∈ O, Stable g (LinearMap.ker (b : Module.End (ZMod 2) V)) := by
        intro g hg v hv
        rw [LinearMap.mem_ker] at hv ⊢
        have h1 := hcommA g hg b
        calc (b : Module.End (ZMod 2) V) (g v)
            = ((b : Module.End (ZMod 2) V) * (g : V →ₗ[ZMod 2] V)) v := rfl
          _ = ((g : V →ₗ[ZMod 2] V) * (b : Module.End (ZMod 2) V)) v := by rw [h1]
          _ = g ((b : Module.End (ZMod 2) V) v) := rfl
          _ = 0 := by rw [hv, map_zero]
      rcases hirr _ hker with h | h
      · have hinj : Function.Injective (b : Module.End (ZMod 2) V) := LinearMap.ker_eq_bot.mp h
        have hsurj : Function.Surjective (b : Module.End (ZMod 2) V) :=
          LinearMap.injective_iff_surjective.mp hinj
        apply Subtype.ext
        ext v
        obtain ⟨w, rfl⟩ := hsurj v
        have : (((a * b : A)) : Module.End (ZMod 2) V) w = 0 := by rw [hab0]; rfl
        simpa using this
      · exfalso
        apply hb0
        apply Subtype.ext
        ext v
        have : v ∈ LinearMap.ker (b : Module.End (ZMod 2) V) := by rw [h]; trivial
        simpa using this
  haveI : IsDomain A := NoZeroDivisors.to_isDomain A
  haveI : Finite A := Subtype.finite
  let φ : O →* A :=
    { toFun := fun g => ⟨((g : V ≃ₗ[ZMod 2] V) : Module.End (ZMod 2) V),
        Algebra.subset_adjoin ⟨g, g.2, rfl⟩⟩
      map_one' := by apply Subtype.ext; rfl
      map_mul' := fun g k => by apply Subtype.ext; rfl }
  refine isCyclic_of_injective_ringHom φ ?_
  intro g k hgk
  have h1 : ((g : V ≃ₗ[ZMod 2] V) : Module.End (ZMod 2) V) =
      ((k : V ≃ₗ[ZMod 2] V) : Module.End (ZMod 2) V) := congrArg Subtype.val hgk
  exact Subtype.ext (LinearEquiv.toLinearMap_injective h1)

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
