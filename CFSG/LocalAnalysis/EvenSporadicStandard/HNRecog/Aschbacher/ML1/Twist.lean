module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GramBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def twist (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (β : A5 ≃* A5) :
    A5 × A5 →* (V ≃ₗ[ZMod 2] V) :=
  σ.comp (MonoidHom.prodMap (MonoidHom.id A5) β.toMonoidHom)

theorem twist_apply (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (β : A5 ≃* A5) (x y : A5) :
    twist σ β (x, y) = σ (x, β y) :=
  rfl

theorem Swap.StdHyp.twist {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)} (hS : Swap.StdHyp σ) (β : A5 ≃* A5) :
    Swap.StdHyp (ML1.twist σ β) := by
  refine ⟨?_, hS.finrank_eq, ?_⟩
  · intro g g' h
    have h1 := hS.inj h
    have h2 : ((g.1, β g.2) : A5 × A5) = (g'.1, β g'.2) := h1
    obtain ⟨e1, e2⟩ := Prod.mk.inj h2
    exact Prod.ext e1 (β.injective e2)
  · intro U hU
    refine hS.irr U fun g u hu => ?_
    obtain ⟨y, hy⟩ := β.surjective g.2
    have := hU (g.1, y) u hu
    rwa [twist_apply, hy] at this

theorem FormHyp.twist {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)} {B : LinearMap.BilinForm (ZMod 2) V}
    (hF : FormHyp σ B) (β : A5 ≃* A5) : FormHyp (ML1.twist σ β) B :=
  ⟨fun g u u' => hF.inv _ u u', hF.alt, hF.nondeg⟩

end CFSG.EvenSporadicStandard.HNRecog.ML1
