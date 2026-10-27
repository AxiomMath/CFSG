module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ClsMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.NonIso

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Wong77

open CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Wong77.Module

theorem module_dichotomy {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (hV : Nat.card V = 2 ^ 11)
    (ρ : Carrier .M23 →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ) :
    (∃ F : V ≃ₗ[ZMod 2] Cocode, ∀ (g : Carrier .M23) (v : V), F (ρ g v) = cocodeRep g (F v)) ∨
    (∃ F : V ≃ₗ[ZMod 2] ↥golayEven,
      ∀ (g : Carrier .M23) (v : V), F (ρ g v) = golayRep g (F v)) := by
  rcases Cls.exists_isomorphic_pair hV natCard_cocode natCard_golayEvenMod ρ hρ cocodeRep
    cocodeRep_injective golayRep golayRep_injective with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (not_equivariant_equiv h).elim

end CFSG.EvenSporadicStandard.Wong77
