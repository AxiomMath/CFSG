module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2S6Socle
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Data

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def CatZ2S6 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (S : Subgroup K), S.Normal → IsSimpleGroup ↥S →
    Catalog ↥S → centralizer (S : Set K) = ⊥ → ∀ z : K, orderOf z = 2 →
    Nonempty (↥(centralizer ({z} : Set K)) ⧸ fusionOddCore ↥(centralizer ({z} : Set K)) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) →
    Z2S6Socle ↥S

@[expose] def EvenLieInvolutionTwoConstrained : Prop :=
  ∀ (S : Type) [Group S] [Finite S], EvenLieType S → ∀ t : S, orderOf t = 2 →
    centralizer ((CFSG.pCore 2 ↥(centralizer ({t} : Set S)) : Subgroup _) :
        Set ↥(centralizer ({t} : Set S))) ≤ CFSG.pCore 2 ↥(centralizer ({t} : Set S))

@[expose] def OddLieA6TwoComponent : Prop :=
  ∀ (S : Type) [Group S] [Finite S], OddLieType S → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ J : Subgroup ↥(fixedSubgroup σ), IsPComponent 2 J →
    Nonempty (↥J ⧸ fusionOddCore ↥J ≃* alternatingGroup (Fin 6)) →
    Nonempty (↥J ≃* alternatingGroup (Fin 6))

@[expose] def EvenOuterA6LeafMod : Prop :=
  ∀ (S : Type) [Group S] [Finite S], EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 →
    σ ∉ (MulAut.conj : S →* MulAut S).range → ∀ J : Subgroup ↥(fixedSubgroup σ),
    KForm.Mod.Z2S6ModData S σ J → Z2S6Socle S

@[expose] def SporadicZ2S6Leaf : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (S : Subgroup K), S.Normal → IsSimpleGroup ↥S →
    centralizer (S : Set K) = ⊥ → NativeSporadic.SporadicRep ↥S →
    ∀ z : K, orderOf z = 2 →
    Nonempty (↥(centralizer ({z} : Set K)) ⧸ fusionOddCore ↥(centralizer ({z} : Set K)) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) → False

end CFSG.EvenSporadicStandard.M24Std
