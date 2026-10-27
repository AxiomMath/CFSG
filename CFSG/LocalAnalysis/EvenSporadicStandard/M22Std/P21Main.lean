module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Cases
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21L52
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Orders
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutProp21

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std

@[expose] def Prop21A6A6Case : Prop :=
  ∀ (V : Type) [Group V], (∀ x y : V, x * y = y * x) → (∀ x : V, x * x = 1) →
    Nat.card V = 256 → ∀ (G : Type) [Group G] [Finite G] (ρ : G →* MulAut V),
    Function.Injective ρ → ∀ z : G, orderOf z = 2 →
    Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) →
    Nonempty (egaLayer (G ⧸ fusionOddCore G) ≃*
      alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) →
    Nonempty (egaLayer G ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) ∧
      ∃ f : G →* Equiv.Perm (Fin 2 × Fin 6), Function.Injective f ∧ ∀ g, f g ∈ wreathS6Z2

@[expose] def Prop21Sp44Case : Prop :=
  ∀ (V : Type) [Group V], (∀ x y : V, x * y = y * x) → (∀ x : V, x * x = 1) →
    Nat.card V = 256 → ∀ (G : Type) [Group G] [Finite G] (ρ : G →* MulAut V),
    Function.Injective ρ → ∀ z : G, orderOf z = 2 →
    Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) →
    LieModel (egaLayer (G ⧸ fusionOddCore G)) .PSp 2 2 2 →
    LieModel (egaLayer G) .PSp 2 2 2 ∧
      z ∉ egaLayer G ⊔ centralizer (egaLayer G : Set G) ∧
      Nonempty (↥(egaLayer G ⊓ centralizer ({z} : Set G)) ≃* Equiv.Perm (Fin 6))

theorem fin77aProp21K_of_harrisSolomonK_of_cases
    (hHS : HarrisSolomonZ2S6IsoK) (hA6A6 : Prop21A6A6Case) (hSp44 : Prop21Sp44Case) :
    Fin77aProp21K := by
  intro V _ hcomm hsq hcard G _ _ hKG ρ hρ z hz hC
  have hG : Nat.card G ∣ gl8 := card_dvd_gl8 hcomm hsq hcard ρ hρ
  rcases hHS G hKG z hz (centralizer_quot_oddCore_equiv hC) with
    h6 | h66 | h8 | hU42 | hL52 | hU52 | hS44 | hU43
  · exact Or.inl (mem_fusionZStar_of_layer_alt6 hz hC h6)
  · exact Or.inr (Or.inl (hA6A6 V hcomm hsq hcard G ρ hρ z hz hC h66))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (prop21_a8 hz hC hG h8))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (prop21_u42 hz hC hG hU42))))
  · let : CommGroup V := { ‹Group V› with mul_comm := hcomm }
    exact (false_of_layer_psl52 hz hC hG hsq hcard ρ hρ hL52).elim
  · exact (false_of_layer_psu52 hG hU52).elim
  · exact Or.inr (Or.inr (Or.inl (hSp44 V hcomm hsq hcard G ρ hρ z hz hC hS44)))
  · exact (false_of_layer_psu43 hG hU43).elim

end CFSG.EvenSporadicStandard.M22Std
