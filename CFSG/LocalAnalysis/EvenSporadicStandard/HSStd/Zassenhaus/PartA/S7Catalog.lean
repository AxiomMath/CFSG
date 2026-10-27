module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.Wreath

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open
open CFSG.EvenSporadicStandard.HSStd

@[expose] def SigmaConfig {X : Type} [Group X] (t y c k : X) : Prop :=
  orderOf y = 3 ∧ y ∈ centralizerDerived t ∧ orderOf c = 3 ∧ k * k = 1 ∧ k ≠ 1 ∧
    y * c = c * y ∧ y * (t * c * t⁻¹) = (t * c * t⁻¹) * y ∧
    c * (t * c * t⁻¹) = (t * c * t⁻¹) * c ∧ y * k = k * y ∧
    Nat.card ↥(Subgroup.closure ({y, c, t * c * t⁻¹} : Set X)) = 27 ∧
    k * c * k⁻¹ = c⁻¹ ∧ k * (t * c * t⁻¹) = (t * c * t⁻¹) * k ∧
    k * (t * k * t⁻¹) = (t * k * t⁻¹) * k

@[expose] def U43Config : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X) [N.Normal],
    LieModel ↥N .PSU 4 3 1 → centralizer (N : Set X) = ⊥ →
    ∀ t : X, orderOf t = 2 →
      Nonempty (↥(centralizer ({t} : Set X)) ≃*
        Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) →
      ∀ y c k : X, SigmaConfig t y c k →
        Nat.card ↥(centralizer ({y} : Set X)) = 1944 ∧
          Nat.card ↥(centralizer ({y, c, t * c * t⁻¹, k, t * k * t⁻¹} : Set X)) = 3

@[expose] def HarrisL39L43NoD8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal → centralizer (N : Set G) = ⊥ →
    (LieModel ↥N .PSL 3 3 2 ∨ LieModel ↥N .PSL 4 3 1) →
    ∀ t : G, orderOf t = 2 →
    Nonempty (↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) →
    ∀ y ∈ centralizerDerived t, orderOf y = 3 → ¬ 8 ∣ Nat.card ↥(centralizer ({y} : Set G))

@[expose] def U43CoverOrbit : Prop :=
  ∀ (T X : Type) [Group T] [Finite T] [Group X] [Finite X] (κ : T →* X), Function.Surjective κ →
    ∀ (E : Subgroup T) [E.Normal], ⁅E, E⁆ = E → (∀ a ∈ E, κ a = 1 → ∀ b ∈ E, a * b = b * a) →
    LieModel ↥(E.map κ) .PSU 4 3 1 → centralizer ((E.map κ : Subgroup X) : Set X) = ⊥ →
    ∀ t : T, orderOf (κ t) = 2 →
      Nonempty (↥(centralizer ({κ t} : Set X)) ≃*
        Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) →
      ∀ y ∈ E, orderOf y = 3 → κ y ∈ centralizerDerived (κ t) →
        Nat.card ↥(centralizer ({κ y} : Set X)) = 1944 →
        {w : T | ∃ g : T, κ g ∈ centralizer ({κ y} : Set X) ∧ w = g * y * g⁻¹}.ncard ≤ 8

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
