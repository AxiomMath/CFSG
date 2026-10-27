module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Inputs
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic

@[expose] def WreathData {G : Type} [Group G] (z : G) : Prop :=
  ∃ R : Subgroup G, Nat.card R = 2 ^ 10 ∧
    (∀ a ∈ R, ∀ b ∈ R, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a) ∧
    ∀ a ∈ R, z * a * z⁻¹ ∈ R → a = 1

@[expose] def Ega81Wreath : Prop :=
  Ega81HypAZ2A8K → ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), KLocalSections G →
    fusionZStar G = ⊥ → standardComponentIsStandard A → IsSporadic A .M24 →
    (∃ S : Sylow 2 (centralizer (A : Set G)), IsCyclic S) →
    (∀ S : Sylow 2 (centralizer (A : Set G)), Nat.card S = 2) →
    (∀ z : G, z ∈ centralizer (A : Set G) → orderOf z = 2 →
      centralizer ({z} : Set G) = A ⊔ zpowers z ∧ CaseTwo A z) →
    ∃ z : G, z ∈ centralizer (A : Set G) ∧ orderOf z = 2 ∧ WreathData z

end CFSG.EvenSporadicStandard.M24Std
