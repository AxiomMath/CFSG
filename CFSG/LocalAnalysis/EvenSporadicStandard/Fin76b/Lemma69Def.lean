
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma66

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

structure EFacts69 {G : Type*} [Group G] (E : Subgroup G) (t : G) : Prop where
  sq : ∀ e ∈ E, e * e = 1 ∨ e * e = t
  card_two : Set.ncard {e : G | e ∈ E ∧ e * e = 1 ∧ e ≠ 1 ∧ e ≠ t} = 10
  card_four : Set.ncard {e : G | e ∈ E ∧ e * e = t} = 20
  anti_two : ∀ x ∈ E, x * x = 1 → x ≠ 1 → x ≠ t →
    Set.ncard {y : G | y ∈ E ∧ y * y = 1 ∧ y ≠ 1 ∧ y ≠ t ∧ y * x ≠ x * y} = 8
  anti_four : ∀ x ∈ E, x * x = 1 → x ≠ 1 → x ≠ t →
    Set.ncard {y : G | y ∈ E ∧ y * y = t ∧ y * x ≠ x * y} = 8
  card_aut : Nat.card (MulAut ↥E) ≤ 1920
  orbit_two : ∀ A : Subgroup (MulAut ↥E), A.index ≤ 2 → ∀ x y : ↥E,
    (x : G) * x = 1 → (x : G) ≠ 1 → (x : G) ≠ t → (y : G) * y = 1 → (y : G) ≠ 1 → (y : G) ≠ t →
      ∃ φ ∈ A, φ x = y
  orbit_four : ∀ A : Subgroup (MulAut ↥E), A.index ≤ 2 → ∀ x y : ↥E,
    (x : G) * x = t → (y : G) * y = t → ∃ φ ∈ A, φ x = y

@[expose] def Fin76bEFacts69 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B → EFacts69 E t

@[expose] def Fin76bFusion69 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → BetaData65 E β →
    (∃ hz : z ∈ centralizer ({β} : Set G),
      WreathAlt ↥(centralizer ({β} : Set G)) (QuotientGroup.mk ⟨z, hz⟩)) →
    ∃ e ∈ E, e * e = 1 ∧ e ≠ 1 ∧ e ≠ t ∧ ∃ g : G, g * z * g⁻¹ = z * e

end CFSG.EvenSporadicStandard.Fin76b
