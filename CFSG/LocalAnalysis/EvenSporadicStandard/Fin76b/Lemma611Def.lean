module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Rest7

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

structure EFacts611 {G : Type*} [Group G] (E : Subgroup G) (t : G) : Prop where
  gen_four : ∃ a b c d : G, Subgroup.closure ({a, b, c, d} : Set G) = E
  orbit_pairs : ∀ A : Subgroup (MulAut ↥E), A.index ≤ 2 → ∀ x y x' y' : ↥E,
    (x : G) * x = 1 → (x : G) ≠ 1 → (x : G) ≠ t → (y : G) * y = 1 → (y : G) ≠ 1 →
      (y : G) ≠ t → (x : G) * y ≠ y * x →
    (x' : G) * x' = 1 → (x' : G) ≠ 1 → (x' : G) ≠ t → (y' : G) * y' = 1 → (y' : G) ≠ 1 →
      (y' : G) ≠ t → (x' : G) * y' ≠ y' * x' →
    ∃ φ ∈ A, φ x = x' ∧ φ y = y'

@[expose] def Fin76bEFacts611 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B → EFacts611 E t

end CFSG.EvenSporadicStandard.Fin76b
