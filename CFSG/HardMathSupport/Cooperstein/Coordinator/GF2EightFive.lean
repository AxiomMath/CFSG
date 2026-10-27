module

public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Open.QuasithinDefs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo

@[expose] def IsAltNaturalSection {V : Type} [CommGroup V] (L : Subgroup (MulAut V))
    (U : Subgroup V) (n : ℕ) : Prop :=
  ∃ α : ↥L →* alternatingGroup (Fin n), Function.Surjective α ∧
  ∃ π : ↥U →* Multiplicative (altHeart n), Function.Surjective π ∧
    π.ker = (U ⊓ fixV L).subgroupOf U ∧
    ∀ (l : ↥L) (u v : ↥U), (v : V) = (l : MulAut V) (u : V) → ∀ x : evenWeight n,
      Multiplicative.toAdd (π u) = (x : altHeart n) →
      Multiplicative.toAdd (π v) = (evenWeightPerm (α l : Equiv.Perm (Fin n)) x : altHeart n)

@[expose] def GF2EightFive : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ H L : Subgroup (MulAut V), L = quasithinGenFitting H → ∀ n : ℕ, (n = 7 ∨ 9 ≤ n) →
      Nonempty (↥L ≃* alternatingGroup (Fin n)) → (∃ A, IsFFStarOffender H A) →
        IsAltNaturalSection L (commV H) n ∨ (n = 7 ∧ H = L ∧ Nat.card (commV H) = 2 ^ 4)

@[expose] def GF2NoFFTripleA7 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ H L : Subgroup (MulAut V), L = quasithinGenFitting H → CFSG.IsQuasisimple ↥L →
      Nat.card (Subgroup.center ↥L) = 3 →
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 7)) →
        ∀ A : Subgroup (MulAut V), ¬ IsFFStarOffender H A

end CFSG.HardMathSupport.Cooperstein.Coordinator
