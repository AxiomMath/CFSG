module

public import CFSG.LieType.Chevalley.NativeRoots
public import CFSG.Blueprint.ChevalleyInfinitesimals
public import CFSG.Blueprint.ChevalleyWeyl
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

structure RootOperatorFamily (τ : Tag) where
  D : (R : Type) → [CommRing R] → Root τ → ℕ → Module.End R (RootModule τ R)
  D_zero : ∀ (R : Type) [CommRing R] (α : Root τ), D R α 0 = 1
  D_eq_zero : ∀ (R : Type) [CommRing R] (α : Root τ) (k : ℕ), 4 ≤ k → D R α k = 0
  D_simple : ∀ (R : Type) [CommRing R] (j : Fin τ.rank) (k : ℕ),
    D R (simpleRoot τ j) k = xCoeff τ R j k
  D_neg_simple : ∀ (R : Type) [CommRing R] (j : Fin τ.rank) (k : ℕ),
    D R (-simpleRoot τ j) k = yCoeff τ R j k
  sign : Fin τ.rank → Root τ → ℤ
  sign_eq : ∀ (i : Fin τ.rank) (α : Root τ), sign i α = 1 ∨ sign i α = -1
  conj : ∀ (R : Type) [CommRing R] (i : Fin τ.rank) (α : Root τ) (k : ℕ),
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * D R α k =
      ((sign i α ^ k : ℤ) : R) • (D R (simple τ i • α) k *
        (weylElt τ R i 1 : Module.End R (RootModule τ R)))

end CFSG.LieType.Chevalley
