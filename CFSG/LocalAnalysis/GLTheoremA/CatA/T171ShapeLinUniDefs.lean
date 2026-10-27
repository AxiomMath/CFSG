module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeWSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

@[expose] def LinMarking : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (N n : ℕ),
    WSetup p L J A d b →
    catalogIs (PSimple p L)
      (onLie fun i => ∃ q : TauCeti.PrimePower, i = .A (N - 1) q ∧ q.card = 2 ^ n) →
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K),
        ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
          Set.univ, LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ

@[expose] def UniMarking : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (N n : ℕ),
    WSetup p L J A d b →
    catalogIs (PSimple p L)
      (onLie fun i => ∃ q : TauCeti.PrimePower, i = .twistedA (N - 1) q ∧ q.card = 2 ^ n) →
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : UnitaryFieldData 2 n K)
      (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n K N)),
      ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K N))
        (LargeEvenGUSet (Fin N) K (2 ^ n)),
        LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
