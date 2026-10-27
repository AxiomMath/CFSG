module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenTypeOne
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

@[expose] def LinFieldTypeA0Bound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p N n : ℕ) (L J A : Subgroup G) (d b : G)
    (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → 3 ≤ N →
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K)) →
    (hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) Set.univ,
      LargeEvenInduces θ (conjRel a) φ) →
    (hS : (Set.univ : Set (GL (Fin N) K)) ⊆ Subgroup.normalizer
      (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) →
    (hsetup : Setup p L J A d b) →
    ∀ M : LiftMap (L := L) (A := A) (S := Set.univ) θ hact hS,
      ∀ lam : Kˣ, (M.mat ⟨d, hsetup.d_mem⟩) ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin N) lam →
      (∀ c : Kˣ, c ^ p ≠ lam) →
      ∀ A₀ : Subgroup G, ∀ (hA₀A : A₀ ≤ A),
        (∀ a (ha : a ∈ A₀), M.mat ⟨a, hA₀A ha⟩ * M.mat ⟨d, hsetup.d_mem⟩ =
          M.mat ⟨d, hsetup.d_mem⟩ * M.mat ⟨a, hA₀A ha⟩) →
        Nat.card A₀ ≤ p ^ (N / p)

@[expose] def UniFieldTypeA0Bound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p N n : ℕ) (L J A : Subgroup G) (d b : G)
    (K : Type) [Field K] [Finite K] (h : UnitaryFieldData 2 n K),
    3 ≤ N → (N, 2 ^ n) ≠ (3, 2) → p ∣ 2 ^ n + 1 →
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n K N)) →
    (hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 n K N)) (LargeEvenGUSet (Fin N) K (2 ^ n)),
      LargeEvenInduces θ (conjRel a) φ) →
    (hS : LargeEvenGUSet (Fin N) K (2 ^ n) ⊆ Subgroup.normalizer
      (unitarySU 2 n K N : Set (GL (Fin N) K))) →
    (hsetup : Setup p L J A d b) →
    ∀ M : LiftMap (L := L) (A := A) (S := LargeEvenGUSet (Fin N) K (2 ^ n)) θ hact hS,
      ∀ lam : Kˣ, (M.mat ⟨d, hsetup.d_mem⟩) ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin N) lam →
      (∀ c : Kˣ, c ^ p ≠ lam) →
      ∀ A₀ : Subgroup G, ∀ (hA₀A : A₀ ≤ A),
        (∀ a (ha : a ∈ A₀), M.mat ⟨a, hA₀A ha⟩ * M.mat ⟨d, hsetup.d_mem⟩ =
          M.mat ⟨d, hsetup.d_mem⟩ * M.mat ⟨a, hA₀A ha⟩) →
        Nat.card A₀ ≤ p ^ (N / p)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
