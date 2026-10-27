module

public import CFSG.LieType.Universal.RootData
public import CFSG.LieType.Steinberg.Basic

public section

namespace CFSG.LieType.HighestRoot

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open scoped MatrixGroups

variable {K : Type*} [Group K]

noncomputable abbrev rootForm (D : UniversalRootDatum K) (γ δ : Fin D.rank → ℤ) : ℚ :=
  form D.isFiniteType (toRat γ) (toRat δ)

structure IsHighestRoot (D : UniversalRootDatum K) (r : Fin D.rank → ℤ) : Prop where
  mem_roots : r ∈ D.roots
  longest : ∀ δ ∈ D.roots, rootForm D δ δ ≤ rootForm D r r
  height_le : ∀ δ ∈ D.roots, ht δ ≤ ht r
  dominant : ∀ i : Fin D.rank, 0 ≤ rootForm D (Pi.single i 1) r

abbrev rankOneGroup (D : UniversalRootDatum K) (γ : Fin D.rank → ℤ) : Subgroup K :=
  D.rootGroup γ ⊔ D.rootGroup (-γ)

@[expose] def highestRootRadical (D : UniversalRootDatum K) (r : Fin D.rank → ℤ) : Subgroup K :=
  ⨆ γ ∈ {γ | γ ∈ D.roots ∧ 0 < rootForm D γ r}, D.rootGroup γ

@[expose] def HighestRootGen (D : UniversalRootDatum K) (p : ℕ) : Prop :=
  ∃ r : Fin D.rank → ℤ, IsHighestRoot D r ∧ D.rootGroup r ≠ ⊥ ∧
    IsPGroup p (highestRootRadical D r) ∧
    highestRootRadical D r ≤ Subgroup.normalizer (D.rootGroup r : Set K) ∧
    Subgroup.normalizer (D.rootGroup r : Set K) ≤
      Subgroup.normalizer (highestRootRadical D r : Set K) ∧
    highestRootRadical D r ⊔ rankOneGroup D r = ⊤

@[expose] def CentralizerCondition (F : Type*) [Field F] (R : Subgroup K) : Prop :=
  ∀ z ∈ R, orderOf z = 2 →
    Subgroup.centralizer ({z} : Set K) ≤ Subgroup.normalizer (R : Set K) ∧
    (Nat.card F = 3 → ∀ L : Subgroup K, L ≤ Subgroup.centralizer ({z} : Set K) →
      Subgroup.centralizer ({z} : Set K) ≤ Subgroup.normalizer (L : Set K) →
      Nonempty (L ≃* SL(2, F)) → z ∈ L → L = R)

@[expose] def HighestRootCZ (D : UniversalRootDatum K) (F : Type*) [Field F] : Prop :=
  ∃ γ ∈ D.roots, (∀ δ ∈ D.roots, rootForm D δ δ ≤ rootForm D γ γ) ∧
    CentralizerCondition F (rankOneGroup D γ)

@[expose] def G2InvolutionData (D : UniversalRootDatum K) (F : Type*) [Field F] : Prop :=
  (∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y) ∧
  ∃ γ ∈ D.roots, (∀ δ ∈ D.roots, rootForm D δ δ ≤ rootForm D γ γ) ∧
    ∀ z ∈ rankOneGroup D γ, orderOf z = 2 →
      Subgroup.centralizer ({z} : Set K) ≤ Subgroup.normalizer (rankOneGroup D γ : Set K) ∧
      ∃ L₀ : Subgroup K, Nonempty (L₀ ≃* SL(2, F)) ∧ z ∈ L₀ ∧
        Subgroup.centralizer ({z} : Set K) ≤ Subgroup.normalizer (L₀ : Set K) ∧
        (∀ a ∈ rankOneGroup D γ, ∀ b ∈ L₀, a * b = b * a) ∧
        ∀ L : Subgroup K, L ≤ Subgroup.centralizer ({z} : Set K) →
          Subgroup.centralizer ({z} : Set K) ≤ Subgroup.normalizer (L : Set K) →
          Nonempty (L ≃* SL(2, F)) → z ∈ L → L = rankOneGroup D γ ∨ L = L₀

end CFSG.LieType.HighestRoot
