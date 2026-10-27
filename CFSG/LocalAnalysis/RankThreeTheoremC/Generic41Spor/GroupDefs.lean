module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def SylowIsPlane (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow p K, IsElemAbelian p (S : Subgroup K) ∧ Nat.card (S : Subgroup K) = p ^ 2

@[expose] def SylowIsHeisenberg (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow p K, Nat.card (S : Subgroup K) = p ^ 3 ∧
    (∃ a ∈ (S : Subgroup K), ∃ b ∈ (S : Subgroup K), a * b ≠ b * a) ∧
    ∀ s ∈ (S : Subgroup K), s ^ p = 1

@[expose] def SylowIsCyclicSq (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow p K, IsCyclic (S : Subgroup K) ∧ Nat.card (S : Subgroup K) = p ^ 2

@[expose] def NoOuterP (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ¬ p ∣ Nat.card (Outer K)

@[expose] def OutIsOrderP (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  Nat.card (Outer K) = p

@[expose] def NormalizerTransitive (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow p K, ∀ a ∈ (S : Subgroup K), a ≠ 1 → ∀ b ∈ (S : Subgroup K), b ≠ 1 →
    ∃ n ∈ normalizer ((S : Subgroup K) : Set K), n * a * n⁻¹ = b

@[expose] def NormalizerNoFixed (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow p K, ∀ a ∈ (S : Subgroup K), a ≠ 1 →
    ∃ n ∈ normalizer ((S : Subgroup K) : Set K), n * a ≠ a * n

@[expose] def NormalizerMaximal (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow p K, ∀ H : Subgroup K, normalizer ((S : Subgroup K) : Set K) ≤ H →
    H = normalizer ((S : Subgroup K) : Set K) ∨ H = ⊤

@[expose] def IsAutOverType (T : ℕ → ∀ (Q : Type) [Group Q], Prop) (p : ℕ) {X : Type} [Group X]
    (K : Subgroup X) : Prop :=
  K.Normal ∧ centralizer (K : Set X) = ⊥ ∧ T p ↥K

@[expose] def SignalizerTrivialX (T : ℕ → ∀ (Q : Type) [Group Q], Prop) (p : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), IsAutOverType T p K →
    ∀ R : Sylow p X, ∀ W : Subgroup X, Nat.Coprime p (Nat.card W) →
      ((R : Subgroup X) ⊓ K) ≤ normalizer (W : Set X) → W = ⊥

@[expose] def Lemma45Facts (T : ℕ → ∀ (Q : Type) [Group Q], Prop) (p : ℕ)
    (Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), IsAutOverType T p K →
    ∀ (R : Sylow p X) (U₀ : Subgroup X), U₀ ≤ (R : Subgroup X) → IsElemAbelian p U₀ →
      Nat.card U₀ = p → Shape K (R : Subgroup X) U₀ →
      ∃ V : Subgroup X, V ≤ K ∧ IsPGroup 2 V ∧ U₀ ≤ normalizer (V : Set X) ∧
        ¬ V ≤ normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X)


@[expose] def Zin {K : Type} [Group K] (S : Subgroup K) : Subgroup K := (Subgroup.center ↥S).map S.subtype

@[expose] def NormalizerTransitiveCenter (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow p K, ∀ z ∈ Zin (S : Subgroup K), z ≠ 1 → ∀ w ∈ Zin (S : Subgroup K), w ≠ 1 →
    ∃ n ∈ normalizer ((S : Subgroup K) : Set K), n * z * n⁻¹ = w

@[expose] def NormalizerIrreducibleQuotient (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow p K, ∀ A : Subgroup K, Zin (S : Subgroup K) ≤ A → A ≤ (S : Subgroup K) →
    normalizer ((S : Subgroup K) : Set K) ≤ normalizer (A : Set K) →
    A = Zin (S : Subgroup K) ∨ A = (S : Subgroup K)

structure ExtraFacts (T : ℕ → ∀ (Q : Type) [Group Q], Prop) (p : ℕ)
    (Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop) : Prop where
  sylow : ∀ (K : Type) [Group K] [Finite K], T p K → SylowIsHeisenberg p K
  noOuter : ∀ (K : Type) [Group K] [Finite K], T p K → NoOuterP p K
  transCenter : ∀ (K : Type) [Group K] [Finite K], T p K → NormalizerTransitiveCenter p K
  irreducible : ∀ (K : Type) [Group K] [Finite K], T p K → NormalizerIrreducibleQuotient p K
  maximal : ∀ (K : Type) [Group K] [Finite K], T p K → NormalizerMaximal p K
  sigTriv : SignalizerTrivialX T p
  lemma45 : Lemma45Facts T p Shape

@[expose] def McLShape {X : Type} [Group X] (K R U₀ : Subgroup X) : Prop :=
  ∃ u ∈ U₀ ⊓ K, ∃ s ∈ R ⊓ K, s * u ≠ u * s

@[expose] def J4Shape {X : Type} [Group X] (K R U₀ : Subgroup X) : Prop :=
  U₀ ⊓ K ≠ ⊥ ∧ ∀ u ∈ U₀ ⊓ K, ∀ s ∈ R ⊓ K, s * u = u * s

@[expose] def TitsShape {X : Type} [Group X] (K R U₀ : Subgroup X) : Prop := U₀ ⊓ K ≠ ⊥

@[expose] def A10Shape {X : Type} [Group X] (K R U₀ : Subgroup X) : Prop :=
  ∃ e : ↥K ≃* alternatingGroup (Fin 10), ∃ u ∈ U₀ ⊓ K, ∃ hu : u ∈ K,
    ((e ⟨u, hu⟩ : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).cycleType = {5, 5}

@[expose] def Sz32Shape {X : Type} [Group X] (K R U₀ : Subgroup X) : Prop := ¬ U₀ ≤ K

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
