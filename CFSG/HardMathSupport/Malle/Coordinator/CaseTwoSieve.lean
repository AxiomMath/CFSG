module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

open CFSG.AGLEmbedding

abbrev reeF4Order : ℕ :=
  2 ^ 60 * 3 ^ 3 * 5 ^ 4 * 11 ^ 2 * 13 * 31 ^ 2 * 41 ^ 2 * 61 * 331 * 1321

abbrev reeF4SylowIndex : ℕ :=
  2 ^ 55 * 3 ^ 2 * 11 ^ 2 * 13 * 31 ^ 2 * 41 ^ 2 * 61 * 331 * 1321

def cyclicCentralizerBound (p : ℕ) : ℕ :=
  if p = 13 ∨ p = 61 then 793 else if p = 331 then 8937 else if p = 1321 then 1321 else 0

@[expose] def ReeF4CyclicToralCentralizers : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    IsReeFFourFiveIndex d → Nonempty (K ≃* CatGroup d) → ∀ w : K,
      ((orderOf w = 13 ∨ orderOf w = 61) →
          ∀ g ∈ Subgroup.centralizer ({w} : Set K), g ^ 793 = 1) ∧
        (orderOf w = 331 → ∀ g ∈ Subgroup.centralizer ({w} : Set K), g ^ 993 = 1) ∧
        (orderOf w = 1321 → ∀ g ∈ Subgroup.centralizer ({w} : Set K), g ^ 1321 = 1)

@[expose] def ReeF4InvolutionCentralizerCoprime : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    IsReeFFourFiveIndex d → Nonempty (K ≃* CatGroup d) → ∀ s : K, s ≠ 1 → s * s = 1 →
      ¬ 15 ∣ Nat.card (Subgroup.centralizer ({s} : Set K))

@[expose] def ReeF4SylowNormalizerCard : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    IsReeFFourFiveIndex d → Nonempty (K ≃* CatGroup d) → ∀ P : Sylow 5 K,
      Nat.card (Subgroup.normalizer ((P : Subgroup K) : Set K)) = 60000

@[expose] def ReeF4OuterSigmaFixedOrder : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsReeFFourFiveIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Y) →
    ∃ σ : Y, σ ∉ K ∧ orderOf σ = 5 ∧
      (∀ F : Subgroup Y, IsPGroup 5 F → F ≤ K → F ≤ Subgroup.centralizer ({σ} : Set Y) →
        Nat.card F ≤ 25) ∧
      ∀ F : Subgroup Y, F ≤ K → F ≤ Subgroup.centralizer ({σ} : Set Y) →
        Nat.card F ∣ 35942400

@[expose] def ReeF4IndexSieve : Prop :=
  ∀ n d : ℕ, n ∣ reeF4SylowIndex → n % 625 = 1 →
    d ∣ 14976 → d ∣ n → d % 25 = 1 → n % 3125 = (1 + 25 * (d - 1)) % 3125 →
    (∀ p ∈ ({3, 13} : Finset ℕ), ∀ a : ℕ, p ^ a ∣ 60000 * n → ¬ p ^ (a + 1) ∣ 60000 * n →
      ∃ s : ℕ, s ∣ p ^ a ∧ s ∣ 2400 * d ∧ p ^ a % 5 = s % 5) →
    (∀ p ∈ ({13, 61, 331, 1321} : Finset ℕ), p ∣ n →
      ∃ c r m : ℕ, p ∣ c ∧ c ∣ cyclicCentralizerBound p ∧ r ∣ p - 1 ∧ c * r ∣ reeF4Order ∧
        reeF4Order / (c * r) % p = 1 ∧ p ∣ m ∧ m ∣ c * r ∧ m ∣ 60000 * n ∧
        60000 * n / m % p = 1) →
    n = 1 ∨ n = 9381251

@[expose] def ReeF4CaseTwoInvariant : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsReeFFourFiveIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ T : Sylow 5 Y,
      3 ≤ CFSG.Open.pRank 5 (T : Subgroup Y) →
      ∀ M : Subgroup Y, M ≤ K → (T : Subgroup Y) ≤ Subgroup.normalizer (M : Set Y) →
        K ⊓ Subgroup.normalizer (((T : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ≤ M → M ≠ K →
        (∀ x ∈ (T : Subgroup Y) ⊓ K, x ^ 5 = 1 → x ≠ 1 →
          M ⊓ Subgroup.centralizer ({x} : Set Y) ≤
            Subgroup.normalizer (((T : Subgroup Y) ⊓ K : Subgroup Y) : Set Y)) →
        M = K ⊓ Subgroup.normalizer (((T : Subgroup Y) ⊓ K : Subgroup Y) : Set Y)

end CFSG.HardMathSupport.Malle.Coordinator
