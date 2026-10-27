module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5YData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Words

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def wSub (ws : List (List Nat)) : Subgroup (Equiv.Perm (Fin 1408)) :=
  Subgroup.closure (elemW '' {w | w ∈ ws})

@[expose] noncomputable def yK (k : Nat) : Subgroup (Equiv.Perm (Fin 1408)) :=
  wSub (ykWords.getD k [])

structure CentFacts (t₀ : Equiv.Perm (Fin 1408)) (O : Subgroup (Equiv.Perm (Fin 1408)))
    (s₁ s₂ : Equiv.Perm (Fin 1408)) : Prop where
  card_O : Nat.card ↥O = 128
  O_le : O ≤ pPrime ⊓ Subgroup.centralizer ({t₀} : Set (Equiv.Perm (Fin 1408)))
  mem_O : t₀ ∈ O
  norm_O : ∀ c ∈ P1408 ⊓ Subgroup.centralizer ({t₀} : Set (Equiv.Perm (Fin 1408))),
    ∀ o ∈ O, c * o * c⁻¹ ∈ O
  card_C : Nat.card ↥(pPrime ⊓ Subgroup.centralizer ({t₀} : Set (Equiv.Perm (Fin 1408)))) ≤ 15360
  s₁_mem : s₁ ∈ pPrime ⊓ Subgroup.centralizer ({t₀} : Set (Equiv.Perm (Fin 1408)))
  s₂_mem : s₂ ∈ pPrime ⊓ Subgroup.centralizer ({t₀} : Set (Equiv.Perm (Fin 1408)))
  s₁_sq : s₁ * s₁ ∈ O
  s₂_pow : s₂ ^ 5 ∈ O

@[expose] def PairBad (O : Subgroup (Equiv.Perm (Fin 1408))) (t₀ y₁ y₂ : Equiv.Perm (Fin 1408)) :
    Prop :=
  ∃ w ∈ Subgroup.closure ({y₁, y₂} : Set (Equiv.Perm (Fin 1408))), w ∈ O ∧ w ≠ 1 ∧ w ≠ t₀

@[expose] def PairGood (t₀ y₁ y₂ : Equiv.Perm (Fin 1408)) : Prop :=
  ∃ k < 2, ∃ c ∈ P1408 ⊓ Subgroup.centralizer ({t₀} : Set (Equiv.Perm (Fin 1408))),
    c * y₁ * c⁻¹ ∈ yK k ∧ c * y₂ * c⁻¹ ∈ yK k ∧
      240 ≤ Nat.card ↥(Subgroup.closure ({y₁, y₂} : Set (Equiv.Perm (Fin 1408))))

@[expose] def PairsBad (O : Subgroup (Equiv.Perm (Fin 1408))) (t₀ s₁ s₂ : Equiv.Perm (Fin 1408)) :
    Prop :=
  ∀ o₁ ∈ O, ∀ o₂ ∈ O,
    ((s₁ * o₁) * (s₁ * o₁) = 1 ∨ (s₁ * o₁) * (s₁ * o₁) = t₀) →
      ((s₂ * o₂) ^ 5 = 1 ∨ (s₂ * o₂) ^ 5 = t₀) → PairBad O t₀ (s₁ * o₁) (s₂ * o₂)

@[expose] def PairsBadOrGood (O : Subgroup (Equiv.Perm (Fin 1408))) (t₀ s₁ s₂ :
    Equiv.Perm (Fin 1408)) : Prop :=
  ∀ o₁ ∈ O, ∀ o₂ ∈ O,
    ((s₁ * o₁) * (s₁ * o₁) = 1 ∨ (s₁ * o₁) * (s₁ * o₁) = t₀) →
      ((s₂ * o₂) ^ 5 = 1 ∨ (s₂ * o₂) ^ 5 = t₀) →
        PairBad O t₀ (s₁ * o₁) (s₂ * o₂) ∨ PairGood t₀ (s₁ * o₁) (s₂ * o₂)

structure YFacts : Prop where
  z : CentFacts elemZ (wSub oGensZ) (elemW sOne) (elemW sTwo)
  az : CentFacts (elemA * elemZ) (wSub oGensAZ) (elemW sOne) (elemW sTwo)
  card_y₀ : Nat.card ↥(yK 0) = 240
  card_y₁ : Nat.card ↥(yK 1) = 240
  pairs_z : PairsBad (wSub oGensZ) elemZ (elemW sOne) (elemW sTwo)
  pairs_az : PairsBadOrGood (wSub oGensAZ) (elemA * elemZ) (elemW sOne) (elemW sTwo)

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
