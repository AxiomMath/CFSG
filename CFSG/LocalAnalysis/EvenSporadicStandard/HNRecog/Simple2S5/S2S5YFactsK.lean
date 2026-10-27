module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5YDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.HNRecog

structure CentFactsK (t₀ : Equiv.Perm (Fin 1408)) (O : Subgroup (Equiv.Perm (Fin 1408)))
    (s₁ s₂ : Equiv.Perm (Fin 1408)) (cg : List (List Nat)) (i : Nat) : Prop where
  card_O : Nat.card ↥O = 128
  O_le : O ≤ pPrime ⊓ Subgroup.centralizer ({t₀} : Set (Equiv.Perm (Fin 1408)))
  mem_O : t₀ ∈ O
  norm_gens : ∀ w ∈ cg, ∀ o ∈ O, elemW w * o * (elemW w)⁻¹ ∈ O
  swap : elemW (cg.getD i []) ∉ blocks1408
  s₁_mem : s₁ ∈ pPrime ⊓ Subgroup.centralizer ({t₀} : Set (Equiv.Perm (Fin 1408)))
  s₂_mem : s₂ ∈ pPrime ⊓ Subgroup.centralizer ({t₀} : Set (Equiv.Perm (Fin 1408)))
  s₁_sq : s₁ * s₁ ∈ O
  s₂_pow : s₂ ^ 5 ∈ O

structure YFactsK : Prop where
  z : CentFactsK elemZ (wSub oGensZ) (elemW sOne) (elemW sTwo) classz.centGens 1
  az : CentFactsK (elemA * elemZ) (wSub oGensAZ) (elemW sOne) (elemW sTwo) classaz.centGens 0
  card_y₀ : Nat.card ↥(yK 0) = 240
  card_y₁ : Nat.card ↥(yK 1) = 240
  pairs_z : PairsBad (wSub oGensZ) elemZ (elemW sOne) (elemW sTwo)
  pairs_az : PairsBadOrGood (wSub oGensAZ) (elemA * elemZ) (elemW sOne) (elemW sTwo)

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5

end
