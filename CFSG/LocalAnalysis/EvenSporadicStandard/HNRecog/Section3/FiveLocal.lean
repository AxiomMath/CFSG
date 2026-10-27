module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

structure FiveSylowFacts (a z : G) : Prop where
  sylow : ∀ ρ : G, ρ ∈ Gx a → orderOf ρ = 5 → IsShapeCentralizerFiveB ↥(Gxy a ρ) →
    ∀ T : Sylow 2 ↥(Gxy a ρ), ∃ z' : G, IsConj z z' ∧ IsConj z (a * z') ∧
      Nat.card ↥(T : Subgroup ↥(Gxy a ρ)) = 4 ∧
      (T : Subgroup ↥(Gxy a ρ)).map (Gxy a ρ).subtype = Subgroup.closure {a, z'} ∧
      padicValNat 2 (Nat.card ↥(Gx ρ)) = 2

structure FiveCentFacts (a z : G) : Prop extends FiveSylowFacts a z where
  cent_five : ∀ ρ : G, ρ ∈ Gx a → orderOf ρ = 5 → IsShapeCentralizerFiveB ↥(Gxy a ρ) →
    ∀ t : G, IsConj a t → t ∈ Gx ρ → IsShapeCentralizerFiveB ↥(Gxy t ρ)

structure FiveCoreFacts (a z : G) : Prop extends FiveCentFacts a z where
  odd_core : ∀ ρ : G, ρ ∈ Gx a → orderOf ρ = 5 → IsShapeCentralizerFiveB ↥(Gxy a ρ) →
    ∀ T : Sylow 2 ↥(Gxy a ρ), ∃ N : Subgroup G, N ≤ Gx ρ ∧ (N.subgroupOf (Gx ρ)).Normal ∧
      IsPGroup 5 ↥N ∧ Nat.card ↥N ≤ 5 ^ 4 ∧
      N ⊔ (T : Subgroup ↥(Gxy a ρ)).map (Gxy a ρ).subtype = Gx ρ ∧
      N ⊓ (T : Subgroup ↥(Gxy a ρ)).map (Gxy a ρ).subtype = ⊥

structure FiveFacts (a z : G) : Prop extends FiveCoreFacts a z where
  five_E : ∀ x ∈ orb5E a a, IsShapeFiveCubeByTwoTwo ↥(Gxy a x)
  inv_cent : ∀ x ∈ orb5E a a, ∀ t : G, orderOf t = 2 → t ∈ Gx (a * x) → t ∈ Gxy a x
  klein_E : ∀ x ∈ orb5E a a, ∃ t t' : G, IsConj a t ∧ IsConj z t' ∧ IsConj z (t * t') ∧
    t ∈ Gxy a x ∧ t' ∈ Gxy a x ∧ t * t' = t' * t

structure OrderFacts (G : Type) [Group G] : Prop where
  card_eq : Nat.card G = 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19
  exists_eleven : ∃ ω : G, orderOf ω = 11
  eleven_one_class : ∀ ω ω' : G, orderOf ω = 11 → orderOf ω' = 11 → IsConj ω ω'
  cent_eleven : ∀ ω : G, orderOf ω = 11 → IsShapeCentralizerEleven ↥(Gx ω)

end CFSG.EvenSporadicStandard.HNRecog.Section3
