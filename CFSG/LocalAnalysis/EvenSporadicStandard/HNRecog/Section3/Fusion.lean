module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G]

structure Fusion1Facts (a z : G) : Prop where
  odd_index : Odd (Gx z).index
  rep_z : ∃ z₀ b u : ↥(Gx a), TwoHSFacts ↥(Gx a) (GxSelf a) z₀ b u ∧
    IsConj z (z₀ : G) ∧ IsConj a (a * z₀) ∧ (z₀ : G) ∈ derivedOf (Gx a) ∧ a ∈ Qz (z₀ : G) ∧
      CFSG.Open.pCoreOf 2 (Gxy a z₀) = Qz (z₀ : G) ⊓ Gx a ∧ IsShapeTwoTwoSixS5 ↥(Gxy a z₀)
  derived_of_2B : ∀ t : G, t ∈ Gx a → t ^ 2 = 1 → IsConj z t → IsConj a (a * t) →
    t ∈ derivedOf (Gx a)

structure CubeFacts (a z : G) : Prop where
  no_cube : ¬ ∃ E : Subgroup G, IsElemTwo 3 E ∧ ∀ t ∈ E, t ^ 2 = 1 → t ≠ 1 → IsConj a t
  m11_two_A : ∀ M : Subgroup G, M ≤ Gx a → IsSporadic ↥M .M11 →
    ∀ t ∈ M, t ^ 2 = 1 → t ≠ 1 → IsConj a t

structure A8Shapes (a z : G) : Prop where
  shape_2211 : ∀ K : Subgroup G, K ≤ Gx a → ∀ φ : alternatingGroup (Fin 8) ≃* ↥K,
    ∀ t : alternatingGroup (Fin 8), (t : Equiv.Perm (Fin 8)).cycleType = {2, 2} →
      IsConj a (φ t : G)
  shape_2222 : ∀ K : Subgroup G, K ≤ Gx a → ∀ φ : alternatingGroup (Fin 8) ≃* ↥K,
    ∀ t : alternatingGroup (Fin 8), (t : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} →
      IsConj z (φ t : G)

structure Fusion2Facts (a z : G) : Prop where
  reps_bu : ∀ z₀ b u : ↥(Gx a), TwoHSFacts ↥(Gx a) (GxSelf a) z₀ b u → IsConj z (z₀ : G) →
    (IsConj a (b : G) ∧ IsConj a (a * b) ∧ (b : G) ∉ derivedOf (Gx a) ∧
      IsShapeTwoTwoTimesA8 ↥(Gxy a b)) ∧
    (IsConj z (u : G) ∧ IsConj z (a * u) ∧ a ∉ Qz (u : G) ∧ IsElemTwo 5 (Qz (u : G) ⊓ Gx a) ∧
      CFSG.Open.pCoreOf 2 (derivedOf (Gxy a u)) = Qz (u : G) ⊓ Qz (a * u) ∧
      IsElemTwo 4 (Qz (u : G) ⊓ Qz (a * u)) ∧ IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy a u))
  mem_derived_iff : ∀ t : G, t ∈ Gx a → t ^ 2 = 1 →
    (t ∈ derivedOf (Gx a) ↔ (IsConj a t ↔ ¬ IsConj a (a * t)))

structure Fusion3Facts (a z : G) : Prop where
  shape_2A : ∀ b ∈ orb2A a a, IsShapeTwoTwoTimesA8 ↥(Gxy a b)
  shape_2AB : ∀ w ∈ orb2AB a z a, IsShapeTwoTwoSixS5 ↥(Gxy a w) ∧ a ∈ Qz w
  shape_2B : ∀ b ∈ orb2B a z a, IsShapeTwoTwoSixS5 ↥(Gxy a b)
  shape_2BB : ∀ w ∈ orb2BB a z a, IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy a w) ∧ a ∉ Qz w

structure A8Pictures (a z : G) : Prop where
  fig8a : ∀ b ∈ orb2A a a, ∀ φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy a b)),
    ∀ t : alternatingGroup (Fin 8), (t : Equiv.Perm (Fin 8)).cycleType = {2, 2} →
      IsConj a (φ t : G) ∧ IsConj z (a * φ t) ∧ IsConj z (b * φ t) ∧ IsConj z (a * b * φ t)
  fig8b : ∀ b ∈ orb2A a a, ∀ φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy a b)),
    ∀ t : alternatingGroup (Fin 8), (t : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} →
      IsConj z (φ t : G) ∧ IsConj a (a * φ t) ∧ IsConj a (b * φ t) ∧ IsConj a (a * b * φ t)
  cube_conj : ∀ E : Subgroup G, IsElemTwo 3 E →
    (∃ a' ∈ E, ∃ b' ∈ E, a' ≠ b' ∧ IsConj a a' ∧ IsConj a b' ∧ IsConj a (a' * b')) →
      ∃ g b t : G, b ∈ orb2A a a ∧ t ∈ derivedOf (Gxy a b) ∧ t ^ 2 = 1 ∧ t ≠ 1 ∧
        E.map (MulAut.conj g).toMonoidHom = Subgroup.closure {a, b, t}
  cube_transitive : ∀ E : Subgroup G, IsElemTwo 3 E → Nat.card {x : G // x ∈ E ∧ IsConj a x} = 6 →
    (∀ x ∈ E, IsConj a x → ∀ y ∈ E, IsConj a y → ∃ g ∈ Subgroup.normalizer (E : Set G),
      g * x * g⁻¹ = y) ∧
    (∀ a' ∈ E, IsConj a a' → ∀ x ∈ (E : Set G) ∩ orb2A a a', ∀ y ∈ (E : Set G) ∩ orb2A a a',
      ∃ g ∈ Subgroup.normalizer (E : Set G) ⊓ Gx a', g * x * g⁻¹ = y)

end CFSG.EvenSporadicStandard.HNRecog.Section3
