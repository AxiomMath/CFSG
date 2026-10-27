module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

abbrev CbarCent (z : G) (x : ↥(Gx z)) : Subgroup (Gbar z) :=
  Subgroup.centralizer ({barOf z x} : Set (Gbar z))

structure GzOrbitFacts (a z : G) : Prop where
  irreducible : ∀ W : Subgroup G, Subgroup.zpowers z ≤ W → W ≤ Qz z →
    (∀ g ∈ derivedOf (Gx z), ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
      W = Subgroup.zpowers z ∨ W = Qz z
  orbit_QB : IsConjOrbitStab (Gx z) {q | q ∈ Qz z ∧ IsConj z q ∧ q ≠ z} (2 ^ 13 * 3)
  orbit_QA : IsConjOrbitStab (Gx z) {q | q ∈ Qz z ∧ IsConj a q} (2 ^ 11 * 15)
  orbit_outA : IsConjOrbitStab (Gx z) {q | q ∈ Gx z ∧ q ∉ Qz z ∧ IsConj a q} (2 ^ 8 * 15)
  shape_QA : ∀ q ∈ Qz z, IsConj a q → IsShapeTwoTwoSixS5 ↥(Gxy z q)
  shape_outA : ∀ q ∈ Gx z, q ∉ Qz z → IsConj a q → IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy z q)

structure GzClassFacts (a z : G) : Prop where
  centralizes_two_A : ∀ x : ↥(Gx z), (x : G) ^ 2 = 1 →
    (IsShapeZ2TimesA5 ↥(CbarCent z x) ∨ IsShapeTwoTwoWrTwo ↥(CbarCent z x)) →
      (∃ y : G, IsConj a y ∧ y ∈ Gxy z x) ∧ (IsConj a x ∨ IsConj z x)
  centQ_card : ∀ x : ↥(Gx z), (barOf z x) ^ 2 = 1 →
    IsShapeTwoTwoTimesA5 ↥(CbarCent z x) →
      Nat.card (centQtilde z x) = 2 ^ 5 ∧
        ((x : G) ^ 2 = 1 → Nat.card {q : G // q ∈ Qz z ∧ q * x = x * q} = 2 ^ 5)
  inv_two : ∀ t : G, orderOf t = 2 → IsConj a t ∨ IsConj z t

structure GzNoFacts (a z : G) : Prop where
  no_twoTwoA5 : ¬ ∃ x : ↥(Gx z), (x : G) ^ 2 = 1 ∧ IsShapeTwoTwoTimesA5 ↥(CbarCent z x)

end CFSG.EvenSporadicStandard.HNRecog.Section3
