module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Graph
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Generic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog CFSG.Monster.GMS

variable {G : Type} [Group G]

structure LinesFacts (a z : G) : Prop where
  six_A : ∀ x ∈ orb6A a a,
    derivedOf (Gxy a x) = Gxy a x ⊓ derivedOf (Gxy a ((a * x) ^ 3)) ∧
    IsShapeA5 ↥(derivedOf (Gxy a x)) ∧
    (∀ φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy a ((a * x) ^ 3))),
      HasSixOrbit φ (derivedOf (Gxy a x))) ∧
    Gxy a x ⊓ Subgroup.closure {a, (a * x) ^ 3} = Subgroup.zpowers ((a * x) ^ 3)
  five_A : ∀ x ∈ orb5A a a,
    IsConjOrbit (Gxy a x) {t | t ∈ Gxy a x ∧ orderOf t = 2} ∧
      {t | t ∈ Gxy a x ∧ orderOf t = 2} = orb2B a z a ∩ orb2B a z x
  common : ∀ x y t : G, IsConj a x → IsConj a y → IsConj a (x * y) → t ≠ x * y →
    t ∈ orb2A a x ∩ orb2A a y → (orb2A a x ∩ orb2A a y ∩ orb2A a t).Nonempty
  unique_third : ∀ x y : G, IsConj a x → IsConj a y → IsConj a (x * y) →
    {t | IsConj a t ∧ t ≠ x ∧ t ≠ y ∧ gammaPerp a {x, y, t} = {x, y, t}} = {x * y}
  fig14_a : ∀ x ∈ orb4A a z a, ∀ c ∈ orb2A a a ∩ orb2A a x,
    IsConj a ((a * x) ^ 2 * c) ∧ IsConj a ((a * x) ^ 2 * x) ∧ IsConj a ((a * x) ^ 2 * x * c) ∧
      IsConj a (a * (a * x) ^ 2) ∧ IsConj a (a * c * (a * x) ^ 2)
  fig14_b : ∀ x ∈ orb4A a z a, ∀ t ∈ orb2B a z a ∩ orb2A a x,
    IsConj a ((a * x) ^ 2 * t) ∧ IsConj a ((a * x) ^ 2 * x) ∧ IsConj a (t * (a * x) ^ 2 * x) ∧
      IsConj a (a * (a * x) ^ 2) ∧ IsConj z (t * a * (a * x) ^ 2)

structure OddInvFacts (a z : G) : Prop where
  odd_inv : ∀ w x y : G, IsConj z w → IsConj a x → IsConj a y → x ∈ Gx w → y ∈ Gx w →
    Odd (orderOf (x * y)) → ∃ t : G, IsConj a t ∧ t ∈ Gxyz x w y
  gamma_of_inv : ∀ x y : G, IsConj a x → IsConj a y → (∃ t : G, orderOf t = 2 ∧ t ∈ Gxy x y) →
    y ∈ gammaSet a z x

structure GammaFacts (a z : G) : Prop where
  inv_one : ∀ x y t : G, IsConj a x → IsConj a y → y ∈ gammaSet a z x → t ∈ orb2A a y →
    y ∈ orb2A a x ∪ orb2B a z x ∪ orb4A a z x ∪ orb4B a x ∪ orb5A a x →
      ∃ s : G, orderOf s = 2 ∧ s ∈ Gxyz x y t
  inv_two_i : ∀ x y t b : G, IsConj a x → IsConj a y → y ∈ gammaSet a z x → t ∈ orb2A a y →
    y ∈ orb3A a x ∪ orb6A a x → b ∈ orb2A a x ∩ orb2A a y →
    t ∈ orb2A a b ∪ orb2B a z b ∪ orb3A a b ∪ orb4B a b ∪ orb6A a b →
      ∃ s : G, orderOf s = 2 ∧ s ∈ Gxyz x y t
  inv_two_ii : ∀ x y t b : G, IsConj a x → IsConj a y → y ∈ gammaSet a z x → t ∈ orb2A a y →
    y ∈ orb3A a x ∪ orb6A a x → b ∈ orb2A a x ∩ orb2A a y → t ∈ orb4A a z b →
      ∃ s : G, orderOf s = 2 ∧ s ∈ Gxy x t
  five_E : ∀ x y t : G, IsConj a x → IsConj a y → y ∈ gammaSet a z x → t ∈ orb2A a y →
    y ∈ orb5E a x →
      ∃ y₁ ∈ orb2A a x ∪ orb2B a z x ∪ orb4A a z x ∪ orb4B a x ∪ orb6A a x, t ∈ orb2A a y₁
  mem_gamma : ∀ x y t : G, IsConj a x → IsConj a y → y ∈ gammaSet a z x → t ∈ orb2A a y →
    t ∈ gammaSet a z x
  connected : (Gamma a).Connected
  eq_gamma : ∀ x y : G, IsConj a x → IsConj a y → y ∈ gammaSet a z x

end CFSG.EvenSporadicStandard.HNRecog.Section3
