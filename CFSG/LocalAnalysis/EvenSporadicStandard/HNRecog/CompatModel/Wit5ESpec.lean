module

public import Certificates.Certificate441875

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open Subgroup CFSG.EvenSporadicStandard.HNRecog

section Cert


theorem wit5e_model (hP : Nat.card ↥P1408 = 177408000) (a x : ↥P1408) (ha : In2A a)
    (hac : a * pZ₁ = pZ₁ * a) (hxc : x * pZ₁ = pZ₁ * x) :
    x ∈ closure {y : ↥P1408 | y * pZ₁ = pZ₁ * y ∧ In2A y ∧ orderOf (a * y) ≠ 5} :=
  Certificates.certificate441875 hP a x ha hac hxc

end Cert

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
