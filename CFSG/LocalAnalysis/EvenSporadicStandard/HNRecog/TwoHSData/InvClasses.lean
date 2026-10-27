
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClassesBase

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.SylowCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WClassSpec
public import Certificates.Certificate26771

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

section Cert

local notation "𝒞" => CFSG.Sporadic.SmallOddCore.conjClass

theorem invClasses_classSpec (hP : Nat.card ↥P1408 = 177408000) :
    ClassSpec classz elemZ ∧ ClassSpec classaz (elemA * elemZ) ∧
      ClassSpec classb elemB ∧ ClassSpec classz₁ elemZ₁ :=
  have h := Certificates.certificate26771 hP
  ⟨h.z, h.az, h.b, h.z₁⟩

theorem not_isConj_inv (hP : Nat.card ↥P1408 = 177408000) :
    ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![pA, pZ, pA * pZ, pB, pZ₁] i) (![pA, pZ, pA * pZ, pB, pZ₁] j) :=
  (Certificates.certificate26771 hP).not_isConj

theorem involution_cover_inv (hP : Nat.card ↥P1408 = 177408000) :
    ∀ x : ↥P1408, orderOf x = 2 →
      ∃ i : Fin 5, IsConj (![pA, pZ, pA * pZ, pB, pZ₁] i) x :=
  (Certificates.certificate26771 hP).cover

theorem classes_distinct (hP : Nat.card ↥P1408 = 177408000) :
    elemA ≠ elemZ ∧ elemA ≠ elemA * elemZ ∧ elemA ≠ elemB ∧ elemA ≠ elemZ₁ ∧
      elemA * elemZ ∉ 𝒞 P1408 elemZ ∧ elemB ∉ 𝒞 P1408 elemZ ∧ elemZ₁ ∉ 𝒞 P1408 elemZ ∧
      elemB ∉ 𝒞 P1408 (elemA * elemZ) ∧ elemZ₁ ∉ 𝒞 P1408 (elemA * elemZ) ∧
      elemZ₁ ∉ 𝒞 P1408 elemB := by
  have h := not_isConj_inv hP
  have ne : ∀ i j : Fin 5, i ≠ j → ((![pA, pZ, pA * pZ, pB, pZ₁] i : ↥P1408) :
      Equiv.Perm (Fin 1408)) ≠ ![pA, pZ, pA * pZ, pB, pZ₁] j := fun i j hij e =>
    h i j hij ((congrArg (IsConj (![pA, pZ, pA * pZ, pB, pZ₁] i)) (Subtype.ext e)).mp
      (IsConj.refl _))
  have nc : ∀ i j : Fin 5, i ≠ j → ((![pA, pZ, pA * pZ, pB, pZ₁] j : ↥P1408) :
      Equiv.Perm (Fin 1408)) ∉ 𝒞 P1408 (![pA, pZ, pA * pZ, pB, pZ₁] i) := fun i j hij hm =>
    h i j hij ((isConj_iff_mem_conjClass P1408 _ _).2 hm)
  exact ⟨ne 0 1 (by decide), ne 0 2 (by decide), ne 0 3 (by decide), ne 0 4 (by decide),
    nc 1 2 (by decide), nc 1 3 (by decide), nc 1 4 (by decide), nc 2 3 (by decide),
    nc 2 4 (by decide), nc 3 4 (by decide)⟩

end Cert

end CFSG.EvenSporadicStandard.HNRecog
