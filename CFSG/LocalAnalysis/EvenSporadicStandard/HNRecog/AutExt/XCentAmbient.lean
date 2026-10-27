module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XCentSpec
public import Certificates.Certificate441898

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog.Section3

theorem derived_eq_N (F : XNFacts) :
    derivedOf XP = closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))) :=
  le_antisymm F.der_le (N_le_derived F)

theorem xCent_ambient (F : XNFacts)
    (hP : Nat.card ↥P1408 = 177408000) :
    ∀ T : ↥XP, T * T = 1 →
      (Nat.card ↥(centralizer ({T} : Set ↥XP)) = 768 ∨
        Nat.card ↥(centralizer ({T} : Set ↥XP)) = 384) → XAutCent ↥XP T := by
  intro T hT2 hcard
  obtain ⟨hii, ha1⟩ := Certificates.certificate441898 hP T hT2 hcard
  have hAT : elemA * (T : Equiv.Perm (Fin 1408)) = T * elemA := (F.a_central T T.2).symm
  have e := derived_eq_N F
  refine xAutCent_of_ambient XP F.a_mem T.2 F.inner hAT ?_ ?_
  · rw [e]
    exact hii
  · rw [e]
    exact ha1

end CFSG.EvenSporadicStandard.HNRecog.Section4.XModel
