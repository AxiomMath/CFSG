module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.SelfStructure
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.SelfSplit
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.SelfFus

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open
open scoped commutatorElement

namespace CentConfig

variable {X : Type} [Group X] [Finite X] {a b : X} {E : Subgroup X} {Fus : X → Prop}

section Certified


theorem case_self (h : CentConfig X a b E Fus) (hE : IsComponentOf E ⊤) :
    TransferWitness X a Fus := by
  haveI hEn : E.Normal := self_normal h hE
  haveI hYn : (centralizer (E : Set X)).Normal := Subgroup.normal_centralizer
  obtain ⟨S, U, A, haS, hUS, hUidx, haU, hAcyc, hbA, hUY, hP⟩ :=
    exists_sylow_split (self_comm E) (self_sup h hE) (self_inf h) h.b_sq h.b_ne
      (self_a_mem h) h.a_sq h.a_ne (self_a_not_mem h) (self_cent h) (self_card h)
      h.two_pow
  refine ⟨S, haS, U, hUS, hUidx, haU, ?_⟩
  intro w hwU hwfus
  obtain ⟨hw2, hw1, hD⟩ := h.fus w hwfus
  by_cases hwY : w ∈ centralizer (E : Set X)
  · have hwA : w ∈ A := hUY ⟨hwU, hwY⟩
    haveI hAcycI : IsCyclic ↥A := hAcyc
    have hb2A : (⟨b, hbA⟩ : ↥A) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using h.b_sq
    have hb1A : (⟨b, hbA⟩ : ↥A) ≠ 1 := by
      intro hb
      exact h.b_ne (by simpa using congrArg Subtype.val hb)
    have hw2A : (⟨w, hwA⟩ : ↥A) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hw2
    have hw1A : (⟨w, hwA⟩ : ↥A) ≠ 1 := by
      intro hw
      exact hw1 (by simpa using congrArg Subtype.val hw)
    have hEq : (⟨b, hbA⟩ : ↥A) = ⟨w, hwA⟩ :=
      CFSG.Semidihedral.UnitaryBranch.eq_of_sq_eq_one_of_isCyclic hb2A hb1A hw2A hw1A
    have hbw : b = w := congrArg Subtype.val hEq
    exact h.fus_b (hbw.symm ▸ hwfus)
  · exact false_of_fus_self (centralizer (E : Set X)) (self_quotient h hE) hw2 hwY hD hP

end Certified

end CentConfig

end CFSG.EvenSporadicStandard.Co3Std.CentT
