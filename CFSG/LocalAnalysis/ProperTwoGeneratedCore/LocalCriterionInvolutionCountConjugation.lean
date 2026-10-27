module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassTripleOrbitConjugation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassTripleOrbit
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

abbrev fullClass (u : G) : Set G := conjugacyWithin (⊤ : Subgroup G) u

abbrev classFixPair (u : G) (a b : Ω) : Type _ :=
  {v : fullClass u // rightAct a (v : G) = a ∧ rightAct b (v : G) = b}

abbrev classFlipPair (u : G) (a b : Ω) : Type _ :=
  {v : fullClass u // rightAct a (v : G) = b}

theorem right_conjugate_mem_fullClass (u g v : G) (hv : v ∈ fullClass u) :
    rightConjugateElem v g ∈ fullClass u := by
  obtain ⟨h, hh⟩ := hv
  refine ⟨⟨(h : G) * g, trivial⟩, ?_⟩
  rw [← hh]
  simp only [rightConjugateElem, mul_inv_rev, mul_assoc]

def fullClassConjugateEquiv (u g : G) : fullClass u ≃ fullClass u where
  toFun v := ⟨rightConjugateElem v.val g, right_conjugate_mem_fullClass u g v v.property⟩
  invFun v := ⟨rightConjugateElem v.val g⁻¹,
    right_conjugate_mem_fullClass u g⁻¹ v v.property⟩
  left_inv v := Subtype.ext (by
    change rightConjugateElem (rightConjugateElem v.val g) g⁻¹ = v.val
    simp only [rightConjugateElem, inv_inv, mul_assoc, mul_inv_cancel_left,
      mul_inv_cancel, mul_one])
  right_inv v := Subtype.ext (by
    change rightConjugateElem (rightConjugateElem v.val g⁻¹) g = v.val
    simp only [rightConjugateElem, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one])

theorem fullClass_orderOf (u : G) (hu : orderOf u = 2) (v : fullClass u) :
    orderOf (v : G) = 2 := by
  obtain ⟨g, hg⟩ := v.property
  rw [← hg]
  simpa only [MulAut.conj_apply, inv_inv] using
    ((MulAut.conj (g : G)⁻¹).orderOf_eq u).trans hu

theorem class_flip_reverse (u : G) (hu : orderOf u = 2) (a b : Ω)
    (v : classFlipPair u a b) : rightAct b (v.val : G) = a := by
  have hv2 : (v.val : G) * (v.val : G) = 1 := by
    have hh := pow_orderOf_eq_one (v.val : G)
    rw [fullClass_orderOf u hu v.val, pow_two] at hh
    exact hh
  calc
    rightAct b (v.val : G) = rightAct (rightAct a (v.val : G)) (v.val : G) :=
      congrArg (fun x : Ω => rightAct x (v.val : G)) v.property.symm
    _ = a := by rw [rightAct_mul, hv2, rightAct_one]

theorem classFixPair_conjugate_iff (u g : G) (a b : Ω) (v : fullClass u) :
    (rightAct a (v : G) = a ∧ rightAct b (v : G) = b) ↔
      (rightAct (rightAct a g) ((fullClassConjugateEquiv u g v : fullClass u) : G) =
          rightAct a g ∧
        rightAct (rightAct b g) ((fullClassConjugateEquiv u g v : fullClass u) : G) =
          rightAct b g) := by
  change _ ↔ (rightAct (rightAct a g) (rightConjugateElem v.val g) = rightAct a g ∧
    rightAct (rightAct b g) (rightConjugateElem v.val g) = rightAct b g)
  rw [rightAct_rightConjugateElem, rightAct_rightConjugateElem]
  exact and_congr (rightAct_injective g).eq_iff.symm (rightAct_injective g).eq_iff.symm

def classFixPairConjugateEquiv (u g : G) (a b : Ω) :
    classFixPair u a b ≃ classFixPair u (rightAct a g) (rightAct b g) :=
  (fullClassConjugateEquiv u g).subtypeEquiv (classFixPair_conjugate_iff u g a b)

theorem classFlipPair_conjugate_iff (u g : G) (a b : Ω) (v : fullClass u) :
    rightAct a (v : G) = b ↔
      rightAct (rightAct a g) ((fullClassConjugateEquiv u g v : fullClass u) : G) =
        rightAct b g := by
  change _ ↔ rightAct (rightAct a g) (rightConjugateElem v.val g) = rightAct b g
  rw [rightAct_rightConjugateElem]
  exact (rightAct_injective g).eq_iff.symm

def classFlipPairConjugateEquiv (u g : G) (a b : Ω) :
    classFlipPair u a b ≃ classFlipPair u (rightAct a g) (rightAct b g) :=
  (fullClassConjugateEquiv u g).subtypeEquiv (classFlipPair_conjugate_iff u g a b)

theorem classFixPair_card_eq_of_doubly_transitive [Finite G]
    (hdouble : ∀ a b c d : Ω, a ≠ b → c ≠ d →
      ∃ g : G, rightAct a g = c ∧ rightAct b g = d)
    (u : G) (a b c d : Ω) (hab : a ≠ b) (hcd : c ≠ d) :
    Nat.card (classFixPair u a b) = Nat.card (classFixPair u c d) := by
  obtain ⟨g, hg1, hg2⟩ := hdouble a b c d hab hcd
  simpa only [hg1, hg2] using Nat.card_congr (classFixPairConjugateEquiv u g a b)

theorem classFlipPair_card_eq_of_doubly_transitive [Finite G]
    (hdouble : ∀ a b c d : Ω, a ≠ b → c ≠ d →
      ∃ g : G, rightAct a g = c ∧ rightAct b g = d)
    (u : G) (a b c d : Ω) (hab : a ≠ b) (hcd : c ≠ d) :
    Nat.card (classFlipPair u a b) = Nat.card (classFlipPair u c d) := by
  obtain ⟨g, hg1, hg2⟩ := hdouble a b c d hab hcd
  simpa only [hg1, hg2] using Nat.card_congr (classFlipPairConjugateEquiv u g a b)

end CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount
