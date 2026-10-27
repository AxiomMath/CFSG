module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassTripleOrbitConjugation

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassTripleOrbit
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

abbrev fixedSet (u : G) : Set Ω := {a | rightAct a u = a}

theorem right_conjugate_fixed_iff (u g : G) (a : Ω) :
    rightAct a (rightConjugateElem u g) = a ↔
      rightAct (rightAct a g⁻¹) u = rightAct a g⁻¹ := by
  have ha : rightAct (rightAct a g⁻¹) g = a := by
    rw [rightAct_mul, inv_mul_cancel, rightAct_one]
  constructor
  · intro h
    apply rightAct_injective g
    change rightAct (rightAct (rightAct a g⁻¹) u) g = rightAct (rightAct a g⁻¹) g
    rw [← rightAct_rightConjugateElem (rightAct a g⁻¹) u g, ha, h]
  · intro h
    calc
      rightAct a (rightConjugateElem u g) =
          rightAct (rightAct (rightAct a g⁻¹) g) (rightConjugateElem u g) := by rw [ha]
      _ = rightAct (rightAct (rightAct a g⁻¹) u) g := rightAct_rightConjugateElem _ _ _
      _ = a := by rw [h, ha]

def fixedSetConjugateEquiv (u g : G) : fixedSet (Ω := Ω) u ≃
    fixedSet (Ω := Ω) (rightConjugateElem u g) where
  toFun a := ⟨rightAct a.val g, by
    change rightAct (rightAct a.val g) (rightConjugateElem u g) = rightAct a.val g
    rw [rightAct_rightConjugateElem, a.property]⟩
  invFun a := ⟨rightAct a.val g⁻¹, (right_conjugate_fixed_iff u g a.val).mp a.property⟩
  left_inv a := Subtype.ext (rightAct_inv_cancel a.val g)
  right_inv a := Subtype.ext (by
    change rightAct (rightAct a.val g⁻¹) g = a.val
    rw [rightAct_mul, inv_mul_cancel, rightAct_one])

theorem conjugate_fixedSet_card [Finite Ω] (u : G)
    (v : G) (hv : v ∈ conjugacyWithin (⊤ : Subgroup G) u) :
    Nat.card (fixedSet (Ω := Ω) v) = Nat.card (fixedSet (Ω := Ω) u) := by
  obtain ⟨g, hg⟩ := hv
  change rightConjugateElem u (g : G) = v at hg
  rw [← hg]
  exact (Nat.card_congr (fixedSetConjugateEquiv (Ω := Ω) u g)).symm

theorem pair_stabilizer_class_intersection (u : G)
    (hcentralizer : ∀ a b c d : Ω,
      a ∈ fixedSet u → b ∈ fixedSet u → c ∈ fixedSet u → d ∈ fixedSet u →
      a ≠ b → c ≠ d →
      ∃ g ∈ Subgroup.centralizer ({u} : Set G),
        rightAct a g = c ∧ rightAct b g = d)
    (a b : Ω) (ha : a ∈ fixedSet u) (hb : b ∈ fixedSet u) (hab : a ≠ b) :
    conjugacyWithin (⊤ : Subgroup G) u ∩
        ((rightStabilizer a ⊓ rightStabilizer b : Subgroup G) : Set G) =
      conjugacyWithin (rightStabilizer a ⊓ rightStabilizer b) u := by
  let D : Subgroup G := rightStabilizer a ⊓ rightStabilizer b
  ext v
  constructor
  · rintro ⟨⟨g, hg⟩, hva, hvb⟩
    change rightConjugateElem u (g : G) = v at hg
    have ha' : rightAct a (g : G)⁻¹ ∈ fixedSet u := by
      apply (right_conjugate_fixed_iff u g a).mp
      rw [hg]
      exact (mem_rightStabilizer a v).mp hva
    have hb' : rightAct b (g : G)⁻¹ ∈ fixedSet u := by
      apply (right_conjugate_fixed_iff u g b).mp
      rw [hg]
      exact (mem_rightStabilizer b v).mp hvb
    have hab' : rightAct a (g : G)⁻¹ ≠ rightAct b (g : G)⁻¹ :=
      fun h => hab (rightAct_injective _ h)
    obtain ⟨c, hc, hca, hcb⟩ := hcentralizer a b _ _ ha hb ha' hb' hab hab'
    have hcgD : c * (g : G) ∈ D := by
      constructor
      · apply (mem_rightStabilizer a _).mpr
        rw [← rightAct_mul, hca, rightAct_mul, inv_mul_cancel, rightAct_one]
      · apply (mem_rightStabilizer b _).mpr
        rw [← rightAct_mul, hcb, rightAct_mul, inv_mul_cancel, rightAct_one]
    have hcu : rightConjugateElem u c = u := by
      have hcomm : u * c = c * u := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
      change c⁻¹ * u * c = u
      rw [mul_assoc, hcomm, inv_mul_cancel_left]
    refine ⟨⟨c * (g : G), hcgD⟩, ?_⟩
    change rightConjugateElem u (c * (g : G)) = v
    calc
      rightConjugateElem u (c * (g : G)) =
          rightConjugateElem (rightConjugateElem u c) (g : G) := by
        simp only [rightConjugateElem, mul_inv_rev, mul_assoc]
      _ = v := by rw [hcu, hg]
  · rintro ⟨g, hg⟩
    refine ⟨⟨⟨g, trivial⟩, hg⟩, ?_⟩
    change rightConjugateElem u (g : G) = v at hg
    have hau : rightAct a u = a := ha
    have hbu : rightAct b u = b := hb
    have hga : rightAct a (g : G) = a := (mem_rightStabilizer a (g : G)).mp g.property.1
    have hgb : rightAct b (g : G) = b := (mem_rightStabilizer b (g : G)).mp g.property.2
    constructor
    · apply (mem_rightStabilizer a v).mpr
      calc
        rightAct a v = rightAct (rightAct a (g : G)) (rightConjugateElem u g) := by
          rw [hga, hg]
        _ = a := by rw [rightAct_rightConjugateElem, hau, hga]
    · apply (mem_rightStabilizer b v).mpr
      calc
        rightAct b v = rightAct (rightAct b (g : G)) (rightConjugateElem u g) := by
          rw [hgb, hg]
        _ = b := by rw [rightAct_rightConjugateElem, hbu, hgb]

end CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount
