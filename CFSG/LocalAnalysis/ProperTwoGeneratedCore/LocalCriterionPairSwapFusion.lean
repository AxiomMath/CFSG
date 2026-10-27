module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairSwapAmbient
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

theorem ambient_fusion_of_two_swap_orbits
    (K D : Subgroup G) (u t : G) (hu : IsInvolution u)
    (hlocal : {s : G | IsInvolution s ∧ s ∈ K ∧ s ∉ D} =
      conjugacyWithin D t ∪ conjugacyWithin D (u * t))
    (hdisj : Disjoint (conjugacyWithin D t) (conjugacyWithin D (u * t)))
    (hclasses : ∀ s : G, IsInvolution s →
      s ∈ conjugacyWithin (⊤ : Subgroup G) u ∨ s ∈ conjugacyWithin (⊤ : Subgroup G) t)
    (hclassesDistinct : conjugacyWithin (⊤ : Subgroup G) u ≠
      conjugacyWithin (⊤ : Subgroup G) t)
    (htfiber : conjugacyWithin (⊤ : Subgroup G) t ∩ ((K : Set G) \ (D : Set G)) =
      conjugacyWithin D t) :
    conjugacyWithin (⊤ : Subgroup G) u ∩ ((K : Set G) \ (D : Set G)) =
        conjugacyWithin D (u * t) ∧
      u * t ∈ conjugacyWithin (⊤ : Subgroup G) u := by
  have hglobalDisjoint : Disjoint (conjugacyWithin (⊤ : Subgroup G) u)
      (conjugacyWithin (⊤ : Subgroup G) t) := by
    apply Set.disjoint_left.mpr
    intro x hxU hxT
    rw [conjugacyWithin_top_eq_conjugatesOf] at hxU hxT
    apply hclassesDistinct
    rw [conjugacyWithin_top_eq_conjugatesOf, conjugacyWithin_top_eq_conjugatesOf]
    exact (hxU.trans hxT.symm).conjugatesOf_eq
  have hlocalout : ∀ s : G, s ∈ conjugacyWithin D t ∪ conjugacyWithin D (u * t) →
      IsInvolution s ∧ s ∈ K ∧ s ∉ D := by
    intro s hs
    rw [← hlocal] at hs
    exact hs
  have hutOrbit : u * t ∈ conjugacyWithin D (u * t) := ⟨1, by simp⟩
  have hutout := hlocalout (u * t) (Or.inr hutOrbit)
  have hutnotT : u * t ∉ conjugacyWithin (⊤ : Subgroup G) t := by
    intro h
    have hfiber : u * t ∈ conjugacyWithin (⊤ : Subgroup G) t ∩
        ((K : Set G) \ (D : Set G)) := ⟨h, hutout.2⟩
    rw [htfiber] at hfiber
    exact Set.disjoint_left.mp hdisj hfiber hutOrbit
  have hutU : u * t ∈ conjugacyWithin (⊤ : Subgroup G) u :=
    (hclasses (u * t) hutout.1).resolve_right hutnotT
  refine ⟨?_, hutU⟩
  ext s
  constructor
  · rintro ⟨hsU, hsK, hsD⟩
    have hsI : IsInvolution s := by
      obtain ⟨g, hg⟩ := hsU
      rw [← hg]
      exact isInvolution_rightConjugateElem hu
    have hsLocal : s ∈ conjugacyWithin D t ∪ conjugacyWithin D (u * t) := by
      rw [← hlocal]
      exact ⟨hsI, hsK, hsD⟩
    rcases hsLocal with hsT | hsUT
    · have hsTG : s ∈ conjugacyWithin (⊤ : Subgroup G) t := by
        obtain ⟨d, hd⟩ := hsT
        exact ⟨⟨d, Subgroup.mem_top _⟩, hd⟩
      exact (Set.disjoint_left.mp hglobalDisjoint hsU hsTG).elim
    · exact hsUT
  · intro hsUT
    have hsout := hlocalout s (Or.inr hsUT)
    refine ⟨?_, hsout.2⟩
    rw [conjugacyWithin_top_eq_conjugatesOf]
    have huUT : IsConj u (u * t) := by
      rw [conjugacyWithin_top_eq_conjugatesOf] at hutU
      exact hutU
    obtain ⟨d, hd⟩ := hsUT
    exact huUT.trans (isConj_iff.mpr ⟨(d : G)⁻¹, by simpa only [inv_inv] using hd⟩)

end CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap
