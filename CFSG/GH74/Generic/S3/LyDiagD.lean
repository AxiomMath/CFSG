module

public import CFSG.GH74.Generic.S3.LyDiagA
public import CFSG.GH74.Generic.S1.SymTransport
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.S3.LyPump
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic Subgroup CFSG.LocalAnalysis.ComponentInitial

section Sign

theorem not_mem_commutator_of_swapped {Y H : Type*} [Group Y] [Group H] (π : Y →* H)
    {L L' : Subgroup H} (P : Subgroup H → Prop) (hP : ∀ J g, P J → P (conjSub g J)) (hL : P L)
    (hLL' : L' ≠ L) (hcomp : ∀ J, P J → J = L ∨ J = L') {g₀ : Y} (hg₀ : conjSub (π g₀) L = L') :
    g₀ ∉ commutator Y := by
  classical
  have hL' : P L' := hg₀ ▸ hP L (π g₀) hL
  have hperm : ∀ a : H, (conjSub a L = L → conjSub a L' = L') ∧ (conjSub a L = L' → conjSub a L' = L) := by
    intro a
    have hinj : ∀ J J' : Subgroup H, conjSub a J = conjSub a J' → J = J' := fun J J' h => by
      rw [← conjSub_inv_conjSub a J, h, conjSub_inv_conjSub]
    have hmem := hcomp _ (hP L' a hL')
    constructor
    · intro h
      rcases hmem with h' | h'
      · exact absurd (hinj _ _ (h'.trans h.symm)) hLL'
      · exact h'
    · intro h
      rcases hmem with h' | h'
      · exact h'
      · exact absurd (hinj _ _ (h'.trans h.symm)) hLL'
  let σ : Y → ZMod 2 := fun g => if conjSub (π g) L = L then 0 else 1
  have hσ : ∀ g h : Y, σ (g * h) = σ g + σ h := by
    intro g h
    have hgh : conjSub (π (g * h)) L = conjSub (π g) (conjSub (π h) L) := by
      rw [map_mul, conjSub_mul]
    have hmh := hcomp _ (hP L (π h) hL)
    have hmg := hcomp _ (hP L (π g) hL)
    simp only [σ, hgh]
    rcases hmh with hh | hh
    · rw [hh]
      simp
    · rw [hh]
      rcases hmg with hg | hg
      · rw [(hperm (π g)).1 hg]
        simp [hg, hLL']
      · have hgL : ¬ conjSub (π g) L = L := by
          rw [hg]
          exact hLL'
        rw [(hperm (π g)).2 hg]
        simp [hgL, hLL']
        decide
  let f : Y →* Multiplicative (ZMod 2) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (σ g)) fun g h => by
      rw [hσ]
      rfl
  intro hmem
  have hker : g₀ ∈ f.ker := Abelianization.commutator_subset_ker f hmem
  rw [MonoidHom.mem_ker] at hker
  have h1 : σ g₀ = 0 := by
    have := congrArg Multiplicative.toAdd hker
    simpa [f] using this
  have h2 : σ g₀ = 1 := by
    have : ¬ conjSub (π g₀) L = L := by
      rw [hg₀]
      exact hLL'
    simp [σ, this]
  rw [h1] at h2
  exact absurd h2 (by decide)

end Sign

section Conj

theorem center_eq_bot_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : center A = ⊥) : center B = ⊥ := by
  have := Subgroup.map_center_eq e
  rw [← this, h, Subgroup.map_bot]

theorem not_isConj_of_centerless_component {G : Type} [Group G] (y x : G)
    (K : Subgroup (CentralizerBar x)) (hK : CFSG.IsComponent K) (hKc : center ↥K = ⊥)
    (hcomp : ∀ J : Subgroup (CentralizerBar y), CFSG.IsComponent J → center ↥J ≠ ⊥) :
    ¬ IsConj y x := by
  rw [isConj_iff]
  rintro ⟨g, hg⟩
  subst hg
  let e := CFSG.GH74.Generic.S1.barConj y g
  have hJ : CFSG.IsComponent (K.map e.symm.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv e.symm hK
  apply hcomp _ hJ
  exact center_eq_bot_of_mulEquiv' (K.equivMapOfInjective _ e.symm.injective) hKc

end Conj

end CFSG.GH74.Generic.S3
