module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L28Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L28Stabilizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Core

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

variable {X : Type} [Group X] {A : Subgroup X} {w : X}
  {ψ : ↥(normalizer (A : Set X)) →* A5WrTwo}

theorem L28_irreducible (h : L28Hyp A w ψ) {B : Subgroup X} (hBA : B ≤ A)
    (hB : ∀ n : ↥(normalizer (A : Set X)), ψ n ∈ commutator A5WrTwo →
      ∀ b ∈ B, (n : X) * b * (n : X)⁻¹ ∈ B) : B = ⊥ ∨ B = A := by
  classical
  obtain ⟨V, hACG, hMod, hFin, e, σ, h8, hσ, hact⟩ := L28_linear_model h
  letI : AddCommGroup V := hACG
  letI : Module (ZMod 2) V := hMod
  letI : Finite V := hFin
  obtain ⟨v, hv, S, hS, hSiso⟩ := L28_exists_stabilizer h e σ hact
  have hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5), ∀ u ∈ U, σ g u ∈ U) →
        U = ⊥ ∨ U = ⊤ :=
    (Fpf.irreducible_iff_exists_stabilizer σ hσ h8).2 ⟨v, hv, S, hS, hSiso⟩
  let U : Submodule (ZMod 2) V :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup' ((B.subgroupOf A).map e))
  have memU : ∀ u : V, u ∈ U ↔
      ∃ b : ↥A, (b : X) ∈ B ∧ e b = Multiplicative.ofAdd u := by
    intro u
    show Multiplicative.ofAdd u ∈ (B.subgroupOf A).map e ↔ _
    rw [Subgroup.mem_map]
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨b, hb, hbe⟩; exact ⟨b, hb, hbe⟩
    · rintro ⟨b, hb, hbe⟩; exact ⟨b, hb, hbe⟩
  have hU : ∀ g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      ∀ u ∈ U, σ g u ∈ U := by
    intro g u hu
    obtain ⟨b, hb, hbe⟩ := (memU u).mp hu
    obtain ⟨n, hn⟩ := h.surj (A5WrTwo.baseEmb g)
    have hmem : ψ n ∈ commutator A5WrTwo := by
      rw [← A5WrTwo.range_baseEmb]
      exact ⟨g, hn.symm⟩
    refine (memU (σ g u)).mpr
      ⟨e.symm (Multiplicative.ofAdd (σ g (Multiplicative.toAdd (e b)))), ?_, ?_⟩
    · rw [hact n g hn b]
      exact hB n hmem (b : X) hb
    · simp [hbe]
  rcases hirr U hU with hUbot | hUtop
  · left
    apply le_antisymm _ bot_le
    intro x hx
    have hxA : x ∈ A := hBA hx
    let b : ↥A := ⟨x, hxA⟩
    have hUb : Multiplicative.toAdd (e b) ∈ U :=
      (memU _).mpr ⟨b, hx, rfl⟩
    rw [hUbot] at hUb
    have hzero : Multiplicative.toAdd (e b) = 0 := by simpa using hUb
    have he1 : e b = 1 := by
      rw [← ofAdd_toAdd (e b), hzero]
      exact ofAdd_zero
    have hb1 : b = 1 := e.map_eq_one_iff.mp he1
    have hx1 : x = 1 := by
      have := congrArg (fun z : ↥A => (z : X)) hb1
      simpa [b] using this
    rw [hx1]
    simp
  · right
    apply le_antisymm hBA
    intro a ha
    let b : ↥A := ⟨a, ha⟩
    have hUb : Multiplicative.toAdd (e b) ∈ U := by
      rw [hUtop]; exact Submodule.mem_top
    rw [memU] at hUb
    obtain ⟨b', hb', hbe'⟩ := hUb
    have hbb : b' = b := by
      apply e.injective
      simpa using hbe'
    have : (b : X) ∈ B := by simpa [hbb] using hb'
    simpa [b] using this

theorem L28_fixedFree (h : L28Hyp A w ψ) {n : ↥(normalizer (A : Set X))}
    {x : alternatingGroup (Fin 5)} (hx : orderOf x = 5)
    (hn : ψ n = A5WrTwo.baseEmb (x, 1) ∨ ψ n = A5WrTwo.baseEmb (1, x)) :
    ∀ a ∈ A, (n : X) * a * (n : X)⁻¹ = a → a = 1 := by
  classical
  obtain ⟨V, hACG, hMod, hFin, e, σ, h8, hσ, hact⟩ := L28_linear_model h
  letI : AddCommGroup V := hACG
  letI : Module (ZMod 2) V := hMod
  letI : Finite V := hFin
  obtain ⟨v, hv, S, hS, hSiso⟩ := L28_exists_stabilizer h e σ hact
  have hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5), ∀ u ∈ U, σ g u ∈ U) →
        U = ⊥ ∨ U = ⊤ :=
    (Fpf.irreducible_iff_exists_stabilizer σ hσ h8).2 ⟨v, hv, S, hS, hSiso⟩
  obtain ⟨hα, hβ⟩ := Fpf.fixedFree_of_irreducible σ hσ h8 hirr
  obtain ⟨hx1, hx2⟩ := Fpf.fixedFree_of_orderOf_eq_five σ hα hβ hx
  intro a ha hfix
  let b : ↥A := ⟨a, ha⟩
  have key : ∀ g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      ψ n = A5WrTwo.baseEmb g →
      (∀ u : V, σ g u = u → u = 0) → a = 1 := by
    intro g hy hfree
    have h1 : σ g (Multiplicative.toAdd (e b)) = Multiplicative.toAdd (e b) := by
      apply Multiplicative.ofAdd.injective
      have hthis : Multiplicative.ofAdd (σ g (Multiplicative.toAdd (e b))) = e b := by
        have hconj := hact n g hy b
        have hbX : e.symm
            (Multiplicative.ofAdd (σ g (Multiplicative.toAdd (e b)))) = b := by
          apply Subtype.ext
          show ((e.symm
            (Multiplicative.ofAdd (σ g (Multiplicative.toAdd (e b))))) : X) = (b : X)
          rw [hconj]
          simpa [b] using hfix
        have h := congrArg (fun z : ↥A => e z) hbX
        simpa using h
      rw [hthis]
      exact (ofAdd_toAdd (e b)).symm
    have h0 : Multiplicative.toAdd (e b) = 0 := hfree _ h1
    have he1 : e b = 1 := by
      rw [← ofAdd_toAdd (e b), h0]
      exact ofAdd_zero
    have hb1 : b = 1 := e.map_eq_one_iff.mp he1
    have : a = 1 := by
      have := congrArg (fun z : ↥A => (z : X)) hb1
      simpa [b] using this
    exact this
  rcases hn with hn | hn
  · exact key (x, 1) hn hx1
  · exact key (1, x) hn hx2

end CFSG.EvenSporadicStandard.HNRecog.Harada
