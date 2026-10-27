module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section PCore

variable {G : Type*} [Group G]

theorem pCoreOf_normal (H : Subgroup G) {p g : G} (hp : p ∈ H) (hg : g ∈ Open.pCoreOf 2 H) :
    p * g * p⁻¹ ∈ Open.pCoreOf 2 H := by
  obtain ⟨f, hf, rfl⟩ := hg
  have hf' : f ∈ CFSG.pCore 2 ↥H := by exact hf
  have := (CFSG.pCore_normal (p := 2) (G := ↥H)).conj_mem f hf' ⟨p, hp⟩
  refine ⟨(⟨p, hp⟩ : ↥H) * f * (⟨p, hp⟩ : ↥H)⁻¹, ?_, rfl⟩
  exact this

theorem pCoreOf_pow (H : Subgroup G) {g : G} (hg : g ∈ Open.pCoreOf 2 H) :
    ∃ n : ℕ, g ^ (2 ^ n) = 1 := by
  obtain ⟨f, hf, rfl⟩ := hg
  have hf' : f ∈ CFSG.pCore 2 ↥H := by exact hf
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨f, hf'⟩
  refine ⟨n, ?_⟩
  have := congrArg (fun x : ↥(CFSG.pCore 2 ↥H) => ((x : ↥H) : G)) hn
  simpa using this

end PCore

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
