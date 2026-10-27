module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.Th2Theta
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.PU3

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Good (M L : Subgroup G) : Prop where
  comp : IsPCompIn 2 M L
  normalizer_le : ∀ R : Subgroup G, R ≤ L → IsPGroup 2 ↥R → R ≠ ⊥ → normalizer (R : Set G) ≤ M
  centralizer_le : ∀ s ∈ M, orderOf s = 2 → (∀ l ∈ L, ⁅l, s⁆ ∈ pPrimeCoreOf 2 M) →
    centralizer ({s} : Set G) ≤ M
  simple : IsSimpleGroup (kBar L)
  nonab : ∃ a b : kBar L, a * b ≠ b * a
  rank : 2 ≤ pRank 2 ↥L

structure Cfg (M L₁ L₂ : Subgroup G) : Prop where
  maximal : IsCoatom M
  good₁ : Good M L₁
  good₂ : Good M L₂
  ne : L₁ ≠ L₂
  only : ∀ L' : Subgroup G, IsPCompIn 2 M L' → L' = L₁ ∨ L' = L₂
  swap : ∃ s ∈ M, cj s L₁ = L₂
  perf : ∀ Y : Subgroup G, Y ≤ M → ⁅Y, Y⁆ = Y → Y ≤ L₁ ⊔ L₂ ⊔ pPrimeCoreOf 2 M

@[expose] def Covers (X L O : Subgroup G) : Prop :=
  ∀ a ∈ L, ∃ x ∈ X, ∃ o ∈ O, a = x * o

omit [Finite G] in
theorem Cfg.symm {M L₁ L₂ : Subgroup G} (h : Cfg M L₁ L₂) : Cfg M L₂ L₁ := by
  refine ⟨h.maximal, h.good₂, h.good₁, h.ne.symm, fun L' hL' => (h.only L' hL').symm, ?_, ?_⟩
  · obtain ⟨s, hs, hsL⟩ := h.swap
    refine ⟨s⁻¹, M.inv_mem hs, ?_⟩
    rw [← hsL]
    exact cj_cj_inv s L₁
  · intro Y hY hperf
    have := h.perf Y hY hperf
    rwa [sup_comm L₂ L₁]

end CFSG.GH74.GLS.PU3
