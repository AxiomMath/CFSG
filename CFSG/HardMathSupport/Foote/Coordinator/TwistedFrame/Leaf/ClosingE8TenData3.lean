module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData2
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData3K

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Lattice

@[expose] def νWord : List (Fin Tag.E8.rank) :=
  [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 2, 3, 0, 2, 1,
    3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4]

@[expose] def νm : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := wordMat Tag.E8 νWord

@[expose] def theta2 : Fin Tag.E8.rank → ℤ := ![1, 1, 1, 1, 0, 0, 0, 0]

theorem νm_theta : νm.mulVec (highRoot Tag.E8) = theta2 := by
  have hν : νm = e8t3K_νLit := e8t3K_wordν
  rw [hν]
  decide +kernel

theorem wm_theta2 : wm.mulVec theta2 = theta2 := by
  rw [e8t3K_wm]
  decide +kernel

theorem wm_νm : wm * νm = νm * wm := by
  have hν : νm = e8t3K_νLit := e8t3K_wordν
  rw [e8t3K_wm, hν]
  decide +kernel

theorem theta2_S₂ : theta2 ∈ rootFinset Tag.E8 ∧
    ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → theta2 i = 0 := by
  rw [e8t3K_mem_iff]
  decide +kernel

theorem neg_theta2_S₂ : -theta2 ∈ rootFinset Tag.E8 ∧
    ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → (-theta2) i = 0 := by
  rw [e8t3K_mem_iff]
  decide +kernel

theorem νm_negTheta : νm.mulVec (-highRoot Tag.E8) = -theta2 := by
  have hν : νm = e8t3K_νLit := e8t3K_wordν
  rw [hν]
  decide +kernel

theorem νm_listA : ∀ γ ∈ listA, νm.mulVec γ ∈ rootFinset Tag.E8 ∧ ∀ α ∈ rootFinset Tag.E8,
    (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → α i = 0) → iform (νm.mulVec γ) α = 0 := by
  have hν : νm = e8t3K_νLit := e8t3K_wordν
  rw [hν]
  have h : ∀ γ ∈ listA, List.ofFn (e8t3K_νLit.mulVec γ) ∈ Tag.E8.artifactRoots ∧
      ∀ l ∈ Tag.E8.artifactRoots, (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ →
        e8t3K_vec l i = 0) → iform (e8t3K_νLit.mulVec γ) (e8t3K_vec l) = 0 := by
    decide +kernel
  intro γ hγ
  exact ⟨e8t3K_mem_iff.2 (h γ hγ).1, e8t3K_forall (Q := fun α =>
    (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → α i = 0) →
      iform (e8t3K_νLit.mulVec γ) α = 0) (h γ hγ).2⟩

theorem νm_listB : ∀ γ ∈ listB, νm.mulVec γ ∈ rootFinset Tag.E8 ∧
    ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → (νm.mulVec γ) i = 0 := by
  have hν : νm = e8t3K_νLit := e8t3K_wordν
  rw [hν]
  simp only [e8t3K_mem_iff]
  decide +kernel

@[expose] def bA0 : Fin Tag.E8.rank → ℤ := ![1, 1, 1, 2, 1, 1, 1, 1]
@[expose] def bA1 : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 5, 4, 3, 2, 1]
@[expose] def uA0 : Fin Tag.E8.rank → ℤ := ![1, 2, 2, 3, 2, 2, 1, 1]
@[expose] def uA1 : Fin Tag.E8.rank → ℤ := ![2, 2, 3, 4, 3, 2, 2, 1]
@[expose] def dA0 : Fin Tag.E8.rank → ℤ := ![0, 0, -1, -1, -1, -1, 0, 0]
@[expose] def dA1 : Fin Tag.E8.rank → ℤ := ![1, 1, 1, 1, 1, 1, 0, 0]
@[expose] def vA0 : Fin Tag.E8.rank → ℤ := ![1, 2, 2, 4, 3, 2, 1, 1]
@[expose] def vA1 : Fin Tag.E8.rank → ℤ := ![1, 1, 2, 2, 2, 1, 1, 1]
@[expose] def mA0 : Fin Tag.E8.rank → ℤ := ![1, 2, 3, 5, 4, 3, 2, 1]

theorem caseA_beta : bA0 ∈ mRoots ∧ bA1 ∈ mRoots ∧ (cls bA0 = 1 ∨ cls bA0 = 4) ∧
    (cls bA1 = 1 ∨ cls bA1 = 4) ∧ wm.mulVec bA0 = bA1 ∧ wm.mulVec bA1 = bA0 ∧ bA0 ≠ bA1 ∧
    bA0 + bA1 ∉ rootFinset Tag.E8 := by
  simp only [mRoots, Finset.mem_filter, e8t3K_mem_iff]
  rw [e8t3K_wm]
  decide +kernel

theorem caseA_u : uA0 ∈ mRoots ∧ uA1 ∈ mRoots ∧ (cls uA0 = 2 ∨ cls uA0 = 3) ∧
    (cls uA1 = 2 ∨ cls uA1 = 3) ∧ νm.mulVec uA0 = bA0 ∧ νm.mulVec uA1 = bA1 ∧ uA0 ≠ uA1 := by
  have hν : νm = e8t3K_νLit := e8t3K_wordν
  simp only [mRoots, Finset.mem_filter, e8t3K_mem_iff]
  rw [hν]
  decide +kernel

theorem caseA_delta : dA0 ∈ rootFinset Tag.E8 ∧ dA0 7 = 0 ∧ dA1 ∈ rootFinset Tag.E8 ∧ dA1 7 = 0 ∧
    wm.mulVec dA0 = dA1 ∧ wm.mulVec dA1 = dA0 ∧ dA0 ≠ dA1 ∧ dA0 + dA1 ∉ rootFinset Tag.E8 := by
  simp only [mRoots, Finset.mem_filter, e8t3K_mem_iff]
  rw [e8t3K_wm]
  decide +kernel

theorem caseA_v : vA0 ∈ mRoots ∧ vA1 ∈ mRoots ∧ (cls vA0 = 2 ∨ cls vA0 = 3) ∧
    (cls vA1 = 2 ∨ cls vA1 = 3) ∧ νm.mulVec vA0 = dA0 ∧ νm.mulVec vA1 = dA1 ∧ vA0 ≠ vA1 := by
  have hν : νm = e8t3K_νLit := e8t3K_wordν
  simp only [mRoots, Finset.mem_filter, e8t3K_mem_iff]
  rw [hν]
  decide +kernel

theorem caseA_mu : mA0 ∈ mRoots ∧ (cls mA0 = 1 ∨ cls mA0 = 4) ∧ mA0 + dA0 ∈ rootFinset Tag.E8 ∧
    mA0 + dA0 ∈ mRoots ∧ (cls (mA0 + dA0) = 2 ∨ cls (mA0 + dA0) = 3) := by
  simp only [mRoots, Finset.mem_filter, e8t3K_mem_iff]
  decide +kernel

@[expose] def bB0 : Fin Tag.E8.rank → ℤ := ![1, 2, 2, 3, 2, 2, 1, 1]
@[expose] def bB1 : Fin Tag.E8.rank → ℤ := ![2, 2, 3, 4, 3, 2, 2, 1]
@[expose] def uB0 : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 5, 4, 3, 2, 1]
@[expose] def uB1 : Fin Tag.E8.rank → ℤ := ![1, 1, 1, 2, 1, 1, 1, 1]
@[expose] def dB0 : Fin Tag.E8.rank → ℤ := ![0, -1, -1, -2, -2, -2, -1, 0]
@[expose] def dB1 : Fin Tag.E8.rank → ℤ := ![1, 2, 2, 3, 2, 1, 0, 0]
@[expose] def vB0 : Fin Tag.E8.rank → ℤ := ![0, 1, 0, 1, 1, 1, 1, 1]
@[expose] def vB1 : Fin Tag.E8.rank → ℤ := ![2, 2, 3, 4, 4, 3, 2, 1]
@[expose] def mB0 : Fin Tag.E8.rank → ℤ := ![1, 2, 2, 4, 3, 3, 2, 1]

theorem caseB_beta : bB0 ∈ mRoots ∧ bB1 ∈ mRoots ∧ (cls bB0 = 2 ∨ cls bB0 = 3) ∧
    (cls bB1 = 2 ∨ cls bB1 = 3) ∧ wm.mulVec bB0 = bB1 ∧ wm.mulVec bB1 = bB0 ∧ bB0 ≠ bB1 ∧
    bB0 + bB1 ∉ rootFinset Tag.E8 := by
  simp only [mRoots, Finset.mem_filter, e8t3K_mem_iff]
  rw [e8t3K_wm]
  decide +kernel

theorem caseB_u : uB0 ∈ mRoots ∧ uB1 ∈ mRoots ∧ (cls uB0 = 1 ∨ cls uB0 = 4) ∧
    (cls uB1 = 1 ∨ cls uB1 = 4) ∧ νm.mulVec uB0 = bB0 ∧ νm.mulVec uB1 = bB1 ∧ uB0 ≠ uB1 := by
  have hν : νm = e8t3K_νLit := e8t3K_wordν
  simp only [mRoots, Finset.mem_filter, e8t3K_mem_iff]
  rw [hν]
  decide +kernel

theorem caseB_delta : dB0 ∈ rootFinset Tag.E8 ∧ dB0 7 = 0 ∧ dB1 ∈ rootFinset Tag.E8 ∧ dB1 7 = 0 ∧
    wm.mulVec dB0 = dB1 ∧ wm.mulVec dB1 = dB0 ∧ dB0 ≠ dB1 ∧ dB0 + dB1 ∉ rootFinset Tag.E8 := by
  simp only [mRoots, Finset.mem_filter, e8t3K_mem_iff]
  rw [e8t3K_wm]
  decide +kernel

theorem caseB_v : vB0 ∈ mRoots ∧ vB1 ∈ mRoots ∧ (cls vB0 = 1 ∨ cls vB0 = 4) ∧
    (cls vB1 = 1 ∨ cls vB1 = 4) ∧ νm.mulVec vB0 = dB0 ∧ νm.mulVec vB1 = dB1 ∧ vB0 ≠ vB1 := by
  have hν : νm = e8t3K_νLit := e8t3K_wordν
  simp only [mRoots, Finset.mem_filter, e8t3K_mem_iff]
  rw [hν]
  decide +kernel

theorem caseB_mu : mB0 ∈ mRoots ∧ (cls mB0 = 2 ∨ cls mB0 = 3) ∧ mB0 + dB0 ∈ rootFinset Tag.E8 ∧
    mB0 + dB0 ∈ mRoots ∧ (cls (mB0 + dB0) = 1 ∨ cls (mB0 + dB0) = 4) := by
  simp only [mRoots, Finset.mem_filter, e8t3K_mem_iff]
  decide +kernel

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
