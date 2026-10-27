module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData2K

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Lattice

@[expose] def fixedRoots : List (Fin Tag.E8.rank → ℤ) :=
  [Pi.single 2 1 + Pi.single 3 1, -(Pi.single 2 1 + Pi.single 3 1),
    Pi.single 5 1 + Pi.single 6 1, -(Pi.single 5 1 + Pi.single 6 1)]

@[expose] def perpPairs : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)) :=
  [(Pi.single 0 1, Pi.single 1 1), (-Pi.single 0 1, -Pi.single 1 1)]

@[expose] def a2Triples : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ) ×
    (Fin Tag.E8.rank → ℤ)) :=
  [(Pi.single 2 1, Pi.single 3 1, Pi.single 2 1 + Pi.single 3 1),
    (-Pi.single 2 1, -Pi.single 3 1, -(Pi.single 2 1 + Pi.single 3 1)),
    (Pi.single 5 1, Pi.single 6 1, Pi.single 5 1 + Pi.single 6 1),
    (-Pi.single 5 1, -Pi.single 6 1, -(Pi.single 5 1 + Pi.single 6 1))]

@[expose] def wm : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := wordMat Tag.E8 TwClass.wordE8Ten

theorem fixedRoots_data : ∀ γ ∈ fixedRoots, γ ∈ lxRoots ∧ wm.mulVec γ = γ := by
  have hw : wm = e8tK_wLit := e8tK_wordw
  simp only [hw, e8tK_lx_iff]
  decide +kernel

theorem perpPairs_data : ∀ p ∈ perpPairs, p.1 ∈ lxRoots ∧ p.2 ∈ lxRoots ∧ wm.mulVec p.1 = p.2 ∧
    wm.mulVec p.2 = p.1 ∧ p.1 ≠ p.2 ∧ p.1 ≠ -p.2 ∧ p.1 + p.2 ∉ rootFinset Tag.E8 := by
  have hw : wm = e8tK_wLit := e8tK_wordw
  simp only [hw, e8tK_lx_iff, e8tK_mem_iff]
  decide +kernel

theorem a2Triples_data : ∀ t ∈ a2Triples, t.1 ∈ lxRoots ∧ t.2.1 ∈ lxRoots ∧ t.2.2 ∈ lxRoots ∧
    wm.mulVec t.1 = t.2.1 ∧ wm.mulVec t.2.1 = t.1 ∧ wm.mulVec t.2.2 = t.2.2 ∧
    t.1 + t.2.1 = t.2.2 ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ -t.2.1 ∧ t.2.2 + t.1 ∉ rootFinset Tag.E8 ∧
    t.2.2 + t.2.1 ∉ rootFinset Tag.E8 ∧ t.2.2 ≠ t.1 ∧ t.2.2 ≠ -t.1 ∧ t.2.2 ≠ t.2.1 ∧
    t.2.2 ≠ -t.2.1 := by
  have hw : wm = e8tK_wLit := e8tK_wordw
  simp only [hw, e8tK_lx_iff, e8tK_mem_iff]
  decide +kernel

theorem s2_data : ∀ γ ∈ ([Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1,
    Pi.single 2 1 + Pi.single 3 1] : List (Fin Tag.E8.rank → ℤ)),
    γ ∈ rootFinset Tag.E8 ∧ ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → γ i = 0 := by
  simp only [e8tK_mem_iff]
  decide +kernel

theorem s2_data_neg : ∀ γ ∈ ([Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1,
    Pi.single 2 1 + Pi.single 3 1] : List (Fin Tag.E8.rank → ℤ)),
    -γ ∈ rootFinset Tag.E8 ∧ ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → (-γ) i = 0 := by
  simp only [e8tK_mem_iff]
  decide +kernel

theorem s1_data : ∀ γ ∈ ([Pi.single 5 1, Pi.single 6 1, Pi.single 5 1 + Pi.single 6 1] :
    List (Fin Tag.E8.rank → ℤ)),
    γ ∈ rootFinset Tag.E8 ∧ ∀ α ∈ rootFinset Tag.E8,
      (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → α i = 0) → iform γ α = 0 := by
  simp only [e8tK_ball_root]
  simp only [e8tK_mem_iff]
  decide +kernel

theorem s1_data_neg : ∀ γ ∈ ([Pi.single 5 1, Pi.single 6 1, Pi.single 5 1 + Pi.single 6 1] :
    List (Fin Tag.E8.rank → ℤ)),
    -γ ∈ rootFinset Tag.E8 ∧ ∀ α ∈ rootFinset Tag.E8,
      (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → α i = 0) → iform (-γ) α = 0 := by
  simp only [e8tK_ball_root]
  simp only [e8tK_mem_iff]
  decide +kernel

@[expose] def listA : List (Fin Tag.E8.rank → ℤ) :=
  [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1, Pi.single 2 1 + Pi.single 3 1,
    -Pi.single 0 1, -Pi.single 1 1, -Pi.single 2 1, -Pi.single 3 1,
    -(Pi.single 2 1 + Pi.single 3 1)]

@[expose] def listB : List (Fin Tag.E8.rank → ℤ) :=
  [Pi.single 5 1, Pi.single 6 1, Pi.single 5 1 + Pi.single 6 1,
    -Pi.single 5 1, -Pi.single 6 1, -(Pi.single 5 1 + Pi.single 6 1)]

theorem listA_data : ∀ γ ∈ listA, γ ∈ rootFinset Tag.E8 ∧
    ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → γ i = 0 := by
  simp only [e8tK_mem_iff]
  decide +kernel

theorem listB_data : ∀ γ ∈ listB, γ ∈ rootFinset Tag.E8 ∧ ∀ α ∈ rootFinset Tag.E8,
    (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → α i = 0) → iform γ α = 0 := by
  simp only [e8tK_ball_root]
  simp only [e8tK_mem_iff]
  decide +kernel

theorem wm_deg1 : ∀ μ ∈ deg1Roots, wm.mulVec μ ∈ deg1Roots := by
  have hw : wm = e8tK_wLit := e8tK_wordw
  simp only [e8tK_ball_deg1]
  simp only [hw, e8tK_deg1_iff]
  decide +kernel

theorem wm_theta : wm.mulVec (highRoot Tag.E8) = highRoot Tag.E8 := by
  have hw : wm = e8tK_wLit := e8tK_wordw
  rw [hw]
  decide +kernel

theorem wm_mRoots : ∀ μ ∈ mRoots, wm.mulVec μ ∈ mRoots ∧ cls (wm.mulVec μ) = 5 - cls μ := by
  have hw : wm = e8tK_wLit := e8tK_wordw
  simp only [e8tK_ball_m]
  simp only [hw, e8tK_m_iff]
  decide +kernel

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
