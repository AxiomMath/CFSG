module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData2

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Lattice

structure PairData (β₀ β₁ : Fin Tag.E8.rank → ℤ) : Prop where
  h₀ : β₀ ∈ rootFinset Tag.E8
  h₁ : β₁ ∈ rootFinset Tag.E8
  d₀ : β₀ 7 = 1
  d₁ : β₁ 7 = 1
  s₀ : β₀ ∈ sRoots1
  s₁ : β₁ ∈ sRoots1
  w₀ : wm.mulVec β₀ = β₁
  w₁ : wm.mulVec β₁ = β₀
  ne : β₀ ≠ β₁
  ne' : β₀ ≠ -β₁
  sum : β₀ + β₁ ∉ rootFinset Tag.E8
  m₀ : -highRoot Tag.E8 ≠ β₀
  m₀' : -highRoot Tag.E8 ≠ -β₀
  r₀ : -highRoot Tag.E8 + β₀ ∈ rootFinset Tag.E8
  m₁ : -highRoot Tag.E8 ≠ β₁
  m₁' : -highRoot Tag.E8 ≠ -β₁
  r₁ : -highRoot Tag.E8 + β₁ ∈ rootFinset Tag.E8
  z₀ : β₀ ≠ -highRoot Tag.E8 + β₁
  z₀' : β₀ ≠ -(-highRoot Tag.E8 + β₁)
  zr : β₀ + (-highRoot Tag.E8 + β₁) ∈ rootFinset Tag.E8
  zdeg : (β₀ + (-highRoot Tag.E8 + β₁)) 7 = 0
  c₀Z : -highRoot Tag.E8 + β₀ ≠ β₀ + (-highRoot Tag.E8 + β₁) ∧
    -highRoot Tag.E8 + β₀ ≠ -(β₀ + (-highRoot Tag.E8 + β₁)) ∧
    -highRoot Tag.E8 + β₀ + (β₀ + (-highRoot Tag.E8 + β₁)) ∉ rootFinset Tag.E8
  c₀₁ : -highRoot Tag.E8 + β₀ ≠ -highRoot Tag.E8 + β₁ ∧
    -highRoot Tag.E8 + β₀ ≠ -(-highRoot Tag.E8 + β₁) ∧
    -highRoot Tag.E8 + β₀ + (-highRoot Tag.E8 + β₁) ∉ rootFinset Tag.E8
  cZ₁ : β₀ + (-highRoot Tag.E8 + β₁) ≠ -highRoot Tag.E8 + β₁ ∧
    β₀ + (-highRoot Tag.E8 + β₁) ≠ -(-highRoot Tag.E8 + β₁) ∧
    β₀ + (-highRoot Tag.E8 + β₁) + (-highRoot Tag.E8 + β₁) ∉ rootFinset Tag.E8

@[expose] def PairDataP1 (β₀ β₁ : Fin Tag.E8.rank → ℤ) : Prop :=
  (β₀ ∈ rootFinset Tag.E8) ∧ (β₁ ∈ rootFinset Tag.E8) ∧ (β₀ 7 = 1) ∧ (β₁ 7 = 1) ∧
  (wm.mulVec β₀ = β₁) ∧ (wm.mulVec β₁ = β₀) ∧ (β₀ ≠ β₁) ∧ (β₀ ≠ -β₁) ∧
  (β₀ + β₁ ∉ rootFinset Tag.E8)

@[expose] def PairDataP2 (β₀ β₁ : Fin Tag.E8.rank → ℤ) : Prop := (β₀ ∈ sRoots1) ∧ (β₁ ∈ sRoots1)

@[expose] def PairDataP3 (β₀ β₁ : Fin Tag.E8.rank → ℤ) : Prop :=
  (-highRoot Tag.E8 ≠ β₀) ∧ (-highRoot Tag.E8 ≠ -β₀) ∧ (-highRoot Tag.E8 + β₀ ∈ rootFinset Tag.E8) ∧
  (-highRoot Tag.E8 ≠ β₁) ∧ (-highRoot Tag.E8 ≠ -β₁) ∧ (-highRoot Tag.E8 + β₁ ∈ rootFinset Tag.E8) ∧
  (β₀ ≠ -highRoot Tag.E8 + β₁) ∧ (β₀ ≠ -(-highRoot Tag.E8 + β₁)) ∧
  (β₀ + (-highRoot Tag.E8 + β₁) ∈ rootFinset Tag.E8) ∧
  ((β₀ + (-highRoot Tag.E8 + β₁)) 7 = 0)

@[expose] def PairDataP4 (β₀ β₁ : Fin Tag.E8.rank → ℤ) : Prop :=
  (-highRoot Tag.E8 + β₀ ≠ β₀ + (-highRoot Tag.E8 + β₁) ∧
    -highRoot Tag.E8 + β₀ ≠ -(β₀ + (-highRoot Tag.E8 + β₁)) ∧
    -highRoot Tag.E8 + β₀ + (β₀ + (-highRoot Tag.E8 + β₁)) ∉ rootFinset Tag.E8) ∧
  (-highRoot Tag.E8 + β₀ ≠ -highRoot Tag.E8 + β₁ ∧
    -highRoot Tag.E8 + β₀ ≠ -(-highRoot Tag.E8 + β₁) ∧
    -highRoot Tag.E8 + β₀ + (-highRoot Tag.E8 + β₁) ∉ rootFinset Tag.E8) ∧
  (β₀ + (-highRoot Tag.E8 + β₁) ≠ -highRoot Tag.E8 + β₁ ∧
    β₀ + (-highRoot Tag.E8 + β₁) ≠ -(-highRoot Tag.E8 + β₁) ∧
    β₀ + (-highRoot Tag.E8 + β₁) + (-highRoot Tag.E8 + β₁) ∉ rootFinset Tag.E8)

theorem PairData.of_P {β₀ β₁ : Fin Tag.E8.rank → ℤ} (h1 : PairDataP1 β₀ β₁)
    (h2 : PairDataP2 β₀ β₁) (h3 : PairDataP3 β₀ β₁) (h4 : PairDataP4 β₀ β₁) :
    PairData β₀ β₁ := by
  obtain ⟨h₀, h₁, d₀, d₁, w₀, w₁, ne, ne', sum⟩ := h1
  obtain ⟨s₀, s₁⟩ := h2
  obtain ⟨m₀, m₀', r₀, m₁, m₁', r₁, z₀, z₀', zr, zdeg⟩ := h3
  obtain ⟨c₀Z, c₀₁, cZ₁⟩ := h4
  exact ⟨h₀, h₁, d₀, d₁, s₀, s₁, w₀, w₁, ne, ne', sum, m₀, m₀', r₀, m₁, m₁', r₁, z₀, z₀', zr,
    zdeg, c₀Z, c₀₁, cZ₁⟩

@[expose] def vS1 : Fin Tag.E8.rank → ℤ := ![0, 0, 0, 0, 0, 0, 0, 1]
@[expose] def vU1 : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 6, 5, 3, 2, 1]
@[expose] def vS3 : Fin Tag.E8.rank → ℤ := ![0, 0, 0, 0, 0, 1, 1, 1]
@[expose] def vU3 : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 6, 5, 4, 3, 1]

theorem pairP1_P2 : PairDataP1 vS1 vU1 := by
  unfold PairDataP1
  simp only [sRoots1, rootFinset_E8_eq]
  decide +kernel

theorem pairP2_P2 : PairDataP2 vS1 vU1 := by
  unfold PairDataP2
  simp only [sRoots1, rootFinset_E8_eq]
  decide +kernel

theorem pairP3_P2 : PairDataP3 vS1 vU1 := by
  unfold PairDataP3
  simp only [sRoots1, rootFinset_E8_eq]
  decide +kernel

theorem pairP4_P2 : PairDataP4 vS1 vU1 := by
  unfold PairDataP4
  simp only [sRoots1, rootFinset_E8_eq]
  decide +kernel

theorem pairData_P2 : PairData vS1 vU1 :=
  PairData.of_P pairP1_P2 pairP2_P2 pairP3_P2 pairP4_P2

theorem pairP1_P4 : PairDataP1 vS3 vU3 := by
  unfold PairDataP1
  simp only [sRoots1, rootFinset_E8_eq]
  decide +kernel

theorem pairP2_P4 : PairDataP2 vS3 vU3 := by
  unfold PairDataP2
  simp only [sRoots1, rootFinset_E8_eq]
  decide +kernel

theorem pairP3_P4 : PairDataP3 vS3 vU3 := by
  unfold PairDataP3
  simp only [sRoots1, rootFinset_E8_eq]
  decide +kernel

theorem pairP4_P4 : PairDataP4 vS3 vU3 := by
  unfold PairDataP4
  simp only [sRoots1, rootFinset_E8_eq]
  decide +kernel

theorem pairData_P4 : PairData vS3 vU3 :=
  PairData.of_P pairP1_P4 pairP2_P4 pairP3_P4 pairP4_P4

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
