module

public import Certificates.Data.E8TenTwo
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData2

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Lattice

@[expose] def toV (l : List Int) : Fin Tag.E8.rank → ℤ := fun j => l.getD j.val 0

@[expose] def nuW (i : ℕ) : Fin Tag.E8.rank → ℤ := toV (E8TenTwo.w2.getD i [])

theorem nuW_data : ∀ i ∈ List.range 20, nuW i ∈ mRoots ∧ (cls (nuW i) = 1 ∨ cls (nuW i) = 4) := by
  unfold nuW toV
  simp only [mRoots, rootFinset_E8_eq]
  decide +kernel

theorem nuW_complete : ∀ μ ∈ mRoots, (cls μ = 1 ∨ cls μ = 4) → ∃ i ∈ List.range 20, nuW i = μ := by
  unfold nuW toV
  simp only [mRoots, rootFinset_E8_eq]
  decide +kernel

theorem nuW_inj : ∀ i ∈ List.range 20, ∀ j ∈ List.range 20, nuW i = nuW j → i = j := by
  unfold nuW toV
  decide +kernel

theorem nuW_pair : ∀ k ∈ List.range 10, wm.mulVec (nuW (2 * k)) = nuW (2 * k + 1) ∧
    wm.mulVec (nuW (2 * k + 1)) = nuW (2 * k) := by
  unfold nuW toV
  decide +kernel

@[expose] def trRoot (t q : ℕ) : Fin Tag.E8.rank → ℤ :=
  toV ((E8TenTwo.triples.getD t []).getD q [])

theorem trRoot_P1 : ∀ t ∈ List.range 4, ∀ q ∈ List.range 3,
    trRoot t q ∈ rootFinset Tag.E8 ∧ trRoot t q 7 = 0 := by
  unfold trRoot toV
  simp only [rootFinset_E8_eq]
  decide +kernel

theorem trRoot_P2 : ∀ t ∈ List.range 4, ∀ q ∈ List.range 3, ∀ i : Fin Tag.E8.rank,
    i.val ∉ TwClass.e8Ten.J₂ → trRoot t q i = 0 := by
  unfold trRoot toV
  decide +kernel

theorem trRoot_P3 : ∀ t ∈ List.range 4, wm.mulVec (trRoot t 0) = trRoot t 1 ∧
    wm.mulVec (trRoot t 1) = trRoot t 0 ∧ wm.mulVec (trRoot t 2) = trRoot t 2 ∧
    trRoot t 0 + trRoot t 1 = trRoot t 2 := by
  unfold trRoot toV
  decide +kernel

theorem trRoot_P4 : ∀ t ∈ List.range 4, trRoot t 0 ≠ trRoot t 1 ∧ trRoot t 0 ≠ -trRoot t 1 ∧
    trRoot t 2 + trRoot t 0 ∉ rootFinset Tag.E8 ∧ trRoot t 2 + trRoot t 1 ∉ rootFinset Tag.E8 ∧
    trRoot t 2 ≠ trRoot t 0 ∧ trRoot t 2 ≠ -trRoot t 0 ∧
    trRoot t 2 ≠ trRoot t 1 ∧ trRoot t 2 ≠ -trRoot t 1 := by
  unfold trRoot toV
  simp only [rootFinset_E8_eq]
  decide +kernel

@[expose] def trSrc (t q : ℕ) : List ℕ :=
  E8TenTwo.srcT ((E8TenTwo.triples.getD t []).getD q [])

theorem trRoot_src : ∀ t ∈ List.range 4, ∀ q ∈ List.range 3, ∀ i ∈ List.range 20,
    (((trSrc t q).getD i 20 < 20 ∧ nuW ((trSrc t q).getD i 20) + trRoot t q = nuW i) ∨
      ((trSrc t q).getD i 20 = 20 ∧ ∀ j ∈ List.range 20, nuW j + trRoot t q ≠ nuW i)) := by
  unfold trSrc trRoot nuW toV
  decide +kernel

theorem trRoot_close : ∀ t ∈ List.range 4, ∀ q ∈ List.range 3, ∀ j ∈ List.range 20,
    nuW j + trRoot t q ∈ rootFinset Tag.E8 → ∃ i ∈ List.range 20, nuW i = nuW j + trRoot t q := by
  unfold trRoot nuW toV
  simp only [rootFinset_E8_eq]
  decide +kernel

@[expose] def AdjP1 (β₀ β₁ : Fin Tag.E8.rank → ℤ) : Prop :=
  β₀ ∈ rootFinset Tag.E8 ∧ β₁ ∈ rootFinset Tag.E8 ∧
  -highRoot Tag.E8 + β₀ ∈ rootFinset Tag.E8 ∧ -highRoot Tag.E8 + β₁ ∈ rootFinset Tag.E8 ∧
  -highRoot Tag.E8 ≠ β₀ ∧ -highRoot Tag.E8 ≠ -β₀ ∧ -highRoot Tag.E8 ≠ β₁ ∧ -highRoot Tag.E8 ≠ -β₁

@[expose] def AdjP2 (β₀ β₁ : Fin Tag.E8.rank → ℤ) : Prop :=
  highRoot Tag.E8 ≠ -highRoot Tag.E8 + β₀ ∧ highRoot Tag.E8 ≠ -(-highRoot Tag.E8 + β₀) ∧
  highRoot Tag.E8 ≠ -highRoot Tag.E8 + β₁ ∧ highRoot Tag.E8 ≠ -(-highRoot Tag.E8 + β₁)

@[expose] def AdjP3 (β₀ β₁ : Fin Tag.E8.rank → ℤ) : Prop :=
  β₀ ≠ -highRoot Tag.E8 + β₁ ∧ β₀ ≠ -(-highRoot Tag.E8 + β₁) ∧
  β₀ + (-highRoot Tag.E8 + β₁) ∉ rootFinset Tag.E8 ∧
  -highRoot Tag.E8 + β₀ ≠ β₁ ∧ -highRoot Tag.E8 + β₀ ≠ -β₁ ∧
  -highRoot Tag.E8 + β₀ + β₁ ∉ rootFinset Tag.E8

@[expose] def AdjP4 (β₀ β₁ : Fin Tag.E8.rank → ℤ) : Prop :=
  β₀ ≠ β₁ ∧ β₀ ≠ -β₁ ∧ β₀ + β₁ ∉ rootFinset Tag.E8

theorem adjP1_std : ∀ k ∈ E8TenTwo.stdRep, AdjP1 (nuW (2 * k)) (nuW (2 * k + 1)) := by
  unfold AdjP1 nuW toV
  simp only [rootFinset_E8_eq]
  decide +kernel

theorem adjP2_std : ∀ k ∈ E8TenTwo.stdRep, AdjP2 (nuW (2 * k)) (nuW (2 * k + 1)) := by
  unfold AdjP2 nuW toV
  decide +kernel

theorem adjP3_std : ∀ k ∈ E8TenTwo.stdRep, AdjP3 (nuW (2 * k)) (nuW (2 * k + 1)) := by
  unfold AdjP3 nuW toV
  simp only [rootFinset_E8_eq]
  decide +kernel

theorem adjP4_std : ∀ k ∈ E8TenTwo.stdRep, AdjP4 (nuW (2 * k)) (nuW (2 * k + 1)) := by
  unfold AdjP4 nuW toV
  simp only [rootFinset_E8_eq]
  decide +kernel

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
