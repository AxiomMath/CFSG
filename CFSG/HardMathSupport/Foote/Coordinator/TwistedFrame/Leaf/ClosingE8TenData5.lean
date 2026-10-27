module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData4

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Lattice

@[expose] def vA6 : Fin Tag.E8.rank → ℤ := Pi.single 5 1
@[expose] def vA7 : Fin Tag.E8.rank → ℤ := Pi.single 6 1
@[expose] def vGc : Fin Tag.E8.rank → ℤ := Pi.single 5 1 + Pi.single 6 1
@[expose] def vGp : Fin Tag.E8.rank → ℤ := -(Pi.single 5 1 + Pi.single 6 1)

@[expose] def Vz (ξ : Fin Tag.E8.rank → ℤ) : Prop :=
  ξ ∉ mRoots ∨ ξ + vGp ∈ rootFinset Tag.E8 ∨ ξ + vGc ∈ rootFinset Tag.E8

@[expose] def certA (ν : Fin Tag.E8.rank → ℤ) : Prop :=
  ν + vA6 ∈ mRoots ∧ ν + vA6 + vGp ∈ rootFinset Tag.E8 ∧
  Vz (ν + vA6) ∧ Vz (ν + vA6 - vGc) ∧ Vz (ν + vA6 - vA7) ∧ Vz (ν + vA6 - vA7 - vGc) ∧
  Vz (ν - vGc) ∧ Vz (ν - vA7) ∧ Vz (ν - vA7 - vGc)

@[expose] def certB (ν : Fin Tag.E8.rank → ℤ) : Prop :=
  ν + vA7 ∈ mRoots ∧ ν + vA7 + vGp ∈ rootFinset Tag.E8 ∧
  Vz (ν + vA7) ∧ Vz (ν + vA7 - vGc) ∧ Vz (ν - vGc) ∧
  Vz (ν + vA7 - vA6) ∧ Vz (ν + vA7 - vA6 - vGc) ∧ Vz (ν + vA7 - vA6 - vA7) ∧
  Vz (ν + vA7 - vA6 - vA7 - vGc)

theorem S0_cases : ∀ ν ∈ mRoots, (cls ν = 2 ∨ cls ν = 3) → ν + vGp ∉ rootFinset Tag.E8 →
    ν + vGc ∉ rootFinset Tag.E8 → certA ν ∨ certB ν := by
  unfold certA certB Vz vA6 vA7 vGc vGp
  simp only [mRoots, rootFinset_E8_eq]
  decide +kernel

theorem mRoots_not_S₁ : ∀ μ ∈ mRoots, ∃ α ∈ rootFinset Tag.E8,
    (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → α i = 0) ∧ iform μ α ≠ 0 := by
  simp only [mRoots, rootFinset_E8_eq]
  decide +kernel

theorem zP2 : vS1 + (-highRoot Tag.E8 + vU1) = vGp := by
  unfold vS1 vU1 vGp
  decide +kernel

theorem zP4 : vS3 + (-highRoot Tag.E8 + vU3) = vGc := by
  unfold vS3 vU3 vGc
  decide +kernel

theorem vGp_data : vGp ∈ rootFinset Tag.E8 ∧ vGp 7 = 0 := by
  unfold vGp
  simp only [rootFinset_E8_eq]
  decide +kernel

theorem vGc_data : vGc ∈ rootFinset Tag.E8 ∧ vGc 7 = 0 := by
  unfold vGc
  simp only [rootFinset_E8_eq]
  decide +kernel

theorem mRoots_closed : ∀ ν ∈ mRoots, (ν + vGp ∈ rootFinset Tag.E8 → ν + vGp ∈ mRoots) ∧
    (ν + vGc ∈ rootFinset Tag.E8 → ν + vGc ∈ mRoots) := by
  unfold vGp vGc
  simp only [mRoots, rootFinset_E8_eq]
  decide +kernel

theorem uneg_comm : ∀ γ ∈ ([vA6, vA7, vGc] : List (Fin Tag.E8.rank → ℤ)),
    γ ≠ -highRoot Tag.E8 ∧ γ ≠ -(-highRoot Tag.E8) ∧ γ + -highRoot Tag.E8 ∉ rootFinset Tag.E8 := by
  unfold vA6 vA7 vGc
  simp only [rootFinset_E8_eq]
  decide +kernel

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
