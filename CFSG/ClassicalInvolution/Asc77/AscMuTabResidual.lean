module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallF
public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallB
public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallD
public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallE

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected

namespace MuTab

variable (p f : ℕ) [Fact p.Prime]

structure MuResidual : Prop where
  pOmegaOdd3 : p ≠ 2 → 5 ≤ p ^ f → piSign p f = false →
    ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), TransSection p f Φ → Φ.Nonempty →
      (⊤ : Subgroup X) ∉ Φ → HasLieType p f Φ .POmegaOdd 3 →
        ∃ K ∈ Φ, dComp Φ K ≠ dstarComp Φ K
  pOmegaMinus4 : p ≠ 2 → 5 ≤ p ^ f → piSign p f = false →
    ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), TransSection p f Φ → Φ.Nonempty →
      (⊤ : Subgroup X) ∉ Φ → HasLieType p f Φ .POmegaMinus 4 →
        ∃ K ∈ Φ, dComp Φ K ≠ dstarComp Φ K
  g2 : p ≠ 2 → 5 ≤ p ^ f → ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)),
    TransSection p f Φ → Φ.Nonempty → (⊤ : Subgroup X) ∉ Φ → HasLieType p f Φ .G2 0 →
      ∃ K ∈ Φ, (omegaStarNbr Φ K).Nonempty
  trialityD4 : p ≠ 2 → 5 ≤ p ^ f → ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)),
    TransSection p f Φ → Φ.Nonempty → (⊤ : Subgroup X) ∉ Φ → HasLieType p f Φ .trialityD4 0 →
      ∃ K ∈ Φ, (omegaStarNbr Φ K).Nonempty
  pOmegaPlus4 : SmallShape p f .POmegaPlus 4

variable {p f}

theorem muSmallShapes_of_residual (hr : MuResidual p f) : MuSmallShapes p f where
  psl3 := smallShape_psl3
  psl4 := smallShape_psl4
  psl5 := smallShape_psl5
  psu3 := smallShape_psu3
  psu4 := smallShape_psu4
  psu5 := smallShape_psu5
  psp2 := smallShape_psp2
  pOmegaOdd3 := by
    intro hp2 hq X _ _ Φ hS hne htop hL
    obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
    rw [muKind_pOmegaOdd_three]
    refine shapeS4_pOmegaOdd3 M hS.hyp hp2 hq hne ?_
    cases hπ : piSign p f
    · exact hr.pOmegaOdd3 hp2 hq hπ X Φ hS hne htop hL
    · exact split_pOmegaOdd3_plus M hS.hyp hp2 hq hne (piSign_true_iff.mp hπ)
  pOmegaPlus4 := hr.pOmegaPlus4
  pOmegaMinus4 := by
    intro hp2 hq X _ _ Φ hS hne htop hL
    obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
    rw [muKind_pOmegaMinus_four]
    refine shapeS4_pOmegaMinus4 M hS.hyp hp2 hq hne ?_
    cases hπ : piSign p f
    · exact hr.pOmegaMinus4 hp2 hq hπ X Φ hS hne htop hL
    · exact split_pOmegaMinus4_plus M hS.hyp hp2 hq hne (piSign_true_iff.mp hπ)
  g2 := by
    intro hp2 hq X _ _ Φ hS hne htop hL
    obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
    rw [muKind_g2]
    exact ⟨dEdgeless_of_g2d4 M hS.hyp hS.trans hp2 hq (Or.inl rfl),
      hr.g2 hp2 hq X Φ hS hne htop hL⟩
  trialityD4 := by
    intro hp2 hq X _ _ Φ hS hne htop hL
    obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
    rw [muKind_trialityD4]
    exact ⟨dEdgeless_of_g2d4 M hS.hyp hS.trans hp2 hq (Or.inr rfl),
      hr.trialityD4 hp2 hq X Φ hS hne htop hL⟩

end MuTab

variable {p f : ℕ} [Fact p.Prime]

theorem ih8MuTableSect_of_residual (hr : MuTab.MuResidual p f) : Ih8MuTableSect p f :=
  ih8MuTableSect_of_shapes (MuTab.muSmallShapes_of_residual hr)

theorem ih8MuTable_of_residual (hr : MuTab.MuResidual p f) : Ih8MuTable p f :=
  ih8MuTable_of_shapes (MuTab.muSmallShapes_of_residual hr)

end CFSG.ClassicalInvolution.Asc77
