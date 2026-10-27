module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabHubSpin
public import CFSG.ClassicalInvolution.Asc77.AscMuTabD4
public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallF

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected

namespace MuTab

variable (p f : ℕ) [Fact p.Prime]

structure MuResidualG2D4 : Prop where
  g2 : p ≠ 2 → 5 ≤ p ^ f → ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)),
    TransSection p f Φ → Φ.Nonempty → (⊤ : Subgroup X) ∉ Φ → HasLieType p f Φ .G2 0 →
      ∃ K ∈ Φ, (omegaStarNbr Φ K).Nonempty
  trialityD4 : p ≠ 2 → 5 ≤ p ^ f → ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)),
    TransSection p f Φ → Φ.Nonempty → (⊤ : Subgroup X) ∉ Φ → HasLieType p f Φ .trialityD4 0 →
      ∃ K ∈ Φ, (omegaStarNbr Φ K).Nonempty

variable {p f}

theorem muSmallShapes_of_g2d4 (hD4 : Ih8D4Star p f) (hr : MuResidualG2D4 p f) :
    MuSmallShapes p f where
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
    · exact split_pOmegaOdd3_minus M hS.hyp hp2 hq hne (pow_mod_four_of_piSign_false hp2 hπ)
    · exact split_pOmegaOdd3_plus M hS.hyp hp2 hq hne (piSign_true_iff.mp hπ)
  pOmegaPlus4 := smallShape_pOmegaPlus4_of hD4
  pOmegaMinus4 := by
    intro hp2 hq X _ _ Φ hS hne htop hL
    obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
    rw [muKind_pOmegaMinus_four]
    refine shapeS4_pOmegaMinus4 M hS.hyp hp2 hq hne ?_
    cases hπ : piSign p f
    · exact split_pOmegaMinus4_minus M hS.hyp hp2 hq hne (pow_mod_four_of_piSign_false hp2 hπ)
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

theorem ih8MuTableSect_of_g2d4 (hD4 : Ih8D4Star p f) (hr : MuTab.MuResidualG2D4 p f) :
    Ih8MuTableSect p f :=
  ih8MuTableSect_of_shapes (MuTab.muSmallShapes_of_g2d4 hD4 hr)

theorem ih8MuTable_of_g2d4 (hD4 : Ih8D4Star p f) (hr : MuTab.MuResidualG2D4 p f) :
    Ih8MuTable p f :=
  ih8MuTable_of_shapes (MuTab.muSmallShapes_of_g2d4 hD4 hr)

end CFSG.ClassicalInvolution.Asc77
