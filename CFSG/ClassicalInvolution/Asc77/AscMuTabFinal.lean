module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabRows
public import CFSG.ClassicalInvolution.Asc77.AscMuTabTriple
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8Free

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic

namespace MuTab

theorem muKind_cases (π : Bool) (t : StatedLieTag) (k : ℕ) :
    (t = .PSL ∧ k = 3) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSL ∧ k = 5) ∨ (t = .PSU ∧ k = 3) ∨
      (t = .PSU ∧ k = 4) ∨ (t = .PSU ∧ k = 5) ∨ (t = .PSp ∧ k = 2) ∨ (t = .POmegaOdd ∧ k = 3) ∨
      (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4) ∨ (t = .G2 ∧ k = 0) ∨
      (t = .trialityD4 ∧ k = 0) ∨ muKind π t k = .large := by
  by_cases h1 : t = .PSL ∧ k = 3
  · exact Or.inl h1
  by_cases h2 : t = .PSL ∧ k = 4
  · exact Or.inr (Or.inl h2)
  by_cases h3 : t = .PSL ∧ k = 5
  · exact Or.inr (Or.inr (Or.inl h3))
  by_cases h4 : t = .PSU ∧ k = 3
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  by_cases h5 : t = .PSU ∧ k = 4
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  by_cases h6 : t = .PSU ∧ k = 5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
  by_cases h7 : t = .PSp ∧ k = 2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
  by_cases h8 : t = .POmegaOdd ∧ k = 3
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8)))))))
  by_cases h9 : t = .POmegaPlus ∧ k = 4
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9))))))))
  by_cases h10 : t = .POmegaMinus ∧ k = 4
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h10)))))))))
  by_cases h11 : t = .G2 ∧ k = 0
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h11))))))))))
  by_cases h12 : t = .trialityD4 ∧ k = 0
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl h12)))))))))))
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr ?_)))))))))))
  simp only [muKind, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ↓reduceIte]

section Shapes

variable (p f : ℕ) [Fact p.Prime]

@[expose] def SmallShape (t : StatedLieTag) (k : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)),
    TransSection p f Φ → Φ.Nonempty → (⊤ : Subgroup X) ∉ Φ → HasLieType p f Φ t k →
      KindShape Φ (muKind (piSign p f) t k)

structure MuSmallShapes : Prop where
  psl3 : SmallShape p f .PSL 3
  psl4 : SmallShape p f .PSL 4
  psl5 : SmallShape p f .PSL 5
  psu3 : SmallShape p f .PSU 3
  psu4 : SmallShape p f .PSU 4
  psu5 : SmallShape p f .PSU 5
  psp2 : SmallShape p f .PSp 2
  pOmegaOdd3 : SmallShape p f .POmegaOdd 3
  pOmegaPlus4 : SmallShape p f .POmegaPlus 4
  pOmegaMinus4 : SmallShape p f .POmegaMinus 4
  g2 : SmallShape p f .G2 0
  trialityD4 : SmallShape p f .trialityD4 0

end Shapes

variable {p f : ℕ} [Fact p.Prime]

theorem kindShape_of_shapes (hsh : MuSmallShapes p f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type}
    [Group X] [Finite X] {Φ : Set (Subgroup X)} (hS : TransSection p f Φ) (hne : Φ.Nonempty)
    (htop : (⊤ : Subgroup X) ∉ Φ) {t : StatedLieTag} {k : ℕ} (hL : HasLieType p f Φ t k) :
    KindShape Φ (muKind (piSign p f) t k) := by
  rcases muKind_cases (piSign p f) t k with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | hlarge
  · exact hsh.psl3 hp2 hq X Φ hS hne htop hL
  · exact hsh.psl4 hp2 hq X Φ hS hne htop hL
  · exact hsh.psl5 hp2 hq X Φ hS hne htop hL
  · exact hsh.psu3 hp2 hq X Φ hS hne htop hL
  · exact hsh.psu4 hp2 hq X Φ hS hne htop hL
  · exact hsh.psu5 hp2 hq X Φ hS hne htop hL
  · exact hsh.psp2 hp2 hq X Φ hS hne htop hL
  · exact hsh.pOmegaOdd3 hp2 hq X Φ hS hne htop hL
  · exact hsh.pOmegaPlus4 hp2 hq X Φ hS hne htop hL
  · exact hsh.pOmegaMinus4 hp2 hq X Φ hS hne htop hL
  · exact hsh.g2 hp2 hq X Φ hS hne htop hL
  · exact hsh.trialityD4 hp2 hq X Φ hS hne htop hL
  · rw [hlarge]
    obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
    exact shapeTriple_of_large M hp2 hq hne htop hlarge

theorem muValues_of_shapes (hsh : MuSmallShapes p f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type}
    [Group X] [Finite X] {Φ : Set (Subgroup X)} (hS : TransSection p f Φ) (hne : Φ.Nonempty)
    (htop : (⊤ : Subgroup X) ∉ Φ) {W : Subgroup X} (hW : W ∈ WSet Φ) :
    MuValues p f (piSign p f) Φ W := fun _ _ hL =>
  muVal_of_shape ⟨hp2, hq, hS.hyp, hS.aEmpty⟩ hW hne _
    (kindShape_of_shapes hsh hp2 hq hS hne htop hL)

end MuTab

variable {p f : ℕ} [Fact p.Prime]

theorem muTableSectBelow_of_shapes (hsh : MuTab.MuSmallShapes p f) {n : ℕ} (hn : CITBelowU p f n) :
    MuTableSectBelow p f n := by
  intro hp2 hq X _ _ hlt Φ hS hne htop W hW
  obtain ⟨t, k, e, M, hL⟩ := hS.exists_datum hn hlt hne
  exact MuTab.muRows_of_values ⟨t, k, hL⟩ (MuTab.muValues_of_shapes hsh hp2 hq hS hne htop hW)
    (fun hE => thm6SectBelow_of (ih8SmallEdge p) hn hp2 hq X hlt Φ hS hne htop hE)
    (fun hNE hNC => thm8SectBelow_of G2D4Models.ih8G2D4_unconditional hn hp2 hq X hlt Φ hS hne
      hNE hNC)

theorem ih8MuTableSect_of_shapes (hsh : MuTab.MuSmallShapes p f) : Ih8MuTableSect p f :=
  fun _ hn => muTableSectBelow_of_shapes hsh hn

theorem ih8MuTable_of_shapes (hsh : MuTab.MuSmallShapes p f) : Ih8MuTable p f :=
  ih8MuTable_of_sect (ih8MuTableSect_of_shapes hsh)

end CFSG.ClassicalInvolution.Asc77
