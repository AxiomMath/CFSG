module

public import CFSG.ClassicalInvolution.Asc77.AscC25J18

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups commutatorElement

section Classify

variable {E : Type} [Group E] [Finite E] {Φ : Set (Subgroup E)} {ι : Type}


theorem classify_sect {n : ℕ} (h4 : Thm4BelowU 3 1 n) (hlt : Nat.card E < n)
    (hΦ : HypOmegaModU (.sl2 3 1) Φ) (hO : classicalInvolutionOddCore E = ⊥)
    (hA : ∀ L ∈ Φ, AEmpty Φ L) (D : LieSystemDataU 3 1 ι E Φ)
    {A A' : Subgroup E} {z a₀ b₀ : E} (T : TwinSect0 Φ A A' z a₀ b₀) :
    (∀ L ∈ Φ, L = A ∨ L = A') ∨
      ∃ (D' : LieSystemDataU 3 1 (Fin 1) E Φ) (t : StatedLieTag) (k : ℕ),
        CompIs 3 1 (D'.kind 0) t k ∧
        ((t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨
          (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)) := by
  rcases exists_single_or_all D hΦ T with hall | ⟨i₀, hi⟩
  · exact Or.inl hall
  · rcases classify3 h4 hlt hΦ hO hA D hi T with hall | ⟨t, k, hCI, htags⟩
    · exact Or.inl hall
    · right
      have hgen : ⨆ _ : Fin 1, (D.hom i₀).range = ⊤ := by
        have h1 : (⨆ j, (D.hom j).range) = (D.hom i₀).range :=
          le_antisymm (iSup_le fun j => by rw [hi j]) (le_iSup (fun j => (D.hom j).range) i₀)
        rw [iSup_const, ← h1, D.generate]
      let D' : LieSystemDataU 3 1 (Fin 1) E Φ :=
        { kind := fun _ => D.kind i₀
          valid := fun _ => D.valid i₀
          hom := fun _ => D.hom i₀
          ker_le_center := fun _ => D.ker_le_center i₀
          commute := fun i j hij => absurd (Subsingleton.elim i j) hij
          generate := hgen
          fundamental := fun L hL => by
            obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
            obtain rfl := hi j
            exact ⟨0, R, hR, hLR⟩
          meets := fun _ => D.meets i₀
          card_eq := D.card_eq }
      exact ⟨D', t, k, hCI, htags⟩

end Classify

end CFSG.ClassicalInvolution.Asc77.C25J
