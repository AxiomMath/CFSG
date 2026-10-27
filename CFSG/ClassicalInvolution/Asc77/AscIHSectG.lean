module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectC
public import CFSG.ClassicalInvolution.Asc77.AscIH8Rest

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

@[expose] def MuRows {X : Type} [Group X] (Φ : Set (Subgroup X)) (W : Subgroup X) : Prop :=
  (MuIsoZ2 Φ W ↔ (if piSign p f then HasLieType p f Φ .PSU 3
      else HasLieType p f Φ .PSL 3)) ∧
  (MuIsoS3 Φ W ↔ ((if piSign p f then HasLieType p f Φ .PSL 3
      else HasLieType p f Φ .PSU 3) ∨ HasLieType p f Φ .G2 0 ∨
      HasLieType p f Φ .trialityD4 0)) ∧
  (MuIsoE4 Φ W ↔ (HasOrthType p f Φ 5 true ∨ HasOrthType p f Φ 6 (!piSign p f) ∨
      (if piSign p f then HasLieType p f Φ .PSU 5 else HasLieType p f Φ .PSL 5))) ∧
  (MuIsoS4 Φ W ↔ (HasOrthType p f Φ 6 (piSign p f) ∨ HasOrthType p f Φ 7 true ∨
      HasOrthType p f Φ 8 false)) ∧
  (HasOrthType p f Φ 8 true → MuIsoWylD4 Φ W) ∧
  (¬ Disconnected.DConnected Φ → MuIsoWylD4 Φ W → HasOrthType p f Φ 8 true)

@[expose] def MuTableSectBelow (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), TransSection p f Φ → Φ.Nonempty → (⊤ : Subgroup X) ∉ Φ →
        ∀ W ∈ WSet Φ, MuRows p f Φ W

@[expose] def Ih8MuTableSect : Prop := ∀ n : ℕ, CITBelowU p f n → MuTableSectBelow p f n

variable {p f}

theorem muTableBelow_of_sect {n : ℕ} (h : MuTableSectBelow p f n) : MuTableBelow p f n := by
  intro hp2 hq G _ _ _ hlt Ω hΩ hA hne htrans W hW
  exact h hp2 hq G hlt Ω (TransSection.of_simple hΩ hne htrans hA) hne (top_notMem_of_simple hΩ)
    W hW

theorem ih8MuTable_of_sect (h : Ih8MuTableSect p f) : Ih8MuTable p f :=
  fun n hn => muTableBelow_of_sect (h n hn)

theorem ih8Rest_of_sect (h5 : Ih8Thm5 p f) (hMu : Ih8MuTableSect p f) (h3 : Ih8Thm3 p f)
    (hG : Ih8G2D4 p f) : IH8Rest p f :=
  ih8Rest_of h5 (ih8MuTable_of_sect hMu) h3 hG

end CFSG.ClassicalInvolution.Asc77
