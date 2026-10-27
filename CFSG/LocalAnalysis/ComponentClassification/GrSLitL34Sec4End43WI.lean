module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem card_le_four_of_lt_eight {A : Subgroup G} (hA : IsElemTwo A) (h : Nat.card A < 8) :
    Nat.card A ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥A)).mp hA.isPGroup
  rw [hk] at h ⊢
  have hk2 : k ≤ 2 := by
    by_contra hk2
    push Not at hk2
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

theorem exists_eight_between : ∀ (n : ℕ) {A B : Subgroup G}, 8 - Nat.card A ≤ n → A ≤ B →
    IsElemTwo B → Nat.card A ≤ 8 → 8 ≤ Nat.card B →
    ∃ A' : Subgroup G, A ≤ A' ∧ A' ≤ B ∧ IsElemTwo A' ∧ Nat.card A' = 8 := by
  intro n
  induction n with
  | zero =>
    intro A B hn hAB hB hA8 _
    exact ⟨A, le_rfl, hAB, hB.mono hAB, by omega⟩
  | succ n ih =>
    intro A B hn hAB hB hA8 hB8
    by_cases hA : Nat.card A = 8
    · exact ⟨A, le_rfl, hAB, hB.mono hAB, hA⟩
    · have hlt : Nat.card A < 8 := lt_of_le_of_ne hA8 hA
      obtain ⟨b, hbB, hbA⟩ : ∃ b ∈ B, b ∉ A := by
        by_contra h
        push Not at h
        have := Subgroup.card_le_of_le (show B ≤ A from h)
        omega
      obtain ⟨-, hcard⟩ := isElemTwo_sup_zpowers (hB.mono hAB) (hB.2 b hbB) hbA
        (fun e he => hB.1 e (hAB he) b hbB)
      have h4 := card_le_four_of_lt_eight (hB.mono hAB) hlt
      have hpos : 0 < Nat.card A := Nat.card_pos
      obtain ⟨A', h1, h2, h3, h4'⟩ := ih (A := A ⊔ zpowers b) (B := B) (by omega)
        (sup_le hAB (zpowers_le.mpr hbB)) hB (by omega) hB8
      exact ⟨A', le_sup_left.trans h1, h2, h3, h4'⟩

end GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

end CFSG.ComponentClassification.GrSLit
