module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1L3Trans
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1L3P1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.GL2Max
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Strong

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

section L3OddProof

set_option linter.unusedSectionVars false

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves

variable {F : Type} [Field F] [Finite F]

theorem f1Core_SL3_odd (hq : Nat.card F % 3 = 2) (hodd : ¬ 2 ∣ Nat.card F) :
    F1Core (SL3 F) := by
  refine f1Core_of_A0 card_A0 ?_
  intro W Y hNW hYW hAY hY hWtop S hS hSW
  have h5 : 5 ≤ Nat.card F := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hmax := gl2NonsplitMax hq h5
  have hroot := sq_add_self_add_one_ne_zero hq
  have hcube := exists_cube hq
  have h3 := three_ne_zero_of_mod hq
  obtain ⟨μ, hμ0, hμ6⟩ := exists_pow_six_ne_one hq h5
  obtain ⟨y, hy⟩ := exists_orderOf_three hAY
  have hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) →
        lev X ∈ W :=
    fun X hX => hNW (lev_mem_normalizer_A0 (mem_Nt_of_comm hX))
  rcases le_P1_or_le_P2_or_transitive hroot hcube hlev with h | h | htr
  · exact (false_of_le_P1_odd hq hodd (hYW.trans h) hY hy).elim
  · exact (false_of_le_P2_odd hq hodd (hYW.trans h) hY hy).elim
  · rcases transitive_cases hroot hcube h3 hmax hμ0 hμ6 hNW htr with h' | ⟨-, hb⟩
    · exact absurd h' hWtop
    · exact normalizer_le_of_transitive hq hodd hmax hNW htr hb
        (CFSG.ABGLocalTools.IsSylowOf.of_le hS hSW le_top)

end L3OddProof

section L3OddFamily

set_option linter.unusedSectionVars false

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3


theorem f1L3Odd_proved : F1L3Odd := by
  intro K _ _ d q hq2 hq hd ⟨e⟩
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := GaloisField q.p q.exponent
  have hF : Nat.card F = q.card := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def]
  have hqF : Nat.card F % 3 = 2 := by rw [hF]; exact hq
  have hFodd : ¬ 2 ∣ Nat.card F := by
    rw [hF, TauCeti.PrimePower.card_def]
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two q.prime_p).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)).symm
  exact f1For_of_core
    ((e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans (pslEquivSL3 hqF))
    (f1Core_SL3_odd hqF hFodd)

end L3OddFamily

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
