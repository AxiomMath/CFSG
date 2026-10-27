module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ClassicalLift
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ClassicalMinus
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ArithLin
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ArithRest
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Subgroup Matrix CFSG.Open CFSG.EvenSmallLie.CatalogOrders


theorem false_of_statedProj_small {S : Type} [Group S] {F : Type} [Field F] [Finite F] {ι : Type}
    [Fintype ι] [DecidableEq ι] (H : Subgroup (GL ι F)) (hF3 : ringChar F ≠ 3)
    (hcard : Fintype.card ι < 8) (e : S ≃* StatedProj H) (K : Subgroup S) (hK : HSType ↥K) :
    False := by
  obtain ⟨Y, -, hY⟩ := exists_hsType_of_statedProj H e K hK
  exact no_hsType_card_lt_eight hF3 hcard Y hY

theorem false_of_statedOmegaMinus_four {S : Type} [Group S] {F : Type} [Field F] [Finite F]
    (b c : F) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (e : S ≃* StatedProj (StatedOmega (StatedQuadMinus 4 F b c))) (K : Subgroup S)
    (hK : HSType ↥K) : False := by
  obtain ⟨Y, hYH, hY⟩ :=
    exists_hsType_of_statedProj (StatedOmega (StatedQuadMinus 4 F b c)) e K hK
  have hcard8 : Fintype.card (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) = 8 := by simp
  by_cases h5 : ringChar F = 5
  · have hodd : (2 : F) ≠ 0 := by
      intro h2
      have h := (ringChar.spec F 2).mp (by exact_mod_cast h2)
      rw [h5] at h
      norm_num at h
    have hBm := minusGram_isUnit_det 3 F hodd b c hirr
    have h10 := hsType_ten_le_card (by omega) Y hY (minusGram 3 F b c) hBm
      (fun s hs => transpose_mul_gram_mul_of_isometry (StatedQuadMinus 4 F b c)
        (minusGram 3 F b c) (fun v w => minusQuad_polar 3 F b c v w) _
        (statedOmega_isometry (StatedQuadMinus 4 F b c) (hYH hs)))
    rw [hcard8] at h10
    omega
  · have h20 := hsType_twenty_le_card h5 Y hY
    rw [hcard8] at h20
    omega

theorem no_hsType_statedClassical {S : Type} [Group S] [Finite S] {t : StatedLieTag}
    {n p f : ℕ} (hp3 : p ≠ 3) (h3 : (Nat.card S).factorization 3 ≤ 4)
    (hM : StatedClassicalModel S t n p f) (K : Subgroup S) (hK : HSType ↥K) : False := by
  have hcardS : Nat.card S = lieOrd t n (p ^ f) := card_eq_lieOrd_of_classical hM
  obtain ⟨hadm, hrest⟩ := hM
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hq3 : ¬ 3 ∣ p ^ f := by
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h)).symm
  cases t
  ·
    obtain ⟨K', _, _, hcard, ⟨e⟩⟩ := hrest
    have hF3 : ringChar K' ≠ 3 := by
      rw [CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hcard]; exact hp3
    by_cases h8 : 8 ≤ n
    · have hd : 3 ^ 5 ∣ Nat.card S := by
        rw [hcardS]; exact three_pow_five_dvd_ordA h8 hq3
      exact false_of_three_pow_five_dvd h3 hd
    · exact false_of_statedProj_small (StatedSL n K') hF3
        (by rw [Fintype.card_fin]; omega) e K hK
  ·
    obtain ⟨K', _, _, hcard, ⟨e⟩⟩ := hrest
    have hchar : ringChar K' = p :=
      CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq (f := f * 2) hp (by omega)
        (hcard.trans (pow_mul p f 2).symm)
    have hF3 : ringChar K' ≠ 3 := by rw [hchar]; exact hp3
    by_cases h8 : 8 ≤ n
    · have hd : 3 ^ 5 ∣ Nat.card S := by
        rw [hcardS]; exact three_pow_five_dvd_ordTwistedA h8 hq3
      exact false_of_three_pow_five_dvd h3 hd
    · exact false_of_statedProj_small (StatedSU n (p ^ f) K') hF3
        (by rw [Fintype.card_fin]; omega) e K hK
  ·
    obtain ⟨K', _, _, hcard, ⟨e⟩⟩ := hrest
    have hF3 : ringChar K' ≠ 3 := by
      rw [CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hcard]; exact hp3
    by_cases h4 : 4 ≤ n
    · have hd : 3 ^ 5 ∣ Nat.card S := by
        rw [hcardS]; exact three_pow_five_dvd_ordBC h4 hq3
      exact false_of_three_pow_five_dvd h3 hd
    · exact false_of_statedProj_small (StatedSp n K') hF3
        (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) e K hK
  ·
    obtain ⟨K', _, _, hcard, ⟨e⟩⟩ := hrest
    have hF3 : ringChar K' ≠ 3 := by
      rw [CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hcard]; exact hp3
    by_cases h4 : 4 ≤ n
    · have hd : 3 ^ 5 ∣ Nat.card S := by
        rw [hcardS]; exact three_pow_five_dvd_ordBC h4 hq3
      exact false_of_three_pow_five_dvd h3 hd
    · exact false_of_statedProj_small (StatedOmega (StatedQuadOdd n K')) hF3
        (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]; omega) e K hK
  ·
    have hn : 4 ≤ n := hadm.2.2
    have hd : 3 ^ 5 ∣ Nat.card S := by
      rw [hcardS]; exact three_pow_five_dvd_ordD hn hq3
    exact false_of_three_pow_five_dvd h3 hd
  ·
    obtain ⟨K', _, _, -, b, c, hirr, ⟨e⟩⟩ := hrest
    have hn : 4 ≤ n := hadm.2.2
    by_cases h5 : 5 ≤ n
    · have hd : 3 ^ 5 ∣ Nat.card S := by
        rw [hcardS]; exact three_pow_five_dvd_ordTwistedD h5 hq3
      exact false_of_three_pow_five_dvd h3 hd
    · obtain rfl : n = 4 := by omega
      exact false_of_statedOmegaMinus_four b c hirr e K hK
  all_goals exact False.elim hrest

end CFSG.ComponentClassification.CatFC.KGHS3
