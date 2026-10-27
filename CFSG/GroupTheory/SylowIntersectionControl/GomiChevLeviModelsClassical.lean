module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageTop
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviBorelTop
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Blueprint Subgroup

variable {X : Type} [Group X] [Finite X] {n f : ℕ}

theorem gomiLeviPackageTop_of_psl (h : StatedClassicalModel X .PSL n 2 f)
    (hSL : 4 ≤ n → GomiLeviFactorsSL) : GomiLeviPackageTop X := by
  obtain ⟨hadm, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have hn2 : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hfac : GomiLeviFactors (CFSG.LieType.Universal.SpecialLinear.rootDatum m F) := by
    by_cases h4 : 4 ≤ m + 1
    · exact hSL h4 m F
    · exact gomiLeviFactors_of_rank_le_two (by show m ≤ 2; omega)
  exact gomiLeviPackageTop_of_borelQuotient
    (CFSG.AGLEmbedding.ParabHub.borelQuotient_sl (m := m)
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans
        e.symm))
    hfac

theorem gomiLeviPackageTop_of_psp (h : StatedClassicalModel X .PSp n 2 f)
    (hSp : 3 ≤ n → GomiLeviFactorsSp) : GomiLeviPackageTop X := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hfac : GomiLeviFactors (CFSG.LieType.Universal.Symplectic.rootDatum n F) := by
    by_cases h3 : 3 ≤ n
    · exact hSp h3 n F
    · exact gomiLeviFactors_of_rank_le_two (by show n ≤ 2; omega)
  exact gomiLeviPackageTop_of_borelQuotient
    (CFSG.AGLEmbedding.ParabHub.borelQuotient_sp e) hfac

theorem gomiLeviPackageTop_of_psu (h : StatedClassicalModel X .PSU n 2 f)
    (hSU : 6 ≤ n → GomiLeviFactorsSU) : GomiLeviPackageTop X := by
  obtain ⟨hadm, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have hn2 : 2 ≤ n := by have := hadm.2.2.1; omega
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hcard
  have hfac : GomiLeviFactors
      (CFSG.LieType.Universal.Unitary.rootDatum (p := 2) hcard n) := by
    by_cases h6 : 6 ≤ n
    · exact hSU h6 F f hcard n
    · exact gomiLeviFactors_of_rank_le_two (by show n / 2 ≤ 2; omega)
  exact gomiLeviPackageTop_of_borelQuotient
    (CFSG.AGLEmbedding.ParabHub.borelQuotient_su hcard hn2 ζ hζ e) hfac

open CFSG.LieType.Universal.Spin in
theorem gomiLeviPackageTop_of_pomegaPlus (h : StatedClassicalModel X .POmegaPlus n 2 f)
    (hSpinPlus : GomiLeviFactorsSpinPlus) : GomiLeviPackageTop X := by
  obtain ⟨hadm, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have hn3 : 3 ≤ n := by have := hadm.2.2; omega
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact gomiLeviPackageTop_of_borelQuotient
    (CFSG.AGLEmbedding.ParabHub.borelQuotient_spinPlus hn3 e) (hSpinPlus n F hn3)

open CFSG.LieType.Universal.Spin in
theorem gomiLeviPackageTop_of_pomegaMinus (h : StatedClassicalModel X .POmegaMinus n 2 f)
    (hSpinMinus : GomiLeviFactorsSpinMinus) : GomiLeviPackageTop X := by
  obtain ⟨hadm, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have hn4 : 4 ≤ n := by have := hadm.2.2; omega
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (coe_ker_spinMatrix_quadMinus hirr)
  exact gomiLeviPackageTop_of_borelQuotient
    (CFSG.AGLEmbedding.ParabHub.borelQuotient_spinMinus hirr hn4 e)
    (hSpinMinus n F b c hirr hn4)

theorem gomiChevLeviPackageModel_classical (hSL : GomiLeviFactorsSL) (hSp : GomiLeviFactorsSp)
    (hSU : GomiLeviFactorsSU) (hSpinPlus : GomiLeviFactorsSpinPlus)
    (hSpinMinus : GomiLeviFactorsSpinMinus) {t : StatedLieTag} (ht : t ∈ classicalTags)
    (n : ℕ) : GomiChevLeviPackageModel t n := by
  simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact gomiChevLeviPackageModel_of_gomiLeviPackageTop fun X _ _ f hm =>
      gomiLeviPackageTop_of_psl (hm.statedClassicalModel (by decide)) fun _ => hSL
  · exact gomiChevLeviPackageModel_of_gomiLeviPackageTop fun X _ _ f hm =>
      gomiLeviPackageTop_of_psu (hm.statedClassicalModel (by decide)) fun _ => hSU
  · exact gomiChevLeviPackageModel_of_gomiLeviPackageTop fun X _ _ f hm =>
      gomiLeviPackageTop_of_psp (hm.statedClassicalModel (by decide)) fun _ => hSp
  · exact gomiChevLeviPackageModel_pOmegaOdd n
  · exact gomiChevLeviPackageModel_of_gomiLeviPackageTop fun X _ _ f hm =>
      gomiLeviPackageTop_of_pomegaPlus (hm.statedClassicalModel (by decide)) hSpinPlus
  · exact gomiChevLeviPackageModel_of_gomiLeviPackageTop fun X _ _ f hm =>
      gomiLeviPackageTop_of_pomegaMinus (hm.statedClassicalModel (by decide)) hSpinMinus

end CFSG.GroupTheory
