module

public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicEsix
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicTwE6
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicDFour
public import CFSG.RankThree.PartOne.S11d.OutStructure
public import CFSG.RankThree.PartOne.S11d.OddRank
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbedding.OuterSylow

open CFSG.Open (IsElemAbelian IsCatalogGroup)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor lieSylowExponent LieOrderFormulasInput)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo)
open CFSG.Blueprint (LieModel classicalTags chevalleyExceptionalTags reeTitsTags)
open CFSG.LocalAnalysis.RankThreeTheoremC (exists_nine_of_psl exists_nine_of_psu exists_nine_of_E6
  exists_nine_of_twistedE6 exists_nine_of_POmegaPlus_four)

section CertFree

theorem mem_inner_of_not_dvd_card_outer {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (Outer K)) {α : MulAut K} (hα : α ^ p = 1) : α ∈ inner K := by
  have hβ : (QuotientGroup.mk α : Outer K) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hα]
    rfl
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hβ) with h1 | h1
  · exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h1)
  · exact absurd (h1 ▸ orderOf_dvd_natCard (QuotientGroup.mk α : Outer K)) h

theorem statedClassicalModel_psl_quotient {K : Type} [Group K] (hZ : Subgroup.center K = ⊥)
    {n p f : ℕ} (h : StatedClassicalModel K .PSL n p f) :
    StatedClassicalModel (K ⧸ Subgroup.center K) .PSL n p f := by
  obtain ⟨hadm, F, i1, i2, hF, ⟨e⟩⟩ := h
  exact ⟨hadm, F, i1, i2, hF,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩⟩

theorem statedClassicalModel_psu_quotient {K : Type} [Group K] (hZ : Subgroup.center K = ⊥)
    {n p f : ℕ} (h : StatedClassicalModel K .PSU n p f) :
    StatedClassicalModel (K ⧸ Subgroup.center K) .PSU n p f := by
  obtain ⟨hadm, F, i1, i2, hF, ⟨e⟩⟩ := h
  exact ⟨hadm, F, i1, i2, hF,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩⟩

theorem localRankLeTwo_of_card_le_prime {K : Type} [Group K] {p : ℕ} (hp : p.Prime)
    (h : ∀ A : Subgroup K, IsElemAbelian p A → Nat.card A ≤ p) : LocalRankLeTwo p K := by
  intro R hR hcard _ _ _ _
  have h1 := h R ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p R).1 hR)
  rw [hcard] at h1
  have h2 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at h2
  omega

theorem pRank_le_one_of_card_le_prime {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h : ∀ A : Subgroup K, IsElemAbelian p A → Nat.card A ≤ p) : CFSG.pRank p K ≤ 1 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_le hp.one_lt fun A _ hA' => by
    rw [pow_one]
    exact h A hA'

theorem false_of_dvd_gcd_psl {K : Type} [Group K] [Finite K] {n ℓ f p : ℕ}
    (hcl : StatedClassicalModel K .PSL n ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : Subgroup.center K = ⊥) (hA : ∀ A : Subgroup K, IsElemAbelian p A → Nat.card A ≤ p)
    (hd : p ∣ Nat.gcd n (ℓ ^ f - 1)) : False := by
  have hpn := hd.trans (Nat.gcd_dvd_left _ _)
  have hpq := hd.trans (Nat.gcd_dvd_right _ _)
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨A, hAel, hAc⟩ := exists_nine_of_psl hcl hpn hpq
    have := hA A hAel
    rw [hAc] at this
    omega
  · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact CFSG.RankThree.PartOne.OutStructure.not_dvd_gcd_psl_of_pRank hp hp5
        (pRank_le_one_of_card_le_prime hp hA) (statedClassicalModel_psl_quotient hZ hcl) hd
    · exact CFSG.RankThree.PartOne.OddRank.not_localRankLeTwo_psl_odd hp (by omega) hℓ2 hcl hpn
        hpq (localRankLeTwo_of_card_le_prime hp hA)

theorem false_of_dvd_gcd_psu {K : Type} [Group K] [Finite K] {n ℓ f p : ℕ}
    (hcl : StatedClassicalModel K .PSU n ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : Subgroup.center K = ⊥) (hA : ∀ A : Subgroup K, IsElemAbelian p A → Nat.card A ≤ p)
    (hd : p ∣ Nat.gcd n (ℓ ^ f + 1)) : False := by
  have hpn := hd.trans (Nat.gcd_dvd_left _ _)
  have hpq := hd.trans (Nat.gcd_dvd_right _ _)
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨A, hAel, hAc⟩ := exists_nine_of_psu hcl hpn hpq
    have := hA A hAel
    rw [hAc] at this
    omega
  · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact CFSG.RankThree.PartOne.OutStructure.not_dvd_gcd_psu_of_pRank hp hp5
        (pRank_le_one_of_card_le_prime hp hA) (statedClassicalModel_psu_quotient hZ hcl) hd
    · exact CFSG.RankThree.PartOne.OddRank.not_localRankLeTwo_psu_odd hp (by omega) hℓ2 hcl hpn
        hpq (localRankLeTwo_of_card_le_prime hp hA)

end CertFree

section CertA

theorem not_dvd_divisor_of_cyclic {K : Type} [Group K] [Finite K] {t : StatedLieTag}
    {n ℓ f p : ℕ} (hadm : StatedLieAdmissible t n ℓ f) (hmodel : LieModel K t n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : Subgroup.center K = ⊥)
    (hA : ∀ A : Subgroup K, IsElemAbelian p A → Nat.card A ≤ p) :
    ¬ p ∣ lieOrderDivisor t n (ℓ ^ f) ∧ ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3) := by
  have hp1 : ¬ p ∣ 1 := hp.not_dvd_one
  have h2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have h4 : ¬ p ∣ 4 := fun h => h2 (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h))
  have hnine : p = 3 → ∀ A : Subgroup K, IsElemAbelian 3 A → Nat.card A = 3 ^ 2 → False := by
    rintro rfl A hA' hc
    have := hA A hA'
    rw [hc] at this
    omega
  rcases hmodel with ⟨ht, hcl⟩ | ⟨hn0, ht, hch⟩ | ⟨hn0, ht, hree⟩ | ⟨hn0, ht, hsz⟩
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨fun hd => ?_, by simp⟩
      exact false_of_dvd_gcd_psl hcl hp hp2 hZ hA hd
    · refine ⟨fun hd => ?_, by simp⟩
      exact false_of_dvd_gcd_psu hcl hp hp2 hZ hA hd
    · exact ⟨fun hd => h2 (hd.trans (Nat.gcd_dvd_left _ _)), by simp⟩
    · exact ⟨fun hd => h2 hd, by simp⟩
    · refine ⟨fun hd => h4 (hd.trans (Nat.gcd_dvd_left _ _)), ?_⟩
      rintro ⟨-, rfl, rfl⟩
      obtain ⟨A, hAel, hAc⟩ := exists_nine_of_POmegaPlus_four hcl
      exact hnine rfl A hAel hAc
    · exact ⟨fun hd => h4 (hd.trans (Nat.gcd_dvd_left _ _)), by simp⟩
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hp1, by simp⟩
    · exact ⟨hp1, by simp⟩
    · refine ⟨fun hd => ?_, by simp⟩
      have h3 : p ∣ 3 := hd.trans (Nat.gcd_dvd_left _ _)
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
      subst hp3
      obtain ⟨A, hAel, hAc⟩ := exists_nine_of_E6 hch
        (hd.trans (Nat.gcd_dvd_right _ _))
      exact hnine rfl A hAel hAc
    · exact ⟨fun hd => h2 (hd.trans (Nat.gcd_dvd_left _ _)), by simp⟩
    · exact ⟨hp1, by simp⟩
    · refine ⟨fun hd => ?_, by simp⟩
      have h3 : p ∣ 3 := hd.trans (Nat.gcd_dvd_left _ _)
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
      subst hp3
      obtain ⟨A, hAel, hAc⟩ := exists_nine_of_twistedE6 hch
      exact hnine rfl A hAel hAc
    · exact ⟨hp1, by simp⟩
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨hp1, by simp⟩
    · exact ⟨hp1, by simp⟩
    · exact ⟨hp1, by simp⟩
  · subst ht
    exact ⟨hp1, by simp⟩

end CertA

end CFSG.AGLEmbedding.OuterSylow
