module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBOdd
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBUnitaryTorus
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenLinear
import CFSG.RankThree.PartOne.N143.HighEvenA
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import CFSG.LocalAnalysis.SectionRank.QTK.EvenBlocks3
import CFSG.LocalAnalysis.SectionRank.QTK.EvenMinus8
import CFSG.RankThree.PartOne.KF.ClsSpWit
import CFSG.RankThree.PartTwo.KFacts.KS21LocalRankOmega

public section

namespace CFSG.SectionRank.QTK.CoverB

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (localRank)

theorem exists_cover_hom {G : Type} [Group G] {Y : Subgroup G} {T : Type} [Group T]
    (e : ↥Y ⧸ center ↥Y ≃* T) :
    ∃ φ : ↥Y →* T, Function.Surjective φ ∧ φ.ker = center ↥Y :=
  ⟨e.toMonoidHom.comp (QuotientGroup.mk' (center ↥Y)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), by
      ext x
      rw [MonoidHom.mem_ker]
      change e (QuotientGroup.mk' (center ↥Y) x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]⟩

variable {G : Type} [Group G] [Finite G]

theorem false_of_three_le_localRank_cover (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h : 3 ≤ localRank r ↥Y) : False := by
  have h1 := localRank_le_evenRank (G := ↥Y) hr hr2
  have h2 : CFSG.Open.evenRank ↥Y ≤ CFSG.Open.evenRank G :=
    CFSG.RankThree.PartTwo.evenRank_subgroup_le Y
  omega

theorem qtkSimpleList_of_cover_psl_even (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {n f : ℕ} (hm : StatedClassicalModel (↥Y ⧸ center ↥Y) .PSL n 2 f)
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (center ↥Y) → TablePrime .PSL n 2 f r) :
    QTKSimpleList (↥Y ⧸ center ↥Y) := by
  obtain ⟨⟨-, hf, hn, h22, -⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  rcases (show n = 2 ∨ n = 3 ∨ (n = 4 ∨ n = 5) ∨ 6 ≤ n by omega) with rfl | rfl | h45 | hn6
  · have hf2 : 2 ≤ f := by
      by_contra h
      exact h22 (by rw [show f = 1 by omega]; rfl)
    exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inl ⟨hf2, hm⟩⟩)))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, hm⟩)⟩)))
  · set e' : (↥Y ⧸ center ↥Y) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
      e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm
    by_cases hf1 : f = 1
    · subst hf1
      exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨n, h45, hm⟩))))
    · obtain ⟨r, hr, hr2, hr5, hrd⟩ :=
        CFSG.RankThree.PartTwo.Census.exists_prime_ne_five_dvd_two_pow_sub_one (f := f) (by omega)
      have hrZ : ¬ r ∣ Nat.card (center ↥Y) := fun h => by
        rcases hZ r hr hr2 h with ⟨-, h1, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ |
            ⟨-, ⟨-, -, h1, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩⟩
        · rcases h45 with rfl | rfl
          · exact not_dvd_four_of_odd_prime hr hr2 h1
          · exact hr5 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp h1)
        · cases h0
        · cases h0
        · cases h0
        · omega
        all_goals cases h0
      refine (false_of_three_le_localRank he e' hr hr2 hrZ
        (CFSG.RankThree.PartTwo.Census.le_localRank_PSL_torus (m := 3) hr
          (by rw [Nat.card_units, hK]; exact hrd) (by omega) (by omega) ?_)).elim
      rcases h45 with rfl | rfl
      · exact Or.inr fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
          (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 2 by simpa using h)))
      · exact Or.inl (by norm_num)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 + 1 := ⟨n - 3, by omega⟩
    set e' : (↥Y ⧸ center ↥Y) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (m + 2 + 1)) K :=
      e.trans (projectiveSpecialLinearGroupEquivStatedProj (m + 2 + 1) K).symm
    by_cases h3 : 3 ∣ Nat.card (center ↥Y)
    · have hq3 : 3 ∣ 2 ^ f - 1 := by
        rcases hZ 3 Nat.prime_three (by norm_num) h3 with ⟨-, -, h1⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ |
            ⟨h0, -⟩ | ⟨-, ⟨-, -, h1, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩⟩
        · exact h1
        · cases h0
        · cases h0
        · cases h0
        · omega
        all_goals cases h0
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
        (by rw [Nat.card_units, hK]; exact hq3)
      obtain ⟨φ, hφ, hker⟩ := exists_cover_hom e'
      have h4 := CFSG.RankThree.PartOne.N143.succ_le_localRank_psl_even hζ
        (by rw [← hζ]; exact pow_orderOf_eq_one ζ) φ hφ hker.le (by rw [hker]; exact h3)
      exact (false_of_three_le_localRank_cover he Nat.prime_three (by norm_num)
        (le_trans (by omega) h4)).elim
    · exact (false_of_three_le_localRank he e' Nat.prime_three (by norm_num) h3
        (three_le_localRank_PSL_of_six_le hn6)).elim

theorem qtkSimpleList_of_cover_psu_even (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {n f : ℕ} (hm : StatedClassicalModel (↥Y ⧸ center ↥Y) .PSU n 2 f)
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (center ↥Y) → TablePrime .PSU n 2 f r) :
    QTKSimpleList (↥Y ⧸ center ↥Y) := by
  obtain ⟨⟨-, hf, hn, h32⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have hU : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : CharP K 2 := hU.charP
  have : Finite K := hU.finite
  rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | rfl | hn6
  · have hf2 : 2 ≤ f := by
      by_contra h
      exact h32 (by rw [show f = 1 by omega]; rfl)
    exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inl ⟨hf2, hm⟩))⟩)))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hf, hm⟩))))⟩)))
  · by_cases hf2 : f = 2
    · subst hf2
      exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hm))))
    · obtain ⟨r, hr, hr2, hr5, hrd⟩ := exists_prime_ne_five_dvd_two_pow_add_one hf hf2
      have hrZ : ¬ r ∣ Nat.card (center ↥Y) := fun h => by
        rcases hZ r hr hr2 h with ⟨h0, -⟩ | ⟨-, h1, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ |
            ⟨-, ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, h1, -⟩⟩
        · cases h0
        · exact hr5 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp h1)
        · cases h0
        · cases h0
        · cases h0
        · cases h0
        · cases h0
        · omega
      exact (false_of_three_le_localRank he e hr hr2 hrZ
        (CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus hU (k := 2) hr hrd
          (by norm_num) (Or.inr fun h => hr5 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).1
            h)))).elim
  · obtain ⟨r, hr, hr2, hrd⟩ :=
      CFSG.RankThree.PartTwo.Census.exists_odd_prime_dvd_two_pow_add_one hf
    by_cases hrZ : r ∣ Nat.card (center ↥Y)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      set e' : (↥Y ⧸ center ↥Y) ≃* unitaryPSU hU (m + 3) :=
        e.trans (unitaryPSUEquiv hU (by omega)).symm
      obtain ⟨φ, hφ, hker⟩ := exists_cover_hom e'
      have h4 := succ_le_localRank_unitary_even_prime hU rfl hr hr2 hrd (Y := ↥Y) (r := m)
        rfl φ hφ hker.le (by rw [hker]; exact hrZ)
      exact (false_of_three_le_localRank_cover he hr hr2 (le_trans (by omega) h4)).elim
    · exact (false_of_three_le_localRank he e hr hr2 hrZ
        (CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus hU (k := 2) hr hrd
          (by omega) (Or.inl (by omega)))).elim

theorem not_tablePrime_of_sp_or_omega {t : StatedLieTag} {n ℓ f r : ℕ}
    (ht : t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus) : ¬ TablePrime t n ℓ f r := by
  rintro (⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ |
      ⟨-, ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩⟩) <;>
    rcases ht with rfl | rfl | rfl <;> cases h0

theorem qtkSimpleList_of_cover_psp_even (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {n f : ℕ} (hm : StatedClassicalModel (↥Y ⧸ center ↥Y) .PSp n 2 f)
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (center ↥Y) → TablePrime .PSp n 2 f r) :
    QTKSimpleList (↥Y ⧸ center ↥Y) := by
  have hnd : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (center ↥Y) := fun r hr hr2 h =>
    not_tablePrime_of_sp_or_omega (Or.inl rfl) (hZ r hr hr2 h)
  obtain ⟨⟨-, hf, hn, h22⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | hn4
  · have hf2 : 2 ≤ f := by
      by_contra h
      exact h22 (by rw [show f = 1 by omega]; rfl)
    exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inl ⟨hf2, hm⟩)))⟩)))
  · by_cases hf1 : f = 1
    · subst hf1
      exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr hm))))
    · obtain ⟨r, hr, hr2, -, hrd⟩ :=
        CFSG.RankThree.PartTwo.Census.exists_prime_ne_five_dvd_two_pow_sub_one (f := f) (by omega)
      exact (false_of_three_le_localRank he e hr hr2 (hnd r hr hr2)
        (CFSG.RankThree.PartOne.KFU.le_localRank_statedSp_torus hr hr2
          (by rw [Nat.card_units, hK]; exact hrd) (by norm_num))).elim
  · refine (false_of_three_le_localRank he e Nat.prime_three (by norm_num)
      (hnd 3 Nat.prime_three (by norm_num)) ?_).elim
    rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
      (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _
        (CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedSp_eq_bot (K := K) (n := n)
          (by omega))) Nat.prime_three]
    exact (three_le_localRank_statedProj_statedOmegaPlus K hn4).trans
      (CFSG.RankThree.PartOne.KFU.localRank_statedProj_statedOmega_quadPlus_le (by omega)
        Nat.prime_three)

theorem qtkSimpleList_of_cover_even_classical (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} (hm : StatedClassicalModel (↥Y ⧸ center ↥Y) t n 2 f)
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (center ↥Y) → TablePrime t n 2 f r) :
    QTKSimpleList (↥Y ⧸ center ↥Y) := by
  cases t with
  | PSL => exact qtkSimpleList_of_cover_psl_even he hm hZ
  | PSU => exact qtkSimpleList_of_cover_psu_even he hm hZ
  | PSp => exact qtkSimpleList_of_cover_psp_even he hm hZ
  | POmegaOdd => exact (hm.1.2.2.2 rfl).elim
  | POmegaPlus =>
    have hnd : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (center ↥Y) := fun r hr hr2 h =>
      not_tablePrime_of_sp_or_omega (Or.inr (Or.inl rfl)) (hZ r hr hr2 h)
    obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hm
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
    exact (false_of_three_le_localRank he e Nat.prime_three (by norm_num)
      (hnd 3 Nat.prime_three (by norm_num))
      (three_le_localRank_statedProj_statedOmegaPlus K hn)).elim
  | POmegaMinus =>
    have hnd : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (center ↥Y) := fun r hr hr2 h =>
      not_tablePrime_of_sp_or_omega (Or.inr (Or.inr rfl)) (hZ r hr hr2 h)
    obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hm
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
    rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
    · by_cases hf1 : f = 1
      · subst hf1
        exact (false_of_three_le_localRank he e Nat.prime_three (by norm_num)
          (hnd 3 Nat.prime_three (by norm_num))
          (three_le_localRank_statedProj_statedOmegaMinus_four_two (by rw [hK, pow_one])
            hirr)).elim
      · obtain ⟨r, hr, hr2, -, hrd⟩ :=
          CFSG.RankThree.PartTwo.Census.exists_prime_ne_five_dvd_two_pow_sub_one (f := f)
            (by omega)
        exact (false_of_three_le_localRank he e hr hr2 (hnd r hr hr2)
          (CFSG.RankThree.PartTwo.KFacts.KS21LocalRank.le_localRank_statedOmegaMinus_torus hr
            hr2 (by rw [Nat.card_units, hK]; exact hrd) b c)).elim
    · exact (false_of_three_le_localRank he e Nat.prime_three (by norm_num)
        (hnd 3 Nat.prime_three (by norm_num))
        (three_le_localRank_statedProj_statedOmegaMinus K hn5 b c)).elim
  | _ => exact hm.2.elim

end CFSG.SectionRank.QTK.CoverB
