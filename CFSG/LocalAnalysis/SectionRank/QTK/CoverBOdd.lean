module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBBasic
public import CFSG.LocalAnalysis.SectionRank.QTK.OddLinear
import CFSG.RankThree.PartOne.Census3.LinearWitness
import CFSG.RankThree.PartTwo.Census.OddClassical.LinearWitness
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness
import CFSG.RankThree.PartTwo.Census.OddClassical.SymplecticWitness
import CFSG.RankThree.PartOne.S11c.OrthogonalRank
public import CFSG.RankThree.CentralLift.ClassicalCenterTrivial

public section

namespace CFSG.SectionRank.QTK.CoverB

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.LieType.Universal.Spin (quadOdd quadPlus quadMinus)

@[expose] def TablePrime (t : StatedLieTag) (n ℓ f r : ℕ) : Prop :=
  (t = .PSL ∧ r ∣ n ∧ r ∣ ℓ ^ f - 1) ∨ (t = .PSU ∧ r ∣ n ∧ r ∣ ℓ ^ f + 1) ∨
    (t = .E6 ∧ r = 3 ∧ 3 ∣ ℓ ^ f - 1) ∨ (t = .twistedE6 ∧ r = 3 ∧ 3 ∣ ℓ ^ f + 1) ∨
    (r = 3 ∧ ((t = .PSL ∧ n = 2 ∧ ℓ = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ ℓ = 3 ∧ f = 1) ∨
      (t = .G2 ∧ n = 0 ∧ ℓ = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ ℓ = 3 ∧ f = 1)))

theorem not_dvd_pow_sub_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) : ¬ p ∣ p ^ f - 1 := by
  intro h
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  have h2 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2] at this
  exact hp.not_dvd_one this

theorem not_dvd_pow_add_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) : ¬ p ∣ p ^ f + 1 := by
  intro h
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  exact hp.not_dvd_one ((Nat.dvd_add_right h1).mp h)

variable {G : Type} [Group G] [Finite G]

theorem qtkSimpleList_of_cover_psl_odd (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {n p f : ℕ} (hp2 : p ≠ 2) (hm : StatedClassicalModel (↥Y ⧸ center ↥Y) .PSL n p f)
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (center ↥Y) → TablePrime .PSL n p f r) :
    QTKSimpleList (↥Y ⧸ center ↥Y) := by
  obtain ⟨⟨hp, hf, hn, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have h2 : (2 : K) ≠ 0 := CFSG.RankThree.PartOne.Census3.two_ne_zero_of_charP hp2
  set e' : (↥Y ⧸ center ↥Y) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm
  have hpZ : 3 ≤ n → ¬ p ∣ Nat.card (center ↥Y) := fun hn3 h => by
    rcases hZ p hp hp2 h with ⟨-, -, h1⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ |
        ⟨-, ⟨-, h1, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩⟩
    · exact not_dvd_pow_sub_one hp hf h1
    · cases h0
    · cases h0
    · cases h0
    · omega
    all_goals cases h0
  rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | rfl | hn5
  · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inl ⟨f, hf, hm⟩⟩)
  · by_cases hf2 : f ≤ 2
    · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inr (Or.inl ⟨f, by omega, Or.inl hm⟩)⟩)
    · exact (false_of_three_le_localRank he e' hp hp2 (hpZ le_rfl)
        (le_trans (by omega) (CFSG.RankThree.PartOne.Census3.le_localRank_PSL_three hp2 hK))).elim
  · by_cases hf1 : f = 1
    · subst hf1
      by_cases hF : ∃ a : ℕ, p = 2 ^ a + 1
      · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hF, hm⟩))))⟩)
      · obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_pred hp hp2 hF
        have hrZ : ¬ r ∣ Nat.card (center ↥Y) := fun h => by
          rcases hZ r hr hr2 h with ⟨-, h1, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ |
              ⟨-, ⟨-, h1, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩⟩
          · exact not_dvd_four_of_odd_prime hr hr2 h1
          · cases h0
          · cases h0
          · cases h0
          · omega
          all_goals cases h0
        refine (false_of_three_le_localRank he e' hr hr2 hrZ ?_).elim
        refine le_localRank_PSL_torus_odd h2 (m := 3) hr ?_ (by norm_num) (by norm_num)
          (Or.inr (not_dvd_four_of_odd_prime hr hr2))
        rw [Nat.card_units, hK, pow_one]
        exact hrd
    · exact (false_of_three_le_localRank he e' hp hp2 (hpZ (by norm_num))
        (le_trans (by omega) (CFSG.RankThree.PartOne.Census3.le_localRank_PSL_four hp2 hK))).elim
  · exact (false_of_three_le_localRank he e' hp hp2 (hpZ (by omega)) (le_trans (by omega)
      (CFSG.RankThree.PartTwo.Census.four_mul_le_localRank_PSL hp2 hK hn5))).elim

theorem qtkSimpleList_of_cover_psu_odd (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {n p f : ℕ} (hp2 : p ≠ 2) (hm : StatedClassicalModel (↥Y ⧸ center ↥Y) .PSU n p f)
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (center ↥Y) → TablePrime .PSU n p f r) :
    QTKSimpleList (↥Y ⧸ center ↥Y) := by
  obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Finite K := hU.finite
  set e' : (↥Y ⧸ center ↥Y) ≃* unitaryPSU hU n := e.trans (unitaryPSUEquiv hU (by omega)).symm
  have hpZ : (n = 4 → 2 ≤ f) → ¬ p ∣ Nat.card (center ↥Y) := fun hn4 h => by
    rcases hZ p hp hp2 h with ⟨h0, -⟩ | ⟨-, -, h1⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ |
        ⟨-, ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, h1, -, h2⟩⟩
    · cases h0
    · exact not_dvd_pow_add_one hp hf h1
    · cases h0
    · cases h0
    · cases h0
    · cases h0
    · cases h0
    · have := hn4 h1
      omega
  rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | hn5
  · by_cases hf2 : f ≤ 2
    · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inr (Or.inl ⟨f, by omega, Or.inr hm⟩)⟩)
    · exact (false_of_three_le_localRank he e' hp hp2 (hpZ (by omega)) (le_trans (by simp; omega)
        (CFSG.RankThree.PartTwo.Census.le_localRank_unitaryPSU hU hp2 (r := 1) le_rfl
          (by norm_num)))).elim
  · by_cases hf1 : f = 1
    · subst hf1
      by_cases hM : ∃ b : ℕ, p + 1 = 2 ^ b
      · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hM, hm⟩))))⟩)
      · obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_succ hM
        have hrZ : ¬ r ∣ Nat.card (center ↥Y) := fun h => by
          rcases hZ r hr hr2 h with ⟨h0, -⟩ | ⟨-, h1, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ |
              ⟨-, ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, -, h1, -⟩⟩
          · cases h0
          · exact not_dvd_four_of_odd_prime hr hr2 h1
          · cases h0
          · cases h0
          · cases h0
          · cases h0
          · cases h0
          · exact hM ⟨2, by rw [h1]; norm_num⟩
        exact (false_of_three_le_localRank he e hr hr2 hrZ
          (le_localRank_statedSU_torus_odd hU hp2 (m := 3) hr (by rwa [pow_one]) (by norm_num)
            (by norm_num) (Or.inr (not_dvd_four_of_odd_prime hr hr2)))).elim
    · exact (false_of_three_le_localRank he e' hp hp2 (hpZ fun _ => by omega)
        (le_trans (by omega)
          (CFSG.RankThree.PartTwo.Census.le_localRank_unitaryPSU_four hU hp2))).elim
  · exact (false_of_three_le_localRank he e' hp hp2 (hpZ (by omega)) (le_trans (by omega)
      (CFSG.RankThree.PartTwo.Census.le_localRank_unitaryPSU hU hp2 (r := 2) (by norm_num)
        (by omega)))).elim

theorem qtkSimpleList_of_cover_psp_odd (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {n p f : ℕ} (hp2 : p ≠ 2) (hm : StatedClassicalModel (↥Y ⧸ center ↥Y) .PSp n p f)
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (center ↥Y) → TablePrime .PSp n p f r) :
    QTKSimpleList (↥Y ⧸ center ↥Y) := by
  obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hpZ : ¬ p ∣ Nat.card (center ↥Y) := fun h => by
    rcases hZ p hp hp2 h with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ |
        ⟨-, ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩⟩ <;> cases h0
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · by_cases hf1 : f = 1
    · subst hf1
      exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inr (Or.inr (Or.inl hm))⟩)
    · exact (false_of_three_le_localRank he e hp hp2 hpZ (le_trans (by omega)
        (CFSG.RankThree.PartTwo.Census.le_localRank_PSp_two hp2 hK))).elim
  · exact (false_of_three_le_localRank he e hp hp2 hpZ (le_trans (by norm_num)
      (CFSG.RankThree.PartTwo.Census.four_le_localRank_PSp hp2 hK hf hn3))).elim

theorem false_of_cover_statedOmega (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (Q : QuadraticForm K (ι → K))
    {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) (hd : 7 ≤ Fintype.card ι)
    (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (e : ↥Y ⧸ center ↥Y ≃* StatedProj (StatedOmega Q₀)) : False := by
  obtain ⟨e''⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived hQ
  let φ : ↥Y →* CFSG.RankThree.Classical2.ProjOrthDerived Q :=
    (e.trans e'').toMonoidHom.comp (QuotientGroup.mk' (center ↥Y))
  have hφ : Function.Surjective φ := (e.trans e'').surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ center ↥Y := fun x hx => by
    have h1 : (e.trans e'') (QuotientGroup.mk' (center ↥Y) x) = 1 := hx
    rw [MulEquiv.map_eq_one_iff] at h1
    exact (QuotientGroup.eq_one_iff x).mp h1
  have h4 := CFSG.RankThree.PartOne.orthogonal_central_cover_four_le_localRank Y hp hp2 hf hK Q
    (by rw [Module.finrank_fintype_fun_eq_card]; exact hd) hB φ hφ hker
  have h5 := localRank_le_evenRank (G := G) hp hp2
  omega

theorem qtkSimpleList_of_cover_odd_classical (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel (↥Y ⧸ center ↥Y) t n p f)
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (center ↥Y) → TablePrime t n p f r) :
    QTKSimpleList (↥Y ⧸ center ↥Y) := by
  cases t with
  | PSL => exact qtkSimpleList_of_cover_psl_odd he hp2 hm hZ
  | PSU => exact qtkSimpleList_of_cover_psu_odd he hp2 hm hZ
  | PSp => exact qtkSimpleList_of_cover_psp_odd he hp2 hm hZ
  | POmegaOdd =>
    obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
    have : CharP K p := finite_field_prime_power_characteristic hp hf hK
    have : Fact p.Prime := ⟨hp⟩
    have h2 : (2 : K) ≠ 0 := by
      intro h0
      have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    refine (false_of_cover_statedOmega he hp hp2 hf hK (quadOdd n K)
      (CFSG.LieType.Universal.Spin.coe_quadOdd n K) ?_
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd n K h2) e).elim
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  | POmegaPlus =>
    obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hm
    refine (false_of_cover_statedOmega he hp hp2 hf hK (quadPlus n K)
      (CFSG.LieType.Universal.Spin.coe_quadPlus n K) ?_
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K) e).elim
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  | POmegaMinus =>
    obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hm
    refine (false_of_cover_statedOmega he hp hp2 hf hK (quadMinus n K b c)
      (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c) ?_
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
      e).elim
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  | _ => exact hm.2.elim

end CFSG.SectionRank.QTK.CoverB
