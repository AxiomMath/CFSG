module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreExcOut
public import CFSG.RankThree.PartOne.KF.ClsCenter

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.LieType.Steinberg.CentralExt
open CFSG.BenderSuzuki.MatrixGroups (SuzukiMatrixGroup)

theorem odd_genericOrders_two {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) :
    Odd ((genericOrders t n 2 f).1 * (genericOrders t n 2 f).2) := by
  obtain ⟨-, hf, ht⟩ := hadm
  have hq : Even (2 ^ f) := (Nat.even_pow' (by omega)).mpr even_two
  have hq1 : Odd (2 ^ f - 1) := by
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    obtain ⟨k, hk⟩ := hq
    exact ⟨k - 1, by omega⟩
  have hq1' : Odd (2 ^ f + 1) := hq.add_one
  have hgcd : ∀ (a : ℕ) {b : ℕ}, Odd b → Odd (Nat.gcd a b) := fun a b hb =>
    Odd.of_dvd_nat hb (Nat.gcd_dvd_right a b)
  cases t
  case POmegaOdd => exact absurd rfl ht.2
  case POmegaMinus =>
    have hn : n ≠ 0 := by
      have h4 : 4 ≤ n := ht
      omega
    simp only [genericOrders, mul_one]
    exact hgcd _ ((Nat.even_pow' hn).mpr hq).add_one
  case POmegaPlus =>
    simp only [genericOrders, hq, ↓reduceIte, mul_one]
    exact odd_one
  all_goals simp only [genericOrders, mul_one]
  all_goals first | exact odd_one | exact hgcd _ hq1 | exact hgcd _ hq1'

theorem exceptionalOrders_snd_dvd_fst (t : StatedLieTag) (n p f : ℕ) :
    (exceptionalOrders t n p f).2 ∣ (exceptionalOrders t n p f).1 := by
  unfold exceptionalOrders
  split <;> decide

theorem card_generic_prod_exceptional (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (generic t n p f × exceptional t n p f) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  simp only [generic, exceptional, Nat.card_prod]
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd,
    Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd]
  simp only [Nat.card_zmod]

theorem oddMultiplier_of_griessRow {S : Type} [Group S] [Finite S] {t : StatedLieTag}
    {n p f : ℕ} (h : GriessAll.GriessRow S t n p f)
    (hg : Odd ((genericOrders t n p f).1 * (genericOrders t n p f).2))
    (he : Odd ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2)) :
    RankTwoSporadic.OddMultiplier S := by
  intro A _ _ hA ⟨e⟩
  obtain ⟨hS, ⟨eM⟩⟩ := h
  let π : A →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center A := by
    ext a
    simp [π]
  have hd := RankThree.PartOne.card_ker_dvd_card_hopfMultiplier ⟨hS⟩ ⟨hA⟩ π hπ hker.le
  rw [hker, ← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv,
    Nat.card_congr eM.toEquiv, card_generic_prod_exceptional] at hd
  exact Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨hg, he⟩) hd

theorem eq_one_of_two_pow_eq_two {f : ℕ} (h : 2 ^ f = 2) : f = 1 :=
  (GriessAll.eq_of_pow_eq_prime Nat.prime_two Nat.prime_two h).2

theorem griessRow_of_char_two
    {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ} (hmodel : Blueprint.LieModel X t n 2 f)
    (hexc : ¬ 2 ∣ (exceptionalOrders t n 2 f).1) : GriessAll.GriessRow X t n 2 f := by
  have hadm := GriessNative.admissible_of_lieModel hmodel
  have hf : 1 ≤ f := hadm.2.1
  have hq2 : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  have hev : 2 ^ f % 2 = 0 := Nat.even_iff.mp ((Nat.even_pow' (by omega)).mpr even_two)
  cases t with
  | PSL => exact GriessClassical.psl_row (GriessNative.classical_of_lieModel hmodel (by decide))
  | PSU =>
    have hcl := GriessNative.classical_of_lieModel hmodel (by decide)
    have hn : 3 ≤ n := hadm.2.2.1
    by_cases he : Even n
    · refine GriessClassical.psu_row hcl he ?_
      by_contra hq
      obtain rfl := eq_one_of_two_pow_eq_two (f := f) (by omega)
      obtain ⟨k, hk⟩ := he
      have : n = 4 ∨ n = 6 := by omega
      rcases this with rfl | rfl <;> exact hexc (by decide)
    · exact GriessClassical.psu_odd_row hcl he
  | PSp =>
    have hcl := GriessNative.classical_of_lieModel hmodel (by decide)
    have hn : 2 ≤ n := hadm.2.2.1
    refine GriessClassical.psp_row hcl ?_
    by_contra hq
    obtain rfl := eq_one_of_two_pow_eq_two (f := f) (by omega)
    have : n = 2 ∨ n = 3 := by omega
    rcases this with rfl | rfl
    · exact absurd rfl hadm.2.2.2
    · exact hexc (by decide)
  | POmegaOdd => exact absurd rfl hadm.2.2.2
  | POmegaPlus =>
    have hcl := GriessNative.classical_of_lieModel hmodel (by decide)
    have hn : 4 ≤ n := hadm.2.2
    refine GriessClassical.pomegaPlus_row hcl ?_
    by_contra hq
    obtain rfl := eq_one_of_two_pow_eq_two (f := f) (by omega)
    obtain rfl : n = 4 := by omega
    exact hexc (by decide)
  | POmegaMinus =>
    exact GriessClassical.pomegaMinus_row (GriessNative.classical_of_lieModel hmodel (by decide))
  | G2 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    have hq3 : 3 ≤ 2 ^ f := hadm.2.2.2
    refine GriessNative.g2_row hce ?_
    by_contra hq
    obtain ⟨-, rfl⟩ := GriessAll.eq_of_pow_eq_four Nat.prime_two (show 2 ^ f = 4 by omega)
    exact hexc (by decide)
  | F4 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    refine GriessNative.f4_row hce ?_
    by_contra hq
    obtain rfl := eq_one_of_two_pow_eq_two (f := f) (by omega)
    exact hexc (by decide)
  | E6 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    exact GriessNative.e6_row hce
  | E7 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    exact GriessNative.e7_row hce
  | E8 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    exact GriessNative.e8_row hce
  | twistedE6 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    refine GriessNative.twistedE6_row hce ?_
    by_contra hq
    obtain rfl := eq_one_of_two_pow_eq_two (f := f) (by omega)
    exact hexc (by decide)
  | trialityD4 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    exact GriessNative.trialityD4_row hce
  | twistedB2 =>
    obtain ⟨rfl, -, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := GriessNative.suzuki_of_lieModel hmodel
    rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
    · exact absurd (by decide) hexc
    · let e' : X ≃* SuzukiMatrixGroup a :=
        e.trans (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)
      let eZ : SuzukiMatrixGroup a ⧸ Subgroup.center (SuzukiMatrixGroup a) ≃*
          SuzukiMatrixGroup a :=
        (QuotientGroup.quotientMulEquivOfEq (SuzukiClosed.suzuki_center_eq_bot ha2)).trans
          QuotientGroup.quotientBot
      refine GriessClassical.of_mulEquiv (e'.trans eZ.symm)
        (GriessExceptional.row_of_subsingleton rfl ?_ (SuzukiClosed.suzuki_hopfMultiplier ha2))
      unfold exceptionalOrders
      split <;> first | rfl | omega
  | twistedG2 => exact absurd hadm.2.2.2.1 (by decide)
  | twistedF4 =>
    obtain ⟨rfl, -⟩ := GriessNative.reeTits_of_lieModel hmodel (by decide)
    exact GriessNative.twistedF4_row hmodel
  | Tits =>
    obtain ⟨rfl, -⟩ := GriessNative.reeTits_of_lieModel hmodel (by decide)
    exact GriessNative.tits_row hmodel

theorem evenLieMultiplierOuterInput_of_exceptionalOuter
    (hout : EvenLieExceptionalOuterInput) : EvenLieMultiplierOuterInput := by
  rintro S _ _ _ _ ⟨t, n, f, hadm, hm⟩ hL34
  by_cases h2 : 2 ∣ (exceptionalOrders t n 2 f).1
  · refine Or.inr (card_outer_le_eight_of_even_exceptional hout hm h2 fun h => ?_)
    rw [Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact hL34 hm
  · have he₁ : Odd (exceptionalOrders t n 2 f).1 := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
    have he₂ : Odd (exceptionalOrders t n 2 f).2 :=
      Odd.of_dvd_nat he₁ (exceptionalOrders_snd_dvd_fst t n 2 f)
    exact Or.inl (oddMultiplier_of_griessRow (griessRow_of_char_two hm h2)
      (odd_genericOrders_two hadm) (Nat.odd_mul.mpr ⟨he₁, he₂⟩))

end CFSG.ComponentClassification.Foote5
