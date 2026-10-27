module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenSplit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLF4Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcF4

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Blueprint (AdjointQuotient)
open CFSG.Blueprint.Chevalley (Tag adjointGroup)
open CFSG.LieType.Chevalley (WeylGroup torusGroup center_adjointGroup_eq_bot)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator LieOrderFormulasInput)
open CFSG.LieType.SeitzGeneration (dvd_pow_sub_one_iff_orderOf)
open CFSG.RankThree.PartOne.KFU (coatomMask coatomMask_cover)
open CFSG.Timmesfeld.ExceptionalOrders (card_torusGroup_F4)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (f4Coat parabolicSum_F4_coat_eq goodFactors_of_bound GoodFactors cntFactors)

set_option linter.unusedVariables false in
theorem twoLocalWhen_F4
    (hLie : LieOrderFormulasInput) : TwoLocalWhen .F4 (fun _ _ => True) := by
  intro K _ _ _ _ n f f₀ p _ hadm hmodel _ hp hp5 _ _ hf
  have hn : n = 0 := hadm.2.2
  subst hn
  obtain ⟨F, hF, hFfin, hFcard, ⟨e⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ f ∧ Nonempty (K ≃* AdjointQuotient Tag.F4 F) := by
    rcases hmodel with ⟨h, -⟩ | ⟨-, -, hE⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact hE.2
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  let θ : K ≃* adjointGroup Tag.F4 F := e.trans
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · have := hadm.2.1
      rw [h0, mul_zero] at hf
      omega
    · exact h0
  have hp12 : ¬ p ∣ 12 := by
    intro h
    have h' : p ∣ 2 ^ 2 * 3 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hp).1 h' with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
  obtain ⟨r, hr, hr2, hdivk, hord⟩ := exists_zsigPrime hf₀ (by norm_num : 2 ≤ 12)
    (fun h => by omega) hp hp12
  refine ⟨r, hr, fun R hR2 hR1 => ?_⟩
  haveI : Fintype (WeylGroup Tag.F4) := Fintype.ofFinite _
  have hrF : ¬ r ∣ Nat.card F := by
    rw [hFcard]
    exact fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have he : orderOf ((Nat.card F : ℕ) : ZMod r) = 12 := by
    rw [hFcard, hf]
    exact hord
  have hH : ¬ r ∣ Nat.card (torusGroup Tag.F4 F) := by
    rw [card_torusGroup_F4]
    intro h
    have h1 : r ∣ Nat.card F ^ 1 - 1 := by
      rw [pow_one]
      exact hr.dvd_of_dvd_pow h
    have h2 := (dvd_pow_sub_one_iff_orderOf Nat.card_pos he).1 h1
    omega
  have hB : 12 < r * 12 := by
    have := hr.two_le
    omega
  have hGC : ∀ i, GoodFactors r 12 (f4Coat i) := fun i =>
    goodFactors_of_bound (by norm_num) hB (by fin_cases i <;> decide)
  have hcnt : ∀ i, cntFactors 12 (f4Coat i) = 0 := fun i => by fin_cases i <;> decide
  have hpar := fun J hJ => not_dvd_card_parabolicSubgroup_of_coatoms Tag.F4 hr hr2 hrF he hH
    coatomMask f4Coat coatomMask_cover parabolicSum_F4_coat_eq hGC hcnt J hJ
  have hN := not_dvd_card_normalizer_of_adjointEquiv Tag.F4 θ hpar R hR2 hR1
  have hq2 : 1 < 2 ^ f₀ := Nat.one_lt_two_pow (by omega)
  have hpos : ∀ m : ℕ, m ≠ 0 → 0 < (2 ^ f₀) ^ m - 1 := fun m hm =>
    Nat.sub_pos_of_lt (Nat.one_lt_pow hm hq2)
  have hnum : lieOrderNumerator .F4 0 (2 ^ f₀) ≠ 0 :=
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos (by positivity) _)
      (hpos 12 (by norm_num))) (hpos 8 (by norm_num))) (hpos 6 (by norm_num)))
      (hpos 2 (by norm_num))).ne'
  have h12 : r ∣ (2 ^ f₀) ^ 12 - 1 := (hdivk 12).2 dvd_rfl
  have hrnum : r ∣ lieOrderNumerator .F4 0 (2 ^ f₀) :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h12 _) _) _) _
  exact padicValNat_add_lt_of_not_dvd hr hN hr.not_dvd_one hnum hrnum

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
