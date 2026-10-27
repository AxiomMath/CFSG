module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenSplit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLF4Core

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Blueprint (AdjointQuotient)
open CFSG.Blueprint.Chevalley (Tag adjointGroup)
open CFSG.LieType.Chevalley (WeylGroup torusGroup center_adjointGroup_eq_bot)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator LieOrderFormulasInput)
open CFSG.LieType.SeitzGeneration (dvd_pow_sub_one_iff_orderOf)
open CFSG.Timmesfeld.ExceptionalOrders
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (goodFactors_of_bound GoodFactors cntFactors chainFactors chain_prod_eq)

section Chains

@[expose] def g2CertJ1 : OrbitCert .G2 where
  lam := 152
  pts := [
    167, 105]
  parents := [
    1]
  table := [
    256, 0]
  lens := [
    0, 1]

@[expose] def g2ChainJ0 : List (ChainStep .G2) := [⟨1, 0, g2Cert1, [(2, 1)]⟩]

@[expose] def g2ChainJ1 : List (ChainStep .G2) := [⟨2, 0, g2CertJ1, [(2, 1)]⟩]

theorem g2ChainJ0_check : chainCheck g2ChainJ0 1 = true := by
  decide +kernel

theorem g2ChainJ1_check : chainCheck g2ChainJ1 2 = true := by
  decide +kernel

@[expose] def g2Coat : Fin Tag.G2.rank → ℕ := ![2, 1]

@[expose] def g2CoatFactors : Fin Tag.G2.rank → List (ℕ × ℕ) := ![[(2, 1)], [(2, 1)]]

theorem g2Coat_cover : ∀ i k : Fin Tag.G2.rank, k ≠ i → k ∈ maskSet .G2 (g2Coat i) := by
  decide

theorem chainFactors_g2ChainJ0 : chainFactors g2ChainJ0 = [(2, 1)] := rfl

theorem chainFactors_g2ChainJ1 : chainFactors g2ChainJ1 = [(2, 1)] := rfl

variable [Fintype (WeylGroup .G2)]

theorem parabolicSum_G2_coat_eq (i : Fin Tag.G2.rank) (q : ℕ) :
    parabolicSum .G2 (maskSet .G2 (g2Coat i)) q =
      ((g2CoatFactors i).map fun f => geomSum f.1 f.2 q).prod := by
  fin_cases i
  · have h := parabolicSum_eq_of_chainCheck q _ _ g2ChainJ1_check
    rw [chain_prod_eq, chainFactors_g2ChainJ1] at h
    exact h
  · have h := parabolicSum_eq_of_chainCheck q _ _ g2ChainJ0_check
    rw [chain_prod_eq, chainFactors_g2ChainJ0] at h
    exact h

end Chains

set_option linter.unusedVariables false in
theorem twoLocalWhen_G2
    (hLie : LieOrderFormulasInput) : TwoLocalWhen .G2 (fun _ _ => True) := by
  intro K _ _ _ _ n f f₀ p _ hadm hmodel _ hp hp5 _ _ hf
  have hn : n = 0 := hadm.2.2.1
  subst hn
  obtain ⟨F, hF, hFfin, hFcard, ⟨e⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ f ∧ Nonempty (K ≃* AdjointQuotient Tag.G2 F) := by
    rcases hmodel with ⟨h, -⟩ | ⟨-, -, hE⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact hE.2
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  let θ : K ≃* adjointGroup Tag.G2 F := e.trans
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · have := hadm.2.1
      rw [h0, mul_zero] at hf
      omega
    · exact h0
  have hp3 : ¬ p ∣ 3 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  obtain ⟨r, hr, hr2, hdivk, hord⟩ := exists_zsigPrime hf₀ (by norm_num : 2 ≤ 3)
    (fun h => by omega) hp hp3
  refine ⟨r, hr, fun R hR2 hR1 => ?_⟩
  haveI : Fintype (WeylGroup Tag.G2) := Fintype.ofFinite _
  have hrF : ¬ r ∣ Nat.card F := by
    rw [hFcard]
    exact fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have he : orderOf ((Nat.card F : ℕ) : ZMod r) = 3 := by
    rw [hFcard, hf]
    exact hord
  have hH : ¬ r ∣ Nat.card (torusGroup Tag.G2 F) := by
    rw [card_torusGroup_G2]
    intro h
    have h1 : r ∣ Nat.card F ^ 1 - 1 := by
      rw [pow_one]
      exact hr.dvd_of_dvd_pow h
    have h2 := (dvd_pow_sub_one_iff_orderOf Nat.card_pos he).1 h1
    omega
  have hB : 2 < r * 3 := by
    have := hr.two_le
    omega
  have hGC : ∀ i, GoodFactors r 3 (g2CoatFactors i) := fun i =>
    goodFactors_of_bound (by norm_num) hB (by fin_cases i <;> decide)
  have hcnt : ∀ i, cntFactors 3 (g2CoatFactors i) = 0 := fun i => by fin_cases i <;> decide
  have hpar := fun J hJ => not_dvd_card_parabolicSubgroup_of_coatoms Tag.G2 hr hr2 hrF he hH
    g2Coat g2CoatFactors g2Coat_cover parabolicSum_G2_coat_eq hGC hcnt J hJ
  have hN := not_dvd_card_normalizer_of_adjointEquiv Tag.G2 θ hpar R hR2 hR1
  have hq2 : 1 < 2 ^ f₀ := Nat.one_lt_two_pow (by omega)
  have hpos : ∀ m : ℕ, m ≠ 0 → 0 < (2 ^ f₀) ^ m - 1 := fun m hm =>
    Nat.sub_pos_of_lt (Nat.one_lt_pow hm hq2)
  have hnum : lieOrderNumerator .G2 0 (2 ^ f₀) ≠ 0 :=
    (Nat.mul_pos (Nat.mul_pos (pow_pos (by positivity) _) (hpos 6 (by norm_num)))
      (hpos 2 (by norm_num))).ne'
  have h6 : r ∣ (2 ^ f₀) ^ 6 - 1 := (hdivk 6).2 (by norm_num)
  have hrnum : r ∣ lieOrderNumerator .G2 0 (2 ^ f₀) :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_left h6 _) _
  exact padicValNat_add_lt_of_not_dvd hr hN hr.not_dvd_one hnum hrnum

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
