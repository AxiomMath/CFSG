module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTwE6Three
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTwE6Out
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTwE6Four
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTwE6Cyc3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTwE6Cyc6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTwE6Lang
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTwE6LangTorus
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamTw
import CFSG.LieType.SeitzGeneration.ExcHigh.Classes
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Solomon.Coordinator

set_option linter.unusedSectionVars false


private theorem dvd_of_orderOf_eq_three {p n : ℕ} (hp : p.Prime)
    (he : orderOf ((n : ℕ) : ZMod p) = 3) : p ∣ n ^ 2 + n + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h3 : ((n : ℕ) : ZMod p) ^ 3 = 1 := by
    rw [← he]
    exact pow_orderOf_eq_one _
  have h1 : ((n : ℕ) : ZMod p) ≠ 1 := fun h => by
    rw [h, orderOf_one] at he
    omega
  have h2 : (((n : ℕ) : ZMod p) - 1) *
      (((n : ℕ) : ZMod p) ^ 2 + ((n : ℕ) : ZMod p) + 1) = 0 := by
    linear_combination h3
  have h5 := (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 h1)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact h5

private theorem dvd_of_orderOf_eq_four {p n : ℕ} (hp : p.Prime)
    (he : orderOf ((n : ℕ) : ZMod p) = 4) : p ∣ n ^ 2 + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h4 : ((n : ℕ) : ZMod p) ^ 4 = 1 := by
    rw [← he]
    exact pow_orderOf_eq_one _
  have h2 : ((n : ℕ) : ZMod p) ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [he] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h3 : (((n : ℕ) : ZMod p) ^ 2 - 1) * (((n : ℕ) : ZMod p) ^ 2 + 1) = 0 := by
    linear_combination h4
  have h5 := (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 h2)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact h5

theorem perfectCentralizerPlanes_cat_twistedE6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ≠ q.p) : PerfectCentralizerPlanes p (Cat ⟨.twistedE6 q, hv⟩) := by
  classical
  obtain ⟨K, hF, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  letI : Field K := hF
  have hℓ := q.prime_p
  have hf := q.exponent_pos
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ q.p ^ q.exponent := fun h =>
    hpq ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  have hp3 : 3 < p := by omega
  have hn1 : 1 ≤ q.p ^ q.exponent := Nat.one_le_pow _ _ hℓ.pos
  have hplanes : PerfectCentralizerPlanes p (twistedE6RootGroup K σ) := by
    by_cases hcnt : 2 ≤ degCountTw (orderOf (((q.p ^ q.exponent : ℕ)) : ZMod p))
    · rcases HardMathSupport.Timmesfeld.LocalTwo.degCountTw_ge_two hcnt with h1 | h2 | h3 | h4 | h6
      ·
        by_cases hp7 : 7 ≤ p
        · exact PerfectCentralizerPlanes.of_mulEquiv e
            (perfectCentralizerPlanes_cat_twistedE6_one q hv hp hp7 hpq (by rw [hqc]; exact h1))
        · have hp5' : p = 5 := by
            have : p = 5 ∨ p = 6 := by omega
            rcases this with h | h
            · exact h
            · subst h
              exact absurd hp (by norm_num)
          subst hp5'
          have hd : 5 ∣ q.p ^ q.exponent - 1 :=
            HardMathSupport.Timmesfeld.LocalTwo.dvd_sub_one_of_orderOf_eq_one hn1 h1
          exact perfectCentralizerPlanes_twistedE6_five hℓ hf hK σ hσ hpK (Or.inl (by omega))
      ·
        by_cases hp7 : 7 ≤ p
        · exact PerfectCentralizerPlanes.of_mulEquiv e
            (perfectCentralizerPlanes_cat_twistedE6_two q hv hp hp7 hpq (by rw [hqc]; exact h2))
        · have hp5' : p = 5 := by
            have : p = 5 ∨ p = 6 := by omega
            rcases this with h | h
            · exact h
            · subst h
              exact absurd hp (by norm_num)
          subst hp5'
          have hd : 5 ∣ q.p ^ q.exponent + 1 :=
            CFSG.LieType.SeitzGeneration.ExcHigh.dvd_add_one_of_orderOf_eq_two hp h2
          exact perfectCentralizerPlanes_twistedE6_five hℓ hf hK σ hσ hpK (Or.inr (by omega))
      ·
        have hd : p ∣ (q.p ^ q.exponent) ^ 2 + q.p ^ q.exponent + 1 :=
          dvd_of_orderOf_eq_three hp h3
        exact perfectCentralizerPlanes_twistedE6_three_cyc hℓ K hf hK σ hσ hp hp3 hd
      ·
        have hd : p ∣ (q.p ^ q.exponent) ^ 2 + 1 := dvd_of_orderOf_eq_four hp h4
        haveI : Fact q.p.Prime := ⟨hℓ⟩
        haveI : Fintype K := Fintype.ofFinite K
        haveI : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
          (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
        exact perfectCentralizerPlanes_twistedE6_four K hf hK σ hσ hp hp5 hd
      ·
        have hq0 : (((q.p ^ q.exponent : ℕ)) : ZMod p) ≠ 0 := fun h =>
          hpK ((ZMod.natCast_eq_zero_iff _ p).1 h)
        have hdvd : 6 ∣ p - 1 := h6 ▸ ZMod.orderOf_dvd_card_sub_one hq0
        have hpne5 : p ≠ 5 := by
          rintro rfl
          norm_num at hdvd
        have hp7 : 7 ≤ p :=
          HardMathSupport.Timmesfeld.LocalTwo.seven_le_of_prime_of_five_lt hp (by omega)
        have hq3 : 3 ≤ q.p ^ q.exponent := by
          have h2 : 2 ≤ q.p ^ q.exponent := Nat.one_lt_pow hf.ne' hℓ.one_lt
          by_contra hlt
          have hq2 : q.p ^ q.exponent = 2 := by omega
          rw [hq2] at h6
          exact HardMathSupport.Timmesfeld.LangTorus.orderOf_two_ne hp hp7
            (Or.inr (Or.inr (Or.inr rfl))) h6
        exact perfectCentralizerPlanes_twistedE6_six hℓ hf K hK σ hσ hp hp7 hpK h6 hq3
    · exact PerfectCentralizerPlanes.of_rankLE1 hp
        (rankLE1_twistedE6 hℓ hf K hK σ hσ hp hpK (by omega))
  exact PerfectCentralizerPlanes.of_mulEquiv e.symm hplanes

theorem innGoodAt_twistedE6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (h32 : ¬ (p = 3 ∧ q.card = 2)) :
    InnGoodAt p (.twistedE6 q) (Cat ⟨.twistedE6 q, hv⟩) := by
  classical
  obtain ⟨K, hF, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  letI : Field K := hF
  have hℓ := q.prime_p
  have hf := q.exponent_pos
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  refine innGoodAt_of_mulEquiv e.symm ?_
  intro D hD hcard hle
  left
  rcases eq_or_ne p 3 with rfl | hp3
  · exact exists_good_twistedE6_three hℓ (Ne.symm hpq) hf (fun h => h32 ⟨rfl, by rw [hqc]; exact h⟩)
      hK σ hσ D (fun α hα => mem_inndiag_of_mem_innAutDerived_twistedE6 hℓ hf hK σ hσ (hle hα))
      hD hcard
  · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    have hplanes : PerfectCentralizerPlanes p (twistedE6RootGroup K σ) :=
      PerfectCentralizerPlanes.of_mulEquiv e (perfectCentralizerPlanes_cat_twistedE6 q hv hp hp5 hpq)
    have hZ : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
      exceptional_fixed_center_trivial TwistTag.E6 K σ
    have hDi : D ≤ inner (twistedE6RootGroup K σ) := fun α hα =>
      mem_inner_of_mem_innAutDerived_of_pow_eq_one_twistedE6 hℓ hf hK σ hσ hp hp3 (hle hα)
        (hD.2 α hα)
    exact exists_good_of_le_inner hZ hplanes hD hcard hDi

theorem lieInnGood_twistedE6 : LieInnGood fun d => ∃ q, d = .twistedE6 q := by
  intro d p hp hp2 hpc h3 h5 hP
  obtain ⟨idx, hv⟩ := d
  obtain ⟨q, rfl⟩ := hP
  refine innGoodAt_twistedE6 q hv hp hp2 ?_ h3
  rwa [TauCeti.LieTypeIndex.characteristic_twistedE6 q] at hpc

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
