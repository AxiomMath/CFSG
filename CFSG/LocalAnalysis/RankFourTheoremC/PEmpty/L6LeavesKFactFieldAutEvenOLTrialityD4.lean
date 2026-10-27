module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLTwistedBase
public import CFSG.Quasithin.Vol2.F134LieD4Cells
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenSplit

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor LieOrderFormulasInput)
open CFSG.Timmesfeld.ExceptionalOrders

namespace OLTwisted


theorem not_dvd_card_normalizer_graphFixed_D4 {F : Type} [Field F] [Finite F] [CharP F 2]
    (σ : F ≃+* F) {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hH : Holds (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) 2) {r : ℕ} (hr : r.Prime)
    (hdv : ∀ k : ℕ, r ∣ (2 ^ f) ^ k - 1 ↔ 12 ∣ k)
    {U : Subgroup (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) :
    ¬ r ∣ Nat.card
      (Subgroup.normalizer (U : Set (graphFixedRootGroup TwistTag.D4 F σ.toRingHom))) := by
  classical
  obtain ⟨a, ha⟩ := exists_card_normalizer_dvd_card_maximal_parabolic TwistTag.D4 σ hH hU hU2
  have hex : ∀ i : Fin TwistTag.D4.foldedTag.rank, ∃ j : Fin TwistTag.D4.foldedTag.rank,
      ∀ k, k ≠ i → k = j := by decide
  obtain ⟨a', ha'⟩ := hex a
  have hle : graphFixedParabolic TwistTag.D4 F σ.toRingHom {b | b ≠ a} ≤
      graphFixedParabolic TwistTag.D4 F σ.toRingHom {a'} :=
    ((fixed_standard_parabolic_cells TwistTag.D4 F σ).2.2.2.1 _ _).2 (fun k hk => ha' k hk)
  have hfin : Finite (ModGL TwistTag.D4.tag F) := finite_modGL
  have h1 := ha.trans (Subgroup.card_dvd_of_le hle)
  rw [CFSG.Quasithin.F134.LieD4.card_graphFixedParabolic_singleton σ.surjective a',
    CFSG.Quasithin.F134.LieD4.card_graphFixedInversionUnipotent_D4 σ hf hF hσ a'] at h1
  have hqorb := card_orbitField (t := TwistTag.D4) Nat.prime_two hf hF (σ := σ.toRingHom) hσ
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hk : ∀ c : Fin TwistTag.D4.foldedTag.rank,
      (TwistTag.D4.orbit c).card = 1 ∨ (TwistTag.D4.orbit c).card = 3 := by decide
  intro hrN
  rcases (Nat.Prime.dvd_mul hr).1 (hrN.trans h1) with h3 | h3
  · refine not_dvd_card_graphFixedRootBorel σ hr hqorb
      (not_dvd_of_dvd_pow_sub_one hq1 (by norm_num) hr ((hdv 12).2 dvd_rfl)) (fun c hc => ?_) h3
    have h4 := (hdv _).1 hc
    rcases hk c with h5 | h5 <;> rw [h5] at h4 <;> omega
  · have hx : 1 ≤ (2 ^ f) ^ (TwistTag.D4.orbit a').card := Nat.one_le_pow _ _ hq1
    have h4 := dvd_sq_sub_one_of_dvd_one_add hx h3
    rw [← pow_mul] at h4
    have h5 := (hdv _).1 h4
    rcases hk a' with h6 | h6 <;> rw [h6] at h5 <;> omega

end OLTwisted

open OLTwisted

theorem twoLocalWhen_trialityD4
    (_hLie : LieOrderFormulasInput) :
    TwoLocalWhen .trialityD4 (fun _ _ => True) := by
  intro K _ _ hs hab n f f₀ p _ hadm hmodel ht hp hp5 hpK hdiv hf
  obtain ⟨-, hf1, hn⟩ := hadm
  have hn0 : n = 0 := hn
  subst hn0
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  obtain ⟨r, hr, hz⟩ := exists_zsig_prime_twelve_eighteen hf₀ (Or.inl rfl) hp hp5
  have hdv : ∀ k : ℕ, r ∣ (2 ^ f) ^ k - 1 ↔ 12 ∣ k := fun k => by
    rw [hf]
    exact (hz k).2
  have hchev : ChevalleyExceptionalModel K .trialityD4 2 f := by
    rcases hmodel with ⟨ht', -⟩ | ⟨-, -, h⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact h
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFfin, σ, hFcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf1 hchev.2
  have hF : Nat.card F = (2 ^ f) ^ 3 := hFcard
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hF3 : Fintype.card F = 2 ^ (3 * f) := by
    rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm]
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hF3
  haveI : Finite (ModGL TwistTag.D4.tag F) := finite_modGL
  have hH : Holds (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) 2 :=
    (holds_of_chevalleyExceptionalModel hchev).of_mulEquiv e
  refine ⟨r, hr, fun R hR2 hR1 => ?_⟩
  have hRn : ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set K)) :=
    not_dvd_card_normalizer_of_mulEquiv e (fun U hU2 hU1 =>
      not_dvd_card_normalizer_graphFixed_D4 σ hf1 hF hσ hH hr hdv hU1 hU2) R hR2 hR1
  have hq1 : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
  have hq2 : 1 < 2 ^ f₀ := Nat.one_lt_two_pow (by omega)
  have hdr : ¬ r ∣ lieOrderDivisor .trialityD4 0 (2 ^ f₀) := by
    simp only [lieOrderDivisor]
    exact fun h => hr.one_lt.ne' (Nat.dvd_one.1 h)
  have hfac : (2 ^ f₀) ^ 12 - 1 = ((2 ^ f₀) ^ 4 - 1) * ((2 ^ f₀) ^ 8 + (2 ^ f₀) ^ 4 + 1) := by
    have h1 : 1 ≤ (2 ^ f₀) ^ 4 := Nat.one_le_pow _ _ hq1
    have h2 : 1 ≤ (2 ^ f₀) ^ 12 := Nat.one_le_pow _ _ hq1
    zify [h1, h2]
    ring
  have hrn : r ∣ lieOrderNumerator .trialityD4 0 (2 ^ f₀) := by
    have h12 : r ∣ (2 ^ f₀) ^ 12 - 1 := ((hz 12).1).2 dvd_rfl
    rw [hfac] at h12
    have h8 : r ∣ (2 ^ f₀) ^ 8 + (2 ^ f₀) ^ 4 + 1 := by
      rcases (Nat.Prime.dvd_mul hr).1 h12 with h | h
      · exact absurd (((hz 4).1).1 h) (by omega)
      · exact h
    simp only [lieOrderNumerator]
    exact (((h8.mul_left _).mul_right _).mul_right _)
  have hnum0 : lieOrderNumerator .trialityD4 0 (2 ^ f₀) ≠ 0 := by
    simp only [lieOrderNumerator]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ two_ne_zero))
      (by positivity)) ?_) ?_
    · have := Nat.one_lt_pow (by norm_num : 6 ≠ 0) hq2
      omega
    · have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hq2
      omega
  exact padicValNat_add_lt_of_not_dvd hr hRn hdr hnum0 hrn

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
