module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLTwistedBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTwE6Chains
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcVal
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
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (twE6Fac foldMask_compl_E6 twistedParabolicSum_twE6_coat_eq card_graphFixedParabolic_eq_borel_mul
    geomSum_mul_sub_one)

namespace OLTwisted

theorem not_dvd_prod_geomSum {r q e : ℕ} (hr : r.Prime) (hq : 1 ≤ q)
    (hdv : ∀ k : ℕ, r ∣ q ^ k - 1 → e ∣ k) (fs : List (ℕ × ℕ))
    (hfs : ∀ g ∈ fs, ¬ e ∣ g.2 * g.1) :
    ¬ r ∣ (fs.map fun g => geomSum g.1 g.2 q).prod := by
  induction fs with
  | nil =>
    intro h
    exact hr.one_lt.ne' (Nat.dvd_one.1 (by simpa using h))
  | cons g fs ih =>
    intro h
    rw [List.map_cons, List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
    · have h2 : geomSum g.1 g.2 q ∣ q ^ (g.2 * g.1) - 1 :=
        Dvd.intro _ (geomSum_mul_sub_one g.1 g.2 q hq)
      exact hfs g List.mem_cons_self (hdv _ (h1.trans h2))
    · exact ih (fun g' hg' => hfs g' (List.mem_cons_of_mem _ hg')) h1


theorem not_dvd_card_normalizer_graphFixed_E6 {F : Type} [Field F] [Finite F] [CharP F 2]
    (σ : F ≃+* F) {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hH : Holds (graphFixedRootGroup TwistTag.E6 F σ.toRingHom) 2) {r : ℕ} (hr : r.Prime)
    (hdv : ∀ k : ℕ, r ∣ (2 ^ f) ^ k - 1 ↔ 18 ∣ k)
    {U : Subgroup (graphFixedRootGroup TwistTag.E6 F σ.toRingHom)} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) :
    ¬ r ∣ Nat.card
      (Subgroup.normalizer (U : Set (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))) := by
  classical
  haveI : Fintype (WeylGroup TwistTag.E6.tag) := Fintype.ofFinite _
  obtain ⟨a, ha⟩ := exists_card_normalizer_dvd_card_maximal_parabolic TwistTag.E6 σ hH hU hU2
  have hq : ∀ b, Nat.card (orbitField TwistTag.E6 F σ.toRingHom b) =
      (2 ^ f) ^ (TwistTag.E6.orbit b).card := card_orbitField Nat.prime_two hf hF hσ
  have eP : Nat.card (graphFixedParabolic TwistTag.E6 F σ.toRingHom {b | b ≠ a}) =
      Nat.card (graphFixedRootBorel TwistTag.E6 F σ.toRingHom) *
        ((twE6Fac a).map fun g => geomSum g.1 g.2 (2 ^ f)).prod := by
    rw [card_graphFixedParabolic_eq_borel_mul σ hq, foldMask_compl_E6,
      twistedParabolicSum_twE6_coat_eq]
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hk : ∀ c : Fin TwistTag.E6.foldedTag.rank,
      (TwistTag.E6.orbit c).card = 1 ∨ (TwistTag.E6.orbit c).card = 2 := by decide
  have hfs : ∀ c : Fin TwistTag.E6.foldedTag.rank, ∀ g ∈ twE6Fac c, ¬ 18 ∣ g.2 * g.1 := by
    decide
  rw [eP] at ha
  intro hrN
  rcases (Nat.Prime.dvd_mul hr).1 (hrN.trans ha) with h1 | h1
  · refine not_dvd_card_graphFixedRootBorel σ hr hq
      (not_dvd_of_dvd_pow_sub_one hq1 (by norm_num) hr ((hdv 18).2 dvd_rfl)) (fun c hc => ?_) h1
    have h4 := (hdv _).1 hc
    rcases hk c with h5 | h5 <;> rw [h5] at h4 <;> omega
  · exact not_dvd_prod_geomSum hr hq1 (fun k hk' => (hdv k).1 hk') (twE6Fac a) (hfs a) h1

end OLTwisted

open OLTwisted

theorem twoLocalWhen_twistedE6
    (_hLie : LieOrderFormulasInput) :
    TwoLocalWhen .twistedE6 (fun _ _ => True) := by
  intro K _ _ hs hab n f f₀ p _ hadm hmodel ht hp hp5 hpK hdiv hf
  obtain ⟨-, hf1, hn⟩ := hadm
  have hn0 : n = 0 := hn
  subst hn0
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  obtain ⟨r, hr, hz⟩ := exists_zsig_prime_twelve_eighteen hf₀ (Or.inr rfl) hp hp5
  have hdv : ∀ k : ℕ, r ∣ (2 ^ f) ^ k - 1 ↔ 18 ∣ k := fun k => by
    rw [hf]
    exact (hz k).2
  have hchev : ChevalleyExceptionalModel K .twistedE6 2 f := by
    rcases hmodel with ⟨ht', -⟩ | ⟨-, -, h⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact h
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFfin, σ, hFcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf1 hchev.2
  have hF : Nat.card F = (2 ^ f) ^ 2 := hFcard
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hF2 : Fintype.card F = 2 ^ (2 * f) := by
    rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm]
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hF2
  haveI : Finite (ModGL TwistTag.E6.tag F) := finite_modGL
  have hH : Holds (graphFixedRootGroup TwistTag.E6 F σ.toRingHom) 2 :=
    (holds_of_chevalleyExceptionalModel hchev).of_mulEquiv e
  refine ⟨r, hr, fun R hR2 hR1 => ?_⟩
  have hRn : ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set K)) :=
    not_dvd_card_normalizer_of_mulEquiv e (fun U hU2 hU1 =>
      not_dvd_card_normalizer_graphFixed_E6 σ hf1 hF hσ hH hr hdv hU1 hU2) R hR2 hR1
  have hq1 : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
  have hq2 : 1 < 2 ^ f₀ := Nat.one_lt_two_pow (by omega)
  have hdr : ¬ r ∣ lieOrderDivisor .twistedE6 0 (2 ^ f₀) := by
    intro h
    simp only [lieOrderDivisor] at h
    have h1 : r ∣ 1 + 2 ^ f₀ := by
      rw [add_comm]
      exact h.trans (Nat.gcd_dvd_right 3 _)
    exact absurd (((hz 2).1).1 (dvd_sq_sub_one_of_dvd_one_add hq1 h1)) (by omega)
  have hfac : (2 ^ f₀) ^ 18 - 1 = ((2 ^ f₀) ^ 9 - 1) * ((2 ^ f₀) ^ 9 + 1) := by
    have h1 : 1 ≤ (2 ^ f₀) ^ 9 := Nat.one_le_pow _ _ hq1
    have h2 : 1 ≤ (2 ^ f₀) ^ 18 := Nat.one_le_pow _ _ hq1
    zify [h1, h2]
    ring
  have hrn : r ∣ lieOrderNumerator .twistedE6 0 (2 ^ f₀) := by
    have h18 : r ∣ (2 ^ f₀) ^ 18 - 1 := ((hz 18).1).2 dvd_rfl
    rw [hfac] at h18
    have h9 : r ∣ (2 ^ f₀) ^ 9 + 1 := by
      rcases (Nat.Prime.dvd_mul hr).1 h18 with h | h
      · exact absurd (((hz 9).1).1 h) (by omega)
      · exact h
    simp only [lieOrderNumerator]
    exact (((((h9.mul_left _).mul_right _).mul_right _).mul_right _).mul_right _)
  have hnum0 : lieOrderNumerator .twistedE6 0 (2 ^ f₀) ≠ 0 := by
    simp only [lieOrderNumerator]
    have hpos : ∀ k : ℕ, k ≠ 0 → (2 ^ f₀) ^ k - 1 ≠ 0 := fun k hk => by
      have := Nat.one_lt_pow hk hq2
      omega
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero _ (pow_ne_zero _ two_ne_zero)) (hpos 12 (by norm_num))) (by positivity))
      (hpos 8 (by norm_num))) (hpos 6 (by norm_num))) (by positivity)) (hpos 2 (by norm_num))
  exact padicValNat_add_lt_of_not_dvd hr hRn hdr hnum0 hrn

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
