module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLTwistedBase
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4Parab
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenSplit

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.SeitzGeneration
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor LieOrderFormulasInput)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)

namespace OLTwisted

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem card_reeLocalParabolic_eq_borel_mul (j : Fin F4.fixedOrbitCount) :
    Nat.card (F4.reeLocalParabolic K a j) = Nat.card (F4.reeFixedBorel K a) *
      (Nat.card (F4.reeFixedOrbitUnipotent K a j) + 1) := by
  have hfin : Finite (ModGL F4.tag K) := finite_modGL
  have hBP : F4.reeFixedBorel K a ≤ F4.reeLocalParabolic K a j :=
    reeFixedBorel_le_reeGamma_inf_parabolicSubgroup _
  have hidx : (F4.reeFixedBorel K a).relIndex (F4.reeLocalParabolic K a j) =
      Nat.card (F4.reeFixedOrbitUnipotent K a j) + 1 := by
    rw [← CFSG.QuasithinUnique.Setup.X6.ncard_image_coset_eq_relIndex]
    change (F4.reeLocalCosets K a j).ncard = _
    rw [ncard_reeLocalCosets]
  have h := Subgroup.relIndex_mul_card (F4.reeFixedBorel K a) (F4.reeLocalParabolic K a j)
  rw [inf_eq_left.2 hBP, hidx] at h
  rw [mul_comm]
  exact h.symm

theorem not_dvd_card_reeLocalParabolic (hK : Nat.card K = 2 ^ (2 * a + 1)) {r : ℕ}
    (hr : r.Prime) (hdv : ∀ k : ℕ, r ∣ (2 ^ (2 * a + 1)) ^ k - 1 ↔ 12 ∣ k)
    (j : Fin F4.fixedOrbitCount) : ¬ r ∣ Nat.card (F4.reeLocalParabolic K a j) := by
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hrq : ¬ r ∣ 2 ^ (2 * a + 1) :=
    not_dvd_of_dvd_pow_sub_one hq1 (by norm_num) hr ((hdv 12).2 dvd_rfl)
  have hB : ¬ r ∣ (2 ^ (2 * a + 1)) ^ 12 * (2 ^ (2 * a + 1) - 1) ^ 2 := by
    intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
    · exact hrq (hr.dvd_of_dvd_pow h1)
    · have h2 := hr.dvd_of_dvd_pow h1
      have h3 := (hdv 1).1 (by rwa [pow_one])
      omega
  rw [card_reeLocalParabolic_eq_borel_mul, CFSG.RankThree.LargeReeOrder.card_reeFixedBorel hK]
  fin_cases j
  · rw [card_reeFixedOrbitUnipotent_zero hK, hK]
    intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
    · exact hB h1
    · have h1' : r ∣ 1 + 2 ^ (2 * a + 1) := by rwa [add_comm] at h1
      have h2 := dvd_sq_sub_one_of_dvd_one_add hq1 h1'
      have h3 := (hdv 2).1 h2
      omega
  · rw [card_reeFixedOrbitUnipotent_one hK, hK]
    intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
    · exact hB h1
    · have hx : 1 ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.one_le_pow _ _ hq1
      have h1' : r ∣ 1 + (2 ^ (2 * a + 1)) ^ 2 := by rwa [add_comm] at h1
      have h2 := dvd_sq_sub_one_of_dvd_one_add hx h1'
      rw [← pow_mul] at h2
      have h3 := (hdv _).1 h2
      omega

theorem not_dvd_card_normalizer_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) {r : ℕ}
    (hr : r.Prime) (hdv : ∀ k : ℕ, r ∣ (2 ^ (2 * a + 1)) ^ k - 1 ↔ 12 ∣ k)
    {R : Subgroup ↥(F4.reeGamma K a)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set ↥(F4.reeGamma K a))) := by
  intro hrN
  have hfin : Finite (ModGL F4.tag K) := finite_modGL
  set E : Subgroup ↥(F4.reeGamma K a) := Subgroup.normalizer (R : Set ↥(F4.reeGamma K a))
    with hE
  set A : Subgroup (ModGL F4.tag K) := E.map (F4.reeGamma K a).subtype with hA
  set R' : Subgroup (ModGL F4.tag K) := R.map (F4.reeGamma K a).subtype with hR'
  have hAΓ : A ≤ F4.reeGamma K a := Subgroup.map_subtype_le _
  have hRΓ : R' ≤ F4.reeGamma K a := Subgroup.map_subtype_le _
  have hR0 : R' ≠ ⊥ := fun h =>
    hR ((Subgroup.map_eq_bot_iff_of_injective R (F4.reeGamma K a).subtype_injective).1 h)
  have hRp : IsPGroup 2 R' := hR2.map _
  have hAR : A ≤ Subgroup.normalizer (R' : Set (ModGL F4.tag K)) :=
    Subgroup.le_normalizer_map _
  obtain ⟨y, hy, j, hj⟩ := exists_conj_le_reeLocalParabolic hK hAΓ hRΓ hR0 hRp hAR
  refine not_dvd_card_reeLocalParabolic hK hr hdv j (hrN.trans ?_)
  have h1 := Subgroup.card_dvd_of_le hj
  rw [Subgroup.card_map_of_injective (MulAut.conj y).injective] at h1
  rwa [hA, Subgroup.card_map_of_injective (F4.reeGamma K a).subtype_injective] at h1

end OLTwisted

open OLTwisted

theorem twoLocalWhen_twistedF4
    (_hLie : LieOrderFormulasInput) :
    TwoLocalWhen .twistedF4 (fun _ _ => True) := by
  intro K _ _ hs hab n f f₀ p _ hadm hmodel ht hp hp5 hpK hdiv hf
  obtain ⟨-, hf1, hn, -⟩ := hadm
  have hn0 : n = 0 := hn
  subst hn0
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  obtain ⟨r, hr, hz⟩ := exists_zsig_prime_twelve_eighteen hf₀ (Or.inl rfl) hp hp5
  have hR : ReeTitsModel K .twistedF4 2 f := by
    rcases hmodel with ⟨ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, -, h⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
    · exact h
    · exact absurd ht' (by decide)
  obtain ⟨-, -, -, -, -, -, hmain⟩ :=
    large_Ree_model_field_outer_group_and_inner_involutions K 2 f hR
  obtain ⟨-, a, hfa, F, _, _, hFcard, he⟩ := hR
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F F4.prime :=
    charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [← Nat.card_eq_fintype_card, hFcard])
  obtain ⟨⟨e⟩, -⟩ := hmain a F hfa hFcard he
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [hFcard, hfa]
  have hdv : ∀ k : ℕ, r ∣ (2 ^ (2 * a + 1)) ^ k - 1 ↔ 12 ∣ k := fun k => by
    rw [← hfa, hf]
    exact (hz k).2
  haveI : Finite (ModGL F4.tag F) := finite_modGL
  refine ⟨r, hr, fun R hR2 hR1 => ?_⟩
  have hRn : ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set K)) :=
    not_dvd_card_normalizer_of_mulEquiv e (fun U hU2 hU1 =>
      not_dvd_card_normalizer_reeGamma hK hr hdv hU1 hU2) R hR2 hR1
  have hq1 : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
  have hq2 : 1 < 2 ^ f₀ := Nat.one_lt_two_pow (by omega)
  have hdr : ¬ r ∣ lieOrderDivisor .twistedF4 0 (2 ^ f₀) := by
    simp only [lieOrderDivisor]
    exact fun h => hr.one_lt.ne' (Nat.dvd_one.1 h)
  have hfac : (2 ^ f₀) ^ 12 - 1 = ((2 ^ f₀) ^ 6 - 1) * ((2 ^ f₀) ^ 6 + 1) := by
    have h1 : 1 ≤ (2 ^ f₀) ^ 6 := Nat.one_le_pow _ _ hq1
    have h2 : 1 ≤ (2 ^ f₀) ^ 12 := Nat.one_le_pow _ _ hq1
    zify [h1, h2]
    ring
  have hrn : r ∣ lieOrderNumerator .twistedF4 0 (2 ^ f₀) := by
    have h12 : r ∣ (2 ^ f₀) ^ 12 - 1 := ((hz 12).1).2 dvd_rfl
    rw [hfac] at h12
    have h6 : r ∣ (2 ^ f₀) ^ 6 + 1 := by
      rcases (Nat.Prime.dvd_mul hr).1 h12 with h | h
      · exact absurd (((hz 6).1).1 h) (by omega)
      · exact h
    simp only [lieOrderNumerator]
    exact ((((h6.mul_left _).mul_right _).mul_right _).mul_right _)
  have hnum0 : lieOrderNumerator .twistedF4 0 (2 ^ f₀) ≠ 0 := by
    simp only [lieOrderNumerator]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero _ (pow_ne_zero _ two_ne_zero)) (by positivity)) ?_) (by positivity)) ?_
    · have := Nat.one_lt_pow (by norm_num : 4 ≠ 0) hq2
      omega
    · omega
  exact padicValNat_add_lt_of_not_dvd hr hRn hdr hnum0 hrn

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
