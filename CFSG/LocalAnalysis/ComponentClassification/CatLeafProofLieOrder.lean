module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith
public import CFSG.GH74.Orders.LieType
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open CFSG.ComponentClassification.CatLeaf

theorem card_of_reeTitsModel_twistedF4
    {G : Type} [Group G] {f : ℕ} (h : ReeTitsModel G .twistedF4 2 f) :
    Nat.card G = ordTwistedF4 (2 ^ f) := by
  have hS := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier G 2 f h
  obtain ⟨-, a, hfa, hmodel⟩ := h
  subst hfa
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_of_card_eq_prime_pow
    (f := 2 * a + 1) (by
      rw [← Nat.card_eq_fintype_card, hK]
      rfl)
  obtain ⟨E⟩ := hS.2.2.2.2.2 a K rfl hK ⟨e⟩
  have hord :=
    (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion a K
      hK).1
  rw [Nat.card_congr E.toEquiv, hord, ordTwistedF4]
  set q := 2 ^ (2 * a + 1) with hq
  have h1 : 1 ≤ q := Nat.one_le_two_pow
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have h3 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3, h4]
  ring

theorem toNat_pow_sub_neg_one_pow {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = if Even i then q ^ i - 1 else q ^ i + 1 := by
  rcases Nat.even_or_odd i with hi | hi
  · rw [ite_eq_left hi, hi.neg_one_pow]
    have h1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
    have h2 : ((q : ℤ) ^ i - 1) = ((q ^ i - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [h2, Int.toNat_natCast]
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hi), hi.neg_one_pow]
    have h2 : ((q : ℤ) ^ i - -1) = ((q ^ i + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h2, Int.toNat_natCast]

theorem card_eq_lieOrder
    {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (h : LieModel X t n p f) :
    Nat.card X = lieOrderNumerator t n (p ^ f) / lieOrderDivisor t n (p ^ f) := by
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    rw [GH74.card_of_lieModel_PSL (by omega) h, ordA, Nat.sub_add_cancel (by omega : 1 ≤ n),
      mul_comm (n - 1) n]
    rfl
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have hc : Nat.card X = ordTwistedA (n - 1) (p ^ f) := by
      by_cases hp2 : p = 2
      · subst hp2
        exact (Timmesfeld.card_statedClassicalModel_two
          (GH74.statedClassicalModel_of_lieModel (by omega) h)).2.1 rfl
      · exact GH74.card_of_lieModel_PSU (by omega) hp2 h
    rw [hc, ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm (n - 1) n,
      Finset.prod_congr rfl fun i _ => toNat_pow_sub_neg_one_pow (Nat.one_le_pow _ _ hp.pos) i]
    rfl
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have hc : Nat.card X = ordBC n (p ^ f) := by
      by_cases hp2 : p = 2
      · subst hp2
        exact (Timmesfeld.card_statedClassicalModel_two
          (GH74.statedClassicalModel_of_lieModel (by omega) h)).2.2.1 rfl
      · exact GH74.card_of_lieModel_PSp (by omega) hp2 h
    rw [hc, ordBC, ← sq]
    rfl
  case POmegaOdd =>
    obtain ⟨-, -, hn, hp2⟩ := hadm
    have hc := (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
      (GH74.statedClassicalModel_of_lieModel (by omega) h)).2.2.2.1 rfl
    have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    rw [hc, ordBC, ClassicalInvolution.gcd_two_sub_one_of_odd hodd, ← sq]
    rfl
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    have hsc := GH74.statedClassicalModel_of_lieModel (by omega) h
    have hc : Nat.card X = ordD n (p ^ f) := by
      by_cases hp2 : p = 2
      · subst hp2
        exact (Timmesfeld.card_statedClassicalModel_two hsc).2.2.2.1 rfl
      · exact (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hsc).2.2.2.2.1 rfl
    rw [hc, ordD]
    rfl
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    have hsc := GH74.statedClassicalModel_of_lieModel (by omega) h
    have hc : Nat.card X = ordTwistedD n (p ^ f) := by
      by_cases hp2 : p = 2
      · subst hp2
        exact (Timmesfeld.card_statedClassicalModel_two hsc).2.2.2.2 rfl
      · exact (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hsc).2.2.2.2.2 rfl
    rw [hc, ordTwistedD]
    rfl
  case G2 =>
    rw [(Timmesfeld.card_chevalleyExceptionalModel_untwisted
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)).1 rfl, ordG2]
    simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
  case F4 =>
    rw [(Timmesfeld.card_chevalleyExceptionalModel_untwisted
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)).2.1 rfl, ordF4]
    simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
  case E6 =>
    rw [(Timmesfeld.card_chevalleyExceptionalModel_untwisted
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)).2.2.1 rfl, ordE6]
    rfl
  case E7 =>
    rw [(Timmesfeld.card_chevalleyExceptionalModel_untwisted
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)).2.2.2.1 rfl, ordE7]
    rfl
  case E8 =>
    rw [(Timmesfeld.card_chevalleyExceptionalModel_untwisted
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)).2.2.2.2 rfl, ordE8]
    simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
  case twistedE6 =>
    rw [ClassicalInvolution.card_of_twistedChevalleyModel_E6 hp hf
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h).2, ordTwistedE6]
    rfl
  case trialityD4 =>
    have hce := GH74.chevalleyExceptionalModel_of_lieModel (by decide) h
    have hc : Nat.card X = ordTrialityD4 (p ^ f) := by
      by_cases hp2 : p = 2
      · subst hp2
        exact Timmesfeld.card_chevalleyExceptionalModel_two hce
      · exact ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two hp2 hce
    rw [hc, ordTrialityD4]
    simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
  case twistedB2 =>
    rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, hrt, -⟩ | ⟨-, -, hsz⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact absurd hrt (by decide)
    · obtain ⟨rfl, -, -, -, hc⟩ := GH74.card_of_suzukiModel hsz
      rw [hc, ordSuzuki]
      simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
  case twistedG2 =>
    rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hrt⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · obtain ⟨rfl, -, -, -, hc⟩ := ClassicalInvolution.card_of_reeTitsModel_twistedG2 hrt
      rw [hc, ordRee]
      simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
    · exact absurd hsz (by decide)
  case twistedF4 =>
    obtain ⟨-, -, -, rfl, -, -⟩ := hadm
    rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hrt⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · rw [card_of_reeTitsModel_twistedF4 hrt, ordTwistedF4]
      simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
    · exact absurd hsz (by decide)
  case Tits =>
    rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hrt⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · obtain ⟨e⟩ := Sporadic.Schreier.Tits.titsModelEquiv X p f hrt
      rw [Nat.card_congr e.toEquiv, Sporadic.Schreier.Tits.card_titsD]
      simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
    · exact absurd hsz (by decide)

theorem lieOrderFormulasInput
    : LieOrderFormulasInput := by
  intro X _ t n p f hadm h
  have hmul : Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) := by
    rw [card_eq_lieOrder hadm h, Nat.div_mul_cancel (lieOrderDivisor_dvd_numerator hadm)]
  have hnum : lieOrderNumerator t n (p ^ f) ≠ 0 := by
    rw [lieOrderNumerator_eq hadm]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hadm.1.ne_zero))
      (lieOrderCofactor_ne_zero hadm)
  have hX : Nat.card X ≠ 0 := fun h0 => hnum (by rw [← hmul, h0, zero_mul])
  refine ⟨Nat.finite_of_card_ne_zero hX, hmul, ?_⟩
  have hfac := congrArg (fun m => m.factorization p) hmul
  rwa [Nat.factorization_mul hX (lieOrderDivisor_ne_zero hadm), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_lieOrderDivisor hadm), add_zero,
    factorization_lieOrderNumerator hadm] at hfac

end CFSG.ComponentClassification.CatLeafProof
