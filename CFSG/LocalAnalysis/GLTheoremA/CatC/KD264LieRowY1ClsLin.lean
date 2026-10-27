module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsLinRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type} [Field K]

theorem three_ne_zero_of_charP {K : Type} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (h3p : p ≠ 3) : (3 : K) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  exact h3p ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h')

theorem no_cube_root_of_not_dvd_units {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    (hK : ¬ 3 ∣ Nat.card Kˣ) : ∀ c : K, c ^ 2 + c + 1 ≠ 0 := by
  intro c hc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc
  set u : Kˣ := Units.mk0 c hc0 with hu
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    have hval : (u : K) = c := rfl
    rw [Units.val_pow_eq_pow_val, Units.val_one, hval]
    linear_combination (c - 1) * hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply h3
    have hc1 : c = 1 := by
      have := congrArg Units.val h1
      simpa [hu] using this
    subst hc1
    linear_combination hc
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  apply hK
  rw [← hord]
  exact orderOf_dvd_natCard u

theorem pow_two_mul_mod_three {Q : ℕ} (hQ : Q % 3 = 2) (i : ℕ) :
    Q ^ (2 * i) % 3 = 1 ∧ Q ^ (2 * i + 1) % 3 = 2 := by
  have hsq : Q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hQ]
  induction i with
  | zero => simp [hQ]
  | succ i ih =>
    constructor
    · rw [show 2 * (i + 1) = 2 * i + 2 by ring, pow_add, Nat.mul_mod, ih.1, hsq]
    · rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by ring, pow_add, Nat.mul_mod, ih.2, hsq]

theorem three_dvd_pow_sub_one_iff {Q : ℕ} (hQ : Q % 3 = 2) (j : ℕ) :
    3 ∣ Q ^ j - 1 ↔ 2 ∣ j := by
  have hpos : 1 ≤ Q := by omega
  obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' j
  · subst hi
    have h1 := (pow_two_mul_mod_three hQ i).1
    have hpow : 1 ≤ Q ^ (2 * i) := Nat.one_le_pow _ _ hpos
    constructor
    · intro _
      exact ⟨i, rfl⟩
    · intro _
      omega
  · subst hi
    have h1 := (pow_two_mul_mod_three hQ i).2
    have hpow : 1 ≤ Q ^ (2 * i + 1) := Nat.one_le_pow _ _ hpos
    constructor
    · intro h3
      omega
    · intro h2
      omega

theorem projectiveSL_pRank_ge_four_of_five' [Finite K] {n : ℕ} (hn : n = 5) (h : 3 ∣ Nat.card K - 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL n K)) := by
  subst hn
  exact projectiveSL_pRank_ge_four_of_five h

theorem KD264Y1ClsLin_holds : KD264Y1ClsLin := by
  intro ⟨e, hv⟩ hfin hR hk2 hk3 hpR hA
  obtain ⟨r, q, hd⟩ := hA
  have hd' : e = TauCeti.LieTypeIndex.A r q := hd
  subst hd'
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hqcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  set K : Type := GaloisField q.p q.exponent with hKdef
  have hcardK : Nat.card K = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
  let eS : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A r q, hv⟩).Group ≃*
      projectiveSL (r + 1) K :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (r + 1) K).symm)
  have hpS : CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL (r + 1) K)) = 3 := by
    have h := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eS
    rw [← h]
    exact hpR
  by_cases hp3 : q.p = 3
  ·
    exfalso
    apply hR
    exact Or.inl ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A r q, hv⟩,
      by simp [CFSG.Yardstones.Md0ec50421ce4.onLie, hp3], ⟨MulEquiv.refl _⟩⟩
  have h3q : ¬ 3 ∣ q.card := three_not_dvd_card_of_char_ne_three q hp3
  have hcard_mod : q.card % 3 = 1 ∨ q.card % 3 = 2 := by omega
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  ·
    exfalso
    have hr1 : r = 1 := by omega
    subst hr1
    exact hk2 ⟨rfl, h3q⟩
  · rcases hcard_mod with hm1 | hm2
    ·
      have hdiv : 3 ∣ Nat.card K - 1 := by
        rw [hcardK]
        omega
      rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with hr3 | hr3 | hr3 | hr3
      ·
        exfalso
        subst hr3
        have hdiv' : 3 ∣ q.card - 1 := by omega
        rcases A2_excluded q hdiv' with h | h
        · exact hk2 h
        · exact hk3 h
      ·
        subst hr3
        exact Or.inl ⟨q, rfl, by omega⟩
      ·
        exfalso
        have h4 := projectiveSL_pRank_ge_four_of_five' (K := K) (n := r + 1) (by omega) hdiv
        omega
      ·
        exfalso
        obtain ⟨E, hE, hc⟩ := exists_elemAbelian_card_81 (K := K) (m := r + 1) (by omega) hdiv
        have h4 := le_pRank_of_elemAbelian_card (k := 4) (by norm_num) le_top hE hc
        omega
    ·
      have hpK : ¬ 3 ∣ Nat.card K := by
        rw [hcardK]
        exact h3q
      have h3K : (3 : K) ≠ 0 := three_ne_zero_of_charP (K := K) q.p hp3
      have hK : ¬ 3 ∣ Nat.card Kˣ := by
        rw [Nat.card_units, hcardK]
        omega
      have hω : ∀ c : K, c ^ 2 + c + 1 ≠ 0 := no_cube_root_of_not_dvd_units h3K hK
      have hpe : ∀ j : ℕ, 3 ∣ Nat.card K ^ j - 1 ↔ 2 ∣ j := by
        intro j
        rw [hcardK]
        exact three_dvd_pow_sub_one_iff hm2 j
      rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ 7 ≤ r by omega) with
        hr3 | hr3 | hr3 | hr3 | hr3 | hr3
      ·
        exfalso
        have := projectiveSL_pRank_le (K := K) h3K hω (r + 1)
        omega
      ·
        exfalso
        have := projectiveSL_pRank_le (K := K) h3K hω (r + 1)
        omega
      ·
        exfalso
        have := projectiveSL_pRank_le (K := K) h3K hω (r + 1)
        omega
      ·
        subst hr3
        exact Or.inr (Or.inr (Or.inl ⟨q, rfl, by omega⟩))
      ·
        subst hr3
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, by omega⟩))))
      ·
        exfalso
        have h4 := projectiveSL_pRank_ge_four_of_two (K := K) hω hpK hpe (n := r + 1) (by omega)
        omega

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
