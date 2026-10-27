module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.KRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Arith2
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalRank
public import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalCoprime
public import CFSG.RankThree.OddKernel.RankOneQuotients
public import CFSG.LocalAnalysis.StandardType.GGLayerCycMCyclic
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.StandardType
open CFSG.Blueprint.Multiplier
open CFSG.StandardType.LayerCycM


private theorem not_dvd_two_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 2 := by
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)

private theorem not_dvd_one_of_prime {p : ℕ} (hp : p.Prime) : ¬ p ∣ 1 := by
  intro h
  exact hp.one_lt.ne' (Nat.dvd_one.mp h)

private theorem not_dvd_two_pow_of_odd_prime {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ 2 ^ k := by
  intro h
  exact not_dvd_two_of_odd_prime hp hp2 (hp.dvd_of_dvd_pow h)

private theorem not_dvd_four_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 4 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact not_dvd_two_pow_of_odd_prime hp hp2

private theorem not_dvd_three_of_odd_prime {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : ¬ p ∣ 3 := by
  intro h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)

private theorem finite_of_finite_prod_left (A : Type) (B : Type) [One B] [Finite (A × B)] :
    Finite A :=
  Finite.of_injective (fun a => (a, (1 : B))) (by intro a b h; simpa using h)

private theorem finite_of_finite_prod_right (A : Type) (B : Type) [One A] [Finite (A × B)] :
    Finite B :=
  Finite.of_injective (fun b => ((1 : A), b)) (by intro a b h; simpa using h)

private theorem pRank_prod_four_fst_le_one
    {A B C D : Type} [Group A] [Finite A] [IsCyclic A]
    [Group B] [Finite B] [Group C] [Finite C] [Group D] [Finite D]
    {p : ℕ} (hp : p.Prime)
    (hB : ¬ p ∣ Nat.card B) (hC : ¬ p ∣ Nat.card C) (hD : ¬ p ∣ Nat.card D) :
    CFSG.Open.pRank p (⊤ : Subgroup ((A × B) × (C × D))) ≤ 1 := by
  have hker : Nat.card (MonoidHom.fst (A × B) (C × D)).ker = Nat.card (C × D) :=
    GL83.I713.card_ker_fst
  have hcop : ¬ p ∣ Nat.card (MonoidHom.fst (A × B) (C × D)).ker := by
    rw [hker, Nat.card_prod]
    exact fun h => (hp.dvd_mul.mp h).elim hC hD
  exact (GL83.I713.pRank_top_le_of_coprime_ker hp (MonoidHom.fst (A × B) (C × D)) hcop).trans
    (GL83.I713.pRank_top_le_one_of_prod (A := A) (B := B) hp hB)

private theorem pRank_model_multiplier_le_one
    {p g1 g2 e1 e2 : ℕ} [Finite (Multiplicative (ZMod g1))]
    [Finite (Multiplicative (ZMod g2))] [Finite (Multiplicative (ZMod e1))]
    [Finite (Multiplicative (ZMod e2))]
    (hp : p.Prime) (hg2 : g2 = 1) (he1 : ¬ p ∣ e1) (he2 : ¬ p ∣ e2) :
    CFSG.Open.pRank p (⊤ : Subgroup
      ((Multiplicative (ZMod g1) × Multiplicative (ZMod g2)) ×
       (Multiplicative (ZMod e1) × Multiplicative (ZMod e2)))) ≤ 1 := by
  subst hg2
  refine pRank_prod_four_fst_le_one hp ?_ ?_ ?_
  · rw [natCard_multiplicative_zmod]
    exact not_dvd_one_of_prime hp
  · rw [natCard_multiplicative_zmod]; exact he1
  · rw [natCard_multiplicative_zmod]; exact he2

private theorem pRank_model_multiplier_snd_le_one
    {p g1 g2 e1 e2 : ℕ} [Finite (Multiplicative (ZMod g1))]
    [Finite (Multiplicative (ZMod g2))] [Finite (Multiplicative (ZMod e1))]
    [Finite (Multiplicative (ZMod e2))]
    (hp : p.Prime) (hg2 : g2 = 1) (hg1 : ¬ p ∣ g1) (he2 : ¬ p ∣ e2) :
    CFSG.Open.pRank p (⊤ : Subgroup
      ((Multiplicative (ZMod g1) × Multiplicative (ZMod g2)) ×
       (Multiplicative (ZMod e1) × Multiplicative (ZMod e2)))) ≤ 1 := by
  subst hg2
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulEquiv.prodComm)]
  refine pRank_prod_four_fst_le_one hp ?_ ?_ ?_
  · rw [natCard_multiplicative_zmod]; exact he2
  · rw [natCard_multiplicative_zmod]; exact hg1
  · rw [natCard_multiplicative_zmod]; exact not_dvd_one_of_prime hp

private theorem genericOrders_pos_char_two (t : CFSG.Assembly.LowTwoRank.StatedLieTag)
    (n f : ℕ) (hf : 1 ≤ f) :
    0 < (genericOrders t n 2 f).1 := by
  have hev : Even (2 ^ f) := (Nat.even_pow' (by omega)).2 even_two
  unfold genericOrders
  split
  all_goals simp_all
  all_goals first |
    (apply Nat.gcd_pos_of_pos_right; omega) |
    (apply Nat.gcd_pos_of_pos_left; omega) | positivity | omega

private theorem genericOrders_second_eq_one_char_two (t : CFSG.Assembly.LowTwoRank.StatedLieTag)
    (n f : ℕ) (hf : 1 ≤ f) :
    (genericOrders t n 2 f).2 = 1 := by
  have hev : Even (2 ^ f) := (Nat.even_pow' (by omega)).2 even_two
  unfold genericOrders
  split
  all_goals simp_all

private theorem exceptionalOrders_eq_one_or_pow_two (lab : GLALabel) (hlab : GLAInLambda2 lab)
    (htag : lab.tag ≠ .B2der) :
    exceptionalOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab) = (1, 1) ∨
    exceptionalOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab) = (2, 1) ∨
    exceptionalOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab) = (2, 2) ∨
    exceptionalOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab) = (4, 4) := by
  rcases lab with ⟨t, ℓ, n⟩
  cases t
  all_goals try (exfalso; exact htag rfl)
  all_goals
    simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
    rcases hlab with ⟨hn, hcond⟩
    simp only [markTag, markRank, markChar, markDeg]
    unfold exceptionalOrders
    split <;> simp_all <;>
      (first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) |
        exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr rfl)))


theorem pRank_griessHopfMultiplier_le_one {X : Type} [Group X] {lab : GLALabel}
    (hlab : GLAInLambda2 lab) (hM : MarkedModel lab X)
    [Finite (CFSG.Open.griessHopfMultiplier X)] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (CFSG.Open.griessHopfMultiplier X)) ≤ 1 := by
  rcases lab with ⟨t, ℓ, n⟩
  by_cases hB2 : t = .B2der
  · subst hB2
    simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
    obtain ⟨-, hℓ, hn⟩ := hlab
    subst hℓ
    subst hn
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
        X .PSL 2 3 2 hM
    have eM' : CFSG.Open.griessHopfMultiplier X ≃*
        ((Multiplicative (ZMod 2) × Multiplicative (ZMod 1)) ×
         (Multiplicative (ZMod 3) × Multiplicative (ZMod 1))) := by
      change CFSG.Open.griessHopfMultiplier X ≃* (generic .PSL 2 3 2 × exceptional .PSL 2 3 2)
      exact eM
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eM']
    by_cases hp3 : p = 3
    · subst hp3
      exact pRank_model_multiplier_snd_le_one (p := 3) (g1 := 2) (g2 := 1) (e1 := 3) (e2 := 1)
        (by norm_num) rfl (by norm_num) (by norm_num)
    · exact pRank_model_multiplier_le_one (p := p) (g1 := 2) (g2 := 1) (e1 := 3) (e2 := 1)
        hp rfl (not_dvd_three_of_odd_prime hp hp3) (not_dvd_one_of_prime hp)
  · by_cases hG2 : t = .G2der
    · subst hG2
      simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
      obtain ⟨-, hℓ, hn⟩ := hlab
      subst hℓ
      subst hn
      obtain ⟨-, ⟨eM⟩⟩ :=
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
          X .PSU 3 3 1 hM
      have eM' : CFSG.Open.griessHopfMultiplier X ≃*
          ((Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) ×
           (Multiplicative (ZMod 1) × Multiplicative (ZMod 1))) := by
        change CFSG.Open.griessHopfMultiplier X ≃* (generic .PSU 3 3 1 × exceptional .PSU 3 3 1)
        exact eM
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eM']
      exact pRank_model_multiplier_le_one (p := p) (g1 := 1) (g2 := 1) (e1 := 1) (e2 := 1)
        hp rfl (not_dvd_one_of_prime hp) (not_dvd_one_of_prime hp)
    · have hchar : markChar ⟨t, ℓ, n⟩ = 2 := by
        cases t <;> simp_all [markChar]
      have hf : 1 ≤ markDeg ⟨t, ℓ, n⟩ := one_le_markDeg hlab
      have hg2 : (genericOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
          (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2 = 1 := by
        rw [hchar]
        exact genericOrders_second_eq_one_char_two (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
          (markDeg ⟨t, ℓ, n⟩) hf
      have hg1 : 0 < (genericOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
          (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1 := by
        rw [hchar]
        exact genericOrders_pos_char_two (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
          (markDeg ⟨t, ℓ, n⟩) hf
      have hE := exceptionalOrders_eq_one_or_pow_two ⟨t, ℓ, n⟩ hlab hB2
      have he1 : ¬ p ∣ (exceptionalOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
          (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1 := by
        rcases hE with h | h | h | h <;> rw [h] <;>
          first | exact not_dvd_one_of_prime hp | exact not_dvd_two_of_odd_prime hp hp2 |
            exact not_dvd_four_of_odd_prime hp hp2
      have he2 : ¬ p ∣ (exceptionalOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
          (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2 := by
        rcases hE with h | h | h | h <;> rw [h] <;>
          first | exact not_dvd_one_of_prime hp | exact not_dvd_two_of_odd_prime hp hp2 |
            exact not_dvd_four_of_odd_prime hp hp2
      obtain ⟨-, ⟨eM⟩⟩ :=
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
          X (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩)
          (markDeg ⟨t, ℓ, n⟩) hM
      haveI : Finite (generic (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
          (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩) ×
          exceptional (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
            (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)) :=
        Finite.of_equiv _ eM.toEquiv
      haveI hAB : Finite (Multiplicative (ZMod (genericOrders (markTag ⟨t, ℓ, n⟩)
          (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1) ×
          Multiplicative (ZMod (genericOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
            (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2)) :=
        finite_of_finite_prod_left
        (Multiplicative (ZMod (genericOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1) × Multiplicative (ZMod (genericOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2))
        (Multiplicative (ZMod (exceptionalOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1) × Multiplicative (ZMod (exceptionalOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2))
      haveI hCD : Finite (Multiplicative (ZMod (exceptionalOrders (markTag ⟨t, ℓ, n⟩)
          (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1) ×
          Multiplicative (ZMod (exceptionalOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
            (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2)) :=
        finite_of_finite_prod_right
        (Multiplicative (ZMod (genericOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1) × Multiplicative (ZMod (genericOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2))
        (Multiplicative (ZMod (exceptionalOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1) × Multiplicative (ZMod (exceptionalOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2))
      haveI : Finite (Multiplicative (ZMod (genericOrders (markTag ⟨t, ℓ, n⟩)
          (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1)) :=
        finite_of_finite_prod_left
          (Multiplicative (ZMod (genericOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
            (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1))
          (Multiplicative (ZMod (genericOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
            (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2))
      haveI : Finite (Multiplicative (ZMod (genericOrders (markTag ⟨t, ℓ, n⟩)
          (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2)) :=
        finite_of_finite_prod_right
          (Multiplicative (ZMod (genericOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
            (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1))
          (Multiplicative (ZMod (genericOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
            (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2))
      haveI : Finite (Multiplicative (ZMod (exceptionalOrders (markTag ⟨t, ℓ, n⟩)
          (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1)) :=
        finite_of_finite_prod_left
          (Multiplicative (ZMod (exceptionalOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
            (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1))
          (Multiplicative (ZMod (exceptionalOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
            (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2))
      haveI : Finite (Multiplicative (ZMod (exceptionalOrders (markTag ⟨t, ℓ, n⟩)
          (markRank ⟨t, ℓ, n⟩) (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2)) :=
        finite_of_finite_prod_right
          (Multiplicative (ZMod (exceptionalOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
            (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1))
          (Multiplicative (ZMod (exceptionalOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
            (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2))
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eM]
      exact pRank_model_multiplier_le_one (p := p)
        (g1 := (genericOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
          (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1)
        (g2 := (genericOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
          (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2)
        (e1 := (exceptionalOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
          (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).1)
        (e2 := (exceptionalOrders (markTag ⟨t, ℓ, n⟩) (markRank ⟨t, ℓ, n⟩)
          (markChar ⟨t, ℓ, n⟩) (markDeg ⟨t, ℓ, n⟩)).2)
        hp hg2 he1 he2



theorem pRank_center_le_one_of_isLabel {K : Type} [Group K] [Finite K] {lab : GLALabel} {p : ℕ}
    (hK : Rk2IsLabel K lab) (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (Subgroup.center K) ≤ 1 := by
  obtain ⟨hQ, hlab, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2 hQ
  haveI : Group.IsPerfect K := hQ'.1
  let X := K ⧸ Subgroup.center K
  haveI : Group.IsPerfect X := CFSG.RankThree.PerfectCover.isPerfect_of_quasisimple_quotient hQ' (MulEquiv.refl X)
  haveI : Finite X := inferInstance
  haveI : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier X) :=
    CFSG.RankThree.PerfectCover.finite_hopfMultiplier (X := X) inferInstance
  haveI : Finite (CFSG.Open.griessHopfMultiplier X) :=
    Finite.of_equiv (CFSG.RankThree.PerfectCover.hopfMultiplier X)
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).symm.toEquiv
  have hgr := pRank_griessHopfMultiplier_le_one hlab hM hp hp2
  let q : K →* X := QuotientGroup.mk' (Subgroup.center K)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = Subgroup.center K := QuotientGroup.ker_mk' _
  have hinc : Function.Surjective (Subgroup.inclusion hk.le) := by
    intro y
    refine ⟨⟨y.1, ?_⟩, Subtype.ext rfl⟩
    rw [hk]
    exact y.2
  let ψ : CFSG.RankThree.PerfectCover.hopfMultiplier X →* Subgroup.center K :=
    (Subgroup.inclusion hk.le).comp
      (CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hq hk.le)
  have hψ : Function.Surjective ψ :=
    hinc.comp (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq hk.le)
  let Φ : CFSG.Open.griessHopfMultiplier X →* Subgroup.center K :=
    ψ.comp (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toMonoidHom
  have hΦ : Function.Surjective Φ :=
    hψ.comp (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).surjective
  have h := CFSG.RankThree.OddKernel.pRank_le_one_of_surjective hp hp2 Φ hΦ (by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hgr)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h
  exact h


theorem evenRank_add_le_of_split {K : Type} [Group K] [Finite K] {p L z : ℕ}
    (hL : L ≤ CFSG.Open.twoLocalPrimeRank p K)
    (hupper : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.twoLocalPrimeRank r K + z ≤ L + 1)
    (he : 5 ≤ CFSG.Open.evenRank K) :
    CFSG.Open.evenRank K + z ≤ CFSG.Open.twoLocalPrimeRank p K + 1 := by
  obtain ⟨r, H, hr, hr2, hH, heq⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.evenRank_attained K (by omega)
  have h1 : CFSG.Open.evenRank K + z = CFSG.Open.pRank r H + z := by rw [← heq]
  calc
    CFSG.Open.evenRank K + z = CFSG.Open.pRank r H + z := h1
    _ ≤ CFSG.Open.twoLocalPrimeRank r K + z := Nat.add_le_add_right
        (CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank r hr H hH) z
    _ ≤ L + 1 := hupper r hr hr2
    _ ≤ CFSG.Open.twoLocalPrimeRank p K + 1 := Nat.add_le_add_right hL 1

theorem evenRank_add_le_of_split_ne {K : Type} [Group K] [Finite K] {p L z : ℕ}
    (hz : z ≤ 1) (hL : L ≤ CFSG.Open.twoLocalPrimeRank p K)
    (hupper : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p →
      CFSG.Open.twoLocalPrimeRank r K + z ≤ L + 1)
    (he : 5 ≤ CFSG.Open.evenRank K) :
    CFSG.Open.evenRank K + z ≤ CFSG.Open.twoLocalPrimeRank p K + 1 := by
  obtain ⟨r, H, hr, hr2, hH, heq⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.evenRank_attained K (by omega)
  rcases eq_or_ne r p with hEq | hrp
  · rw [hEq] at heq hr
    have hep : CFSG.Open.evenRank K ≤ CFSG.Open.twoLocalPrimeRank p K :=
      heq ▸ CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank p hr H hH
    omega
  · calc
      CFSG.Open.evenRank K + z = CFSG.Open.pRank r H + z := by rw [← heq]
      _ ≤ CFSG.Open.twoLocalPrimeRank r K + z := Nat.add_le_add_right
          (CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank r hr H hH) z
      _ ≤ L + 1 := hupper r hr hr2 hrp
      _ ≤ CFSG.Open.twoLocalPrimeRank p K + 1 := Nat.add_le_add_right hL 1

theorem evenRank_add_le_of_four {K : Type} [Group K] [Finite K] {p z : ℕ}
    (hz : z ≤ 1) (he : 5 ≤ CFSG.Open.evenRank K)
    (h4 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → CFSG.Open.twoLocalPrimeRank r K ≤ 4) :
    CFSG.Open.evenRank K + z ≤ CFSG.Open.twoLocalPrimeRank p K + 1 := by
  obtain ⟨r, H, hr, hr2, hH, heq⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.evenRank_attained K (by omega)
  have hrp : r = p := by
    by_contra hne
    have hle := (CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank r hr H hH).trans
      (h4 r hr hr2 hne)
    rw [heq] at hle
    omega
  subst r
  have hmp : CFSG.Open.evenRank K ≤ CFSG.Open.twoLocalPrimeRank p K := by
    rw [← heq]
    exact CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank p hr H hH
  omega

theorem twoLocalPrimeRank_le_rk2Mult {K : Type} [Group K] [Finite K] {lab : GLALabel} {r : ℕ}
    (hK : Rk2IsLabel K lab) (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.twoLocalPrimeRank r K ≤ rk2Mult lab (rk2Ord r lab.n) :=
  (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank r hr K).trans
    (rk2KRank K lab r hK hr hr2)

theorem rk2Mult_le_rank {lab : GLALabel}
    (ht : lab.tag = .A ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD)
    (h1 : 1 ≤ lab.rank) {m : ℕ} (hm : 0 < m) : rk2Mult lab m ≤ lab.rank := by
  rcases ht with ht | ht | ht | ht | ht
  · simp only [rk2Mult, ht]
    by_cases hm1 : m = 1
    · subst hm1
      simp
    · rw [if_neg hm1]
      have hm2 : 2 ≤ m := by omega
      calc (lab.rank + 1) / m ≤ (lab.rank + 1) / 2 := Nat.div_le_div_left hm2 (by norm_num)
        _ ≤ lab.rank := by omega
  all_goals
    by_cases hm3 : 3 ≤ m
    · exact (rk2Mult_bcd_le (by tauto) hm3).trans (Nat.div_le_self _ _)
    · have hmle : m = 1 ∨ m = 2 := by omega
      rcases hmle with rfl | rfl <;> simp [rk2Mult, ht] <;> try (split_ifs <;> omega)

theorem rk2Mult_A_le_div_three {lab : GLALabel} (ht : lab.tag = .A) {m : ℕ} (hm : 3 ≤ m) :
    rk2Mult lab m ≤ (lab.rank + 1) / 3 := by
  simp only [rk2Mult, ht]
  have hm1 : m ≠ 1 := by omega
  simp only [hm1, ↓reduceIte]
  exact Nat.div_le_div_left hm (by norm_num)

theorem rk2Mult_E6_le_six {lab : GLALabel} (ht : lab.tag = .E6) (m : ℕ) :
    rk2Mult lab m ≤ 6 := by
  simp only [rk2Mult, ht]
  exact List.countP_le_length

theorem rk2Mult_E7_le_seven {lab : GLALabel} (ht : lab.tag = .E7) (m : ℕ) :
    rk2Mult lab m ≤ 7 := by
  simp only [rk2Mult, ht]
  exact List.countP_le_length

theorem rk2Mult_E8_le_eight {lab : GLALabel} (ht : lab.tag = .E8) (m : ℕ) :
    rk2Mult lab m ≤ 8 := by
  simp only [rk2Mult, ht]
  exact List.countP_le_length

theorem rk2Mult_F4_le_four {lab : GLALabel} (ht : lab.tag = .F4) (m : ℕ) :
    rk2Mult lab m ≤ 4 := by
  simp only [rk2Mult, ht]
  exact List.countP_le_length

theorem rk2Mult_twE6_le_six {lab : GLALabel} (ht : lab.tag = .twE6) (m : ℕ) :
    rk2Mult lab m ≤ 6 := by
  simp only [rk2Mult, ht]
  exact List.countP_le_length

private theorem twE6_small_four : ∀ m < 61, 1 ≤ m → m ≠ 2 →
    rk2Cnt [(2, true), (5, false), (6, true), (8, true), (9, false), (12, true)] m ≤ 4 := by
  decide

theorem rk2Mult_twE6_le_four_of_ne_two {lab : GLALabel} (ht : lab.tag = .twE6)
    {m : ℕ} (hm : 1 ≤ m) (hm2 : m ≠ 2) : rk2Mult lab m ≤ 4 := by
  simp only [rk2Mult, ht]
  by_cases h : m < 61
  · exact twE6_small_four m h hm hm2
  · rw [rk2Cnt_large [(2, true), (5, false), (6, true), (8, true), (9, false), (12, true)]
      60 (by intro f hf; simp at hf; rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
      (m := m) (by omega)]
    omega

private theorem E7_small_three : ∀ m < 61, 3 ≤ m →
    rk2Cnt [(2, true), (6, true), (8, true), (10, true), (12, true), (14, true), (18, true)] m ≤ 3 := by
  decide

theorem rk2Mult_E7_le_three {lab : GLALabel} (ht : lab.tag = .E7) {m : ℕ} (hm : 3 ≤ m) :
    rk2Mult lab m ≤ 3 := by
  simp only [rk2Mult, ht]
  by_cases h : m < 61
  · exact E7_small_three m h hm
  · rw [rk2Cnt_large [(2, true), (6, true), (8, true), (10, true), (12, true), (14, true),
      (18, true)] 60
      (by intro f hf; simp at hf; rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
      (m := m) (by omega)]
    omega

private theorem E8_small_four : ∀ m < 61, 3 ≤ m →
    rk2Cnt [(2, true), (8, true), (12, true), (14, true), (18, true), (20, true), (24, true),
      (30, true)] m ≤ 4 := by
  decide

theorem rk2Mult_E8_le_four {lab : GLALabel} (ht : lab.tag = .E8) {m : ℕ} (hm : 3 ≤ m) :
    rk2Mult lab m ≤ 4 := by
  simp only [rk2Mult, ht]
  by_cases h : m < 61
  · exact E8_small_four m h hm
  · rw [rk2Cnt_large [(2, true), (8, true), (12, true), (14, true), (18, true), (20, true),
      (24, true), (30, true)] 60
      (by intro f hf; simp at hf; rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
      (m := m) (by omega)]
    omega

theorem rk2Mult_twA_le_half_of_ne_two {lab : GLALabel} (ht : lab.tag = .twA)
    {m : ℕ} (hm : 0 < m) (hm2 : m ≠ 2) : rk2Mult lab m ≤ (lab.rank + 1) / 2 := by
  simp only [rk2Mult, ht]
  have hm2' : m ≠ 2 := hm2
  simp only [hm2', ↓reduceIte]
  split_ifs with h4 h1
  · have hm6 : 6 ≤ m := by omega
    calc 2 * (lab.rank + 1) / m ≤ 2 * (lab.rank + 1) / 6 := Nat.div_le_div_left hm6 (by norm_num)
      _ = (lab.rank + 1) / 3 := by
        rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.mul_div_mul_left (lab.rank + 1) 3 (by norm_num)]
      _ ≤ (lab.rank + 1) / 2 := Nat.div_le_div_left (by norm_num) (by norm_num)
  · by_cases hm1 : m = 1
    · subst hm1
      simp
    · have hm6 : 6 ≤ 2 * m := by omega
      calc (lab.rank + 1) / (2 * m) ≤ (lab.rank + 1) / 6 :=
            Nat.div_le_div_left hm6 (by norm_num)
        _ ≤ (lab.rank + 1) / 2 := Nat.div_le_div_left (by norm_num) (by norm_num)
  · have hm4 : 4 ≤ m := by omega
    calc (lab.rank + 1) / m ≤ (lab.rank + 1) / 4 := Nat.div_le_div_left hm4 (by norm_num)
      _ ≤ (lab.rank + 1) / 2 := Nat.div_le_div_left (by norm_num) (by norm_num)


theorem evenRank_le_of_rk2Mult_le {K : Type} [Group K] [Finite K] {lab : GLALabel} {B : ℕ}
    (hK : Rk2IsLabel K lab) (hB : ∀ m : ℕ, rk2Mult lab m ≤ B) :
    CFSG.Open.evenRank K ≤ B := by
  rw [CFSG.RankThreeEvenClassification.Helpers.evenRank_eq_sup_twoLocalRanks]
  refine csSup_le' ?_
  rintro k ⟨p, hp, hp2, rfl⟩
  exact (twoLocalPrimeRank_le_rk2Mult hK hp hp2).trans (hB _)

theorem evenRank_le_four_of_F4 {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (ht : lab.tag = .F4) : CFSG.Open.evenRank K ≤ 4 :=
  evenRank_le_of_rk2Mult_le hK fun m => rk2Mult_F4_le_four ht m

theorem evenRank_le_two_of_small {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (ht : rk2SmallTag lab) : CFSG.Open.evenRank K ≤ 2 := by
  rw [CFSG.RankThreeEvenClassification.Helpers.evenRank_eq_sup_twoLocalRanks]
  refine csSup_le' ?_
  rintro k ⟨p, hp, hp2, rfl⟩
  exact (twoLocalPrimeRank_le_rk2Mult hK hp hp2).trans
    (rk2Mult_le_two_of_small ht (rk2Ord_pos hp hp2 lab.n))

theorem evenRank_le_four_of_E6_one {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (ht : lab.tag = .E6) (hn : lab.n = 1) :
    CFSG.Open.evenRank K ≤ 4 := by
  rw [CFSG.RankThreeEvenClassification.Helpers.evenRank_eq_sup_twoLocalRanks]
  refine csSup_le' ?_
  rintro k ⟨p, hp, hp2, rfl⟩
  have hm1 : rk2Ord p lab.n ≠ 1 := by rw [hn]; exact rk2Ord_one_ne_one hp
  have hm2 : 2 ≤ rk2Ord p lab.n := by
    have := rk2Ord_pos hp hp2 lab.n
    omega
  refine (twoLocalPrimeRank_le_rk2Mult hK hp hp2).trans ?_
  simp only [rk2Mult, ht]
  exact rk2Cnt_E6_le_four hm2


@[expose] def Rk2SplitW1A : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    lab.tag = .A → p.Prime → p ≠ 2 → p ∣ 2 ^ lab.n - 1 →
      lab.rank - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤
        CFSG.Open.twoLocalPrimeRank p K

@[expose] def Rk2SplitW1BCD : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    (lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D) → p.Prime → p ≠ 2 → p ∣ 2 ^ lab.n - 1 →
      lab.rank - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤
        CFSG.Open.twoLocalPrimeRank p K

@[expose] def Rk2SplitW1E6 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    lab.tag = .E6 → p.Prime → p ≠ 2 → p ∣ 2 ^ lab.n - 1 →
      5 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K

@[expose] def Rk2SplitW1E7 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    lab.tag = .E7 → p.Prime → p ≠ 2 → p ∣ 2 ^ lab.n - 1 →
      6 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K

@[expose] def Rk2SplitW1E8 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    lab.tag = .E8 → p.Prime → p ≠ 2 → p ∣ 2 ^ lab.n - 1 →
      7 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K

@[expose] def Rk2SplitW2TwA : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    lab.tag = .twA → p.Prime → p ≠ 2 → p ∣ 2 ^ lab.n + 1 →
      lab.rank - 2 + CFSG.Open.pRank p (Subgroup.center K) ≤
        CFSG.Open.twoLocalPrimeRank p K

@[expose] def Rk2SplitHTwA : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (r : ℕ), Rk2IsLabel K lab →
    lab.tag = .twA → 2 ≤ lab.n → r.Prime → r ≠ 2 → r ∣ 2 ^ lab.n + 1 →
      CFSG.Open.twoLocalPrimeRank r K ≤ lab.rank - 1

@[expose] def Rk2SplitW3TwD : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    lab.tag = .twD → 4 ≤ lab.rank → p.Prime → p ≠ 2 →
      (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1) →
      lab.rank - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤
        CFSG.Open.twoLocalPrimeRank p K

@[expose] def Rk2SplitW4TwE6Lower : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    lab.tag = .twE6 → 2 ≤ lab.n → p.Prime → p ≠ 2 → p ∣ 2 ^ lab.n + 1 →
      4 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K

@[expose] def Rk2SplitW4TwE6Upper : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (r : ℕ), Rk2IsLabel K lab →
    lab.tag = .twE6 → 2 ≤ lab.n → r.Prime → 5 ≤ r → r ∣ 2 ^ lab.n + 1 →
      CFSG.Open.twoLocalPrimeRank r K ≤ 5

@[expose] def Rk2SplitW4TwE6Five : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    lab.tag = .twE6 → 2 ≤ lab.n → p.Prime → 5 ≤ p → p ∣ 2 ^ lab.n + 1 →
      5 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K

@[expose] def Rk2SplitW5A : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    lab.tag = .A → lab.n = 1 → p = 3 →
      (lab.rank + 1) / 2 + CFSG.Open.pRank p (Subgroup.center K) ≤
        CFSG.Open.twoLocalPrimeRank p K

@[expose] def Rk2SplitW5BCD : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    (lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D) → lab.n = 1 → p = 3 →
      lab.rank - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤
        CFSG.Open.twoLocalPrimeRank p K

@[expose] def Rk2SplitW5E7 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    lab.tag = .E7 → lab.n = 1 → p = 3 →
      6 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K

@[expose] def Rk2SplitW5E8 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    lab.tag = .E8 → lab.n = 1 → p = 3 →
      7 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K

structure Rk2SplitInputs : Prop where
  w1_A : Rk2SplitW1A
  w1_BCD : Rk2SplitW1BCD
  w1_E6 : Rk2SplitW1E6
  w1_E7 : Rk2SplitW1E7
  w1_E8 : Rk2SplitW1E8
  w2_twA : Rk2SplitW2TwA
  h_twA : Rk2SplitHTwA
  w3_twD : Rk2SplitW3TwD
  w4_twE6_lower : Rk2SplitW4TwE6Lower
  w4_twE6_upper : Rk2SplitW4TwE6Upper
  w4_twE6_five : Rk2SplitW4TwE6Five
  w5_A : Rk2SplitW5A
  w5_BCD : Rk2SplitW5BCD
  w5_E7 : Rk2SplitW5E7
  w5_E8 : Rk2SplitW5E8

private theorem upper_of_mult_le {K : Type} [Group K] [Finite K] {lab : GLALabel} {z L M : ℕ}
    (hK : Rk2IsLabel K lab)
    (hM : ∀ r : ℕ, r.Prime → r ≠ 2 → rk2Mult lab (rk2Ord r lab.n) ≤ M)
    (hLM : M + z ≤ L + 1) :
    ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.twoLocalPrimeRank r K + z ≤ L + 1 := by
  intro r hr hr2
  calc CFSG.Open.twoLocalPrimeRank r K + z ≤ rk2Mult lab (rk2Ord r lab.n) + z :=
        Nat.add_le_add_right (twoLocalPrimeRank_le_rk2Mult hK hr hr2) z
    _ ≤ M + z := Nat.add_le_add_right (hM r hr hr2) z
    _ ≤ L + 1 := hLM

private theorem evenRank_le_rank_of_twD {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (ht : lab.tag = .twD) (h1 : 1 ≤ lab.rank) :
    CFSG.Open.evenRank K ≤ lab.rank := by
  rw [CFSG.RankThreeEvenClassification.Helpers.evenRank_eq_sup_twoLocalRanks]
  refine csSup_le' ?_
  rintro k ⟨p, hp, hp2, rfl⟩
  exact (twoLocalPrimeRank_le_rk2Mult hK hp hp2).trans
    (rk2Mult_le_rank (lab := lab) (Or.inr (Or.inr (Or.inr (Or.inr ht)))) h1
      (rk2Ord_pos hp hp2 lab.n))

theorem rk2Split_of_inputs (h : Rk2SplitInputs) : Rk2Split := by
  intro K _ _ lab p hK hp hp2 hsplit he
  have hz : CFSG.Open.pRank p (Subgroup.center K) ≤ 1 :=
    pRank_center_le_one_of_isLabel hK hp hp2
  have hlab : GLAInLambda2 lab := (rk2_model_of_isLabel hK).2.1
  change CFSG.Open.evenRank K + CFSG.Open.pRank p (Subgroup.center K) ≤
    CFSG.Open.twoLocalPrimeRank p K + 1
  rcases lab with ⟨t, ℓ, n⟩
  by_cases hn1 : n = 1
  · subst hn1
    have hp3 : p = 3 := by
      rcases hsplit with ⟨-, hd⟩ | ⟨-, -, -, hd⟩ | ⟨-, hd⟩ | ⟨-, h3⟩
      · exact absurd (Nat.dvd_one.mp (by simpa using hd)) hp.ne_one
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by simpa using hd)
      · exact absurd (Nat.dvd_one.mp (by simpa using hd)) hp.ne_one
      · exact h3
    subst hp3
    simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
    cases t
    ·
      refine evenRank_add_le_of_split (L := (ℓ + 1) / 2 + CFSG.Open.pRank 3 (Subgroup.center K))
        (hL := by simpa using h.w5_A K ⟨.A, ℓ, 1⟩ 3 hK rfl rfl rfl) ?_ he
      refine upper_of_mult_le hK (M := (ℓ + 1) / 2) ?_ (by omega)
      intro r hr hr2
      have hmpos := rk2Ord_pos hr hr2 1
      have hmne1 : rk2Ord r 1 ≠ 1 := rk2Ord_one_ne_one hr
      have hm2 : 2 ≤ rk2Ord r 1 := by omega
      simp only [rk2Mult]
      rw [if_neg hmne1]
      exact Nat.div_le_div_left hm2 (by norm_num)
    ·
      have hℓ3 : 3 ≤ ℓ := by omega
      refine evenRank_add_le_of_split_ne hz (L := ℓ - 2 + CFSG.Open.pRank 3 (Subgroup.center K))
        (hL := by
          simpa using h.w2_twA K ⟨.twA, ℓ, 1⟩ 3 hK rfl Nat.prime_three (by norm_num)
            (by norm_num)) ?_ he
      intro r hr hr2 hr3
      have hm := twoLocalPrimeRank_le_rk2Mult hK hr hr2
      by_cases hd : r ∣ 2 ^ 1 + 1
      · have h3 : r = 3 :=
          (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (by simpa using hd)
        exact absurd h3 hr3
      · have hm2 : rk2Ord r 1 ≠ 2 := by
          intro h2
          exact hd ((rk2Ord_eq_two_iff hr hr2).1 h2)
        have hle := rk2Mult_twA_le_half_of_ne_two (lab := ⟨.twA, ℓ, 1⟩) rfl
          (rk2Ord_pos hr hr2 1) hm2
        have hle' : rk2Mult ⟨.twA, ℓ, 1⟩ (rk2Ord r 1) ≤ (ℓ + 1) / 2 := by
          simpa using hle
        have hm' : CFSG.Open.twoLocalPrimeRank r K ≤ (ℓ + 1) / 2 := hm.trans hle'
        have hdiv : (ℓ + 1) / 2 ≤ ℓ - 1 := by omega
        omega
    ·
      have hℓ2 : 2 ≤ ℓ := by omega
      refine evenRank_add_le_of_split (L := ℓ - 1 + CFSG.Open.pRank 3 (Subgroup.center K))
        (hL := by simpa using h.w5_BCD K ⟨.B, ℓ, 1⟩ 3 hK (Or.inl rfl) rfl rfl) ?_ he
      refine upper_of_mult_le hK (M := ℓ) ?_ (by omega)
      intro r hr hr2
      exact rk2Mult_le_rank (lab := ⟨.B, ℓ, 1⟩) (Or.inr (Or.inl rfl)) (by show 1 ≤ ℓ; omega)
        (rk2Ord_pos hr hr2 1)
    ·
      have hℓ2 : 2 ≤ ℓ := by omega
      refine evenRank_add_le_of_split (L := ℓ - 1 + CFSG.Open.pRank 3 (Subgroup.center K))
        (hL := by simpa using h.w5_BCD K ⟨.C, ℓ, 1⟩ 3 hK (Or.inr (Or.inl rfl)) rfl rfl) ?_ he
      refine upper_of_mult_le hK (M := ℓ) ?_ (by omega)
      intro r hr hr2
      exact rk2Mult_le_rank (lab := ⟨.C, ℓ, 1⟩) (Or.inr (Or.inr (Or.inl rfl))) (by show 1 ≤ ℓ; omega)
        (rk2Ord_pos hr hr2 1)
    ·
      have hℓ3 : 3 ≤ ℓ := by omega
      refine evenRank_add_le_of_split (L := ℓ - 1 + CFSG.Open.pRank 3 (Subgroup.center K))
        (hL := by simpa using h.w5_BCD K ⟨.D, ℓ, 1⟩ 3 hK (Or.inr (Or.inr rfl)) rfl rfl) ?_ he
      refine upper_of_mult_le hK (M := ℓ) ?_ (by omega)
      intro r hr hr2
      exact rk2Mult_le_rank (lab := ⟨.D, ℓ, 1⟩) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by show 1 ≤ ℓ; omega)
        (rk2Ord_pos hr hr2 1)
    ·
      by_cases hℓ4 : 4 ≤ ℓ
      · refine evenRank_add_le_of_split (L := ℓ - 1 + CFSG.Open.pRank 3 (Subgroup.center K))
          (hL := by
            simpa using h.w3_twD K ⟨.twD, ℓ, 1⟩ 3 hK rfl hℓ4 Nat.prime_three (by norm_num)
              (Or.inl (by norm_num))) ?_ he
        refine upper_of_mult_le hK (M := ℓ) ?_ (by omega)
        intro r hr hr2
        exact rk2Mult_le_rank (lab := ⟨.twD, ℓ, 1⟩) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          (by show 1 ≤ ℓ; omega) (rk2Ord_pos hr hr2 1)
      · have hle : CFSG.Open.evenRank K ≤ ℓ :=
          evenRank_le_rank_of_twD hK rfl (by show 1 ≤ ℓ; omega)
        omega
    ·
      exact absurd he (by have := evenRank_le_four_of_E6_one hK rfl rfl; omega)
    ·
      refine evenRank_add_le_of_split (L := 6 + CFSG.Open.pRank 3 (Subgroup.center K))
        (hL := by simpa using h.w5_E7 K ⟨.E7, ℓ, 1⟩ 3 hK rfl rfl rfl) ?_ he
      refine upper_of_mult_le hK (M := 7) ?_ (by omega)
      intro r hr hr2
      exact rk2Mult_E7_le_seven (lab := ⟨.E7, ℓ, 1⟩) rfl (rk2Ord r 1)
    ·
      refine evenRank_add_le_of_split (L := 7 + CFSG.Open.pRank 3 (Subgroup.center K))
        (hL := by simpa using h.w5_E8 K ⟨.E8, ℓ, 1⟩ 3 hK rfl rfl rfl) ?_ he
      refine upper_of_mult_le hK (M := 8) ?_ (by omega)
      intro r hr hr2
      exact rk2Mult_E8_le_eight (lab := ⟨.E8, ℓ, 1⟩) rfl (rk2Ord r 1)
    ·
      exact absurd he (by have := evenRank_le_four_of_F4 hK rfl; omega)
    ·
      refine evenRank_add_le_of_four hz he ?_
      intro r hr hr2 hr3
      have hm2 : rk2Ord r 1 ≠ 2 := by
        intro h2
        exact hr3 ((rk2Ord_one_eq_two_iff hr hr2).1 h2)
      have hm3 : 3 ≤ rk2Ord r 1 := by
        have hp1 := rk2Ord_pos hr hr2 1
        have hn1 := rk2Ord_one_ne_one hr
        omega
      exact (twoLocalPrimeRank_le_rk2Mult hK hr hr2).trans
        (rk2Mult_twE6_le_four_of_ne_two rfl (le_trans (by norm_num) hm3) hm2)
    ·
      exact absurd he (by
        have := evenRank_le_two_of_small hK (Or.inr (Or.inl rfl)); omega)
    ·
      exact absurd he (by
        have := evenRank_le_two_of_small hK (Or.inl rfl); omega)
    ·
      exact absurd he (by
        have := evenRank_le_two_of_small hK (Or.inr (Or.inr (Or.inl rfl))); omega)
    ·
      exact absurd he (by
        have := evenRank_le_two_of_small hK (Or.inr (Or.inr (Or.inr (Or.inl rfl)))); omega)
    ·
      exact absurd he (by
        have := evenRank_le_two_of_small hK
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))); omega)
    ·
      exact absurd he (by
        have := evenRank_le_two_of_small hK
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))); omega)
    ·
      exact absurd he (by
        have := evenRank_le_two_of_small hK
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))); omega)
  · have hnpos : 1 ≤ n := hlab.1
    have hn2 : 2 ≤ n := by omega
    rcases hsplit with ⟨huntw, hdvd⟩ | ⟨huntw, htwB2, htwF4, hdvd⟩ | ⟨htag, hdvd⟩ | ⟨hn, hp3⟩
    ·
      cases t
      all_goals simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
      ·
        refine evenRank_add_le_of_split (L := ℓ - 1 + CFSG.Open.pRank p (Subgroup.center K))
          (hL := by simpa using h.w1_A K ⟨.A, ℓ, n⟩ p hK rfl hp hp2 hdvd) ?_ he
        refine upper_of_mult_le hK (M := ℓ) ?_ (by omega)
        intro r hr hr2
        exact rk2Mult_le_rank (lab := ⟨.A, ℓ, n⟩) (Or.inl rfl) hlab.2.1
          (rk2Ord_pos hr hr2 n)
      ·
        exact huntw.elim
      ·
        refine evenRank_add_le_of_split (L := ℓ - 1 + CFSG.Open.pRank p (Subgroup.center K))
          (hL := by simpa using h.w1_BCD K ⟨.B, ℓ, n⟩ p hK (Or.inl rfl) hp hp2 hdvd) ?_ he
        refine upper_of_mult_le hK (M := ℓ) ?_ (by omega)
        intro r hr hr2
        exact rk2Mult_le_rank (lab := ⟨.B, ℓ, n⟩) (Or.inr (Or.inl rfl)) (by show 1 ≤ ℓ; omega)
          (rk2Ord_pos hr hr2 n)
      ·
        refine evenRank_add_le_of_split (L := ℓ - 1 + CFSG.Open.pRank p (Subgroup.center K))
          (hL := by simpa using h.w1_BCD K ⟨.C, ℓ, n⟩ p hK (Or.inr (Or.inl rfl)) hp hp2 hdvd) ?_ he
        refine upper_of_mult_le hK (M := ℓ) ?_ (by omega)
        intro r hr hr2
        exact rk2Mult_le_rank (lab := ⟨.C, ℓ, n⟩) (Or.inr (Or.inr (Or.inl rfl))) (by show 1 ≤ ℓ; omega)
          (rk2Ord_pos hr hr2 n)
      ·
        refine evenRank_add_le_of_split (L := ℓ - 1 + CFSG.Open.pRank p (Subgroup.center K))
          (hL := by simpa using h.w1_BCD K ⟨.D, ℓ, n⟩ p hK (Or.inr (Or.inr rfl)) hp hp2 hdvd) ?_ he
        refine upper_of_mult_le hK (M := ℓ) ?_ (by omega)
        intro r hr hr2
        exact rk2Mult_le_rank (lab := ⟨.D, ℓ, n⟩) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by show 1 ≤ ℓ; omega)
          (rk2Ord_pos hr hr2 n)
      ·
        exact huntw.elim
      ·
        refine evenRank_add_le_of_split (L := 5 + CFSG.Open.pRank p (Subgroup.center K))
          (hL := by simpa using h.w1_E6 K ⟨.E6, ℓ, n⟩ p hK rfl hp hp2 hdvd) ?_ he
        refine upper_of_mult_le hK (M := 6) ?_ (by omega)
        intro r hr hr2
        exact rk2Mult_E6_le_six (lab := ⟨.E6, ℓ, n⟩) rfl (rk2Ord r n)
      ·
        refine evenRank_add_le_of_split (L := 6 + CFSG.Open.pRank p (Subgroup.center K))
          (hL := by simpa using h.w1_E7 K ⟨.E7, ℓ, n⟩ p hK rfl hp hp2 hdvd) ?_ he
        refine upper_of_mult_le hK (M := 7) ?_ (by omega)
        intro r hr hr2
        exact rk2Mult_E7_le_seven (lab := ⟨.E7, ℓ, n⟩) rfl (rk2Ord r n)
      ·
        refine evenRank_add_le_of_split (L := 7 + CFSG.Open.pRank p (Subgroup.center K))
          (hL := by simpa using h.w1_E8 K ⟨.E8, ℓ, n⟩ p hK rfl hp hp2 hdvd) ?_ he
        refine upper_of_mult_le hK (M := 8) ?_ (by omega)
        intro r hr hr2
        exact rk2Mult_E8_le_eight (lab := ⟨.E8, ℓ, n⟩) rfl (rk2Ord r n)
      ·
        exact absurd he (by have := evenRank_le_four_of_F4 hK rfl; omega)
      ·
        exact huntw.elim
      ·
        exact huntw.elim
      ·
        exact absurd he (by
          have := evenRank_le_two_of_small hK (Or.inl rfl); omega)
      ·
        exact huntw.elim
      ·
        exact huntw.elim
      ·
        exact absurd he (by
          have := evenRank_le_two_of_small hK
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))); omega)
      ·
        exact absurd he (by
          have := evenRank_le_two_of_small hK
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))); omega)
      ·
        exact huntw.elim
    ·
      cases t
      all_goals simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
      ·
        exact (huntw trivial).elim
      ·
        have hℓ2 : 2 ≤ ℓ := by omega
        refine evenRank_add_le_of_split (L := ℓ - 2 + CFSG.Open.pRank p (Subgroup.center K))
          (hL := by simpa using h.w2_twA K ⟨.twA, ℓ, n⟩ p hK rfl hp hp2 hdvd) ?_ he
        intro r hr hr2
        have hm := twoLocalPrimeRank_le_rk2Mult hK hr hr2
        by_cases hd : r ∣ 2 ^ n + 1
        · have hle : CFSG.Open.twoLocalPrimeRank r K ≤ ℓ - 1 := by
            have h' := h.h_twA K ⟨.twA, ℓ, n⟩ r hK rfl hn2 hr hr2 hd
            dsimp only at h'
            exact h'
          omega
        · have hm2 : rk2Ord r n ≠ 2 := by
            intro h2
            exact hd ((rk2Ord_eq_two_iff hr hr2).1 h2)
          have hle := rk2Mult_twA_le_half_of_ne_two (lab := ⟨.twA, ℓ, n⟩) rfl
            (rk2Ord_pos hr hr2 n) hm2
          have hle' : rk2Mult ⟨.twA, ℓ, n⟩ (rk2Ord r n) ≤ (ℓ + 1) / 2 := by
            dsimp only at hle
            exact hle
          have hm' : CFSG.Open.twoLocalPrimeRank r K ≤ (ℓ + 1) / 2 := hm.trans hle'
          have hdiv : (ℓ + 1) / 2 ≤ ℓ - 1 := by omega
          omega
      ·
        exact (huntw trivial).elim
      ·
        exact (huntw trivial).elim
      ·
        exact (huntw trivial).elim
      ·
        by_cases hℓ4 : 4 ≤ ℓ
        · refine evenRank_add_le_of_split (L := ℓ - 1 + CFSG.Open.pRank p (Subgroup.center K))
            (hL := by
              simpa using h.w3_twD K ⟨.twD, ℓ, n⟩ p hK rfl hℓ4 hp hp2 (Or.inl hdvd)) ?_ he
          refine upper_of_mult_le hK (M := ℓ) ?_ (by omega)
          intro r hr hr2
          exact rk2Mult_le_rank (lab := ⟨.twD, ℓ, n⟩) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
            (by show 1 ≤ ℓ; omega) (rk2Ord_pos hr hr2 n)
        · have hle : CFSG.Open.evenRank K ≤ ℓ :=
            evenRank_le_rank_of_twD hK rfl (by show 1 ≤ ℓ; omega)
          omega
      ·
        exact (huntw trivial).elim
      ·
        exact (huntw trivial).elim
      ·
        exact (huntw trivial).elim
      ·
        exact (huntw trivial).elim
      ·
        by_cases hp5 : 5 ≤ p
        · refine evenRank_add_le_of_split (L := 5 + CFSG.Open.pRank p (Subgroup.center K))
            (hL := by
              simpa using h.w4_twE6_five K ⟨.twE6, ℓ, n⟩ p hK rfl hn2 hp hp5 hdvd) ?_ he
          refine upper_of_mult_le hK (M := 6) ?_ (by omega)
          intro r hr hr2
          exact rk2Mult_twE6_le_six (lab := ⟨.twE6, ℓ, n⟩) rfl (rk2Ord r n)
        · have hp3 : p = 3 := by
            have h2 : 2 ≤ p := hp.two_le
            have h5 : p < 5 := by omega
            interval_cases p
            · exact absurd rfl hp2
            · rfl
            · exact absurd hp (by norm_num)
          subst hp3
          refine evenRank_add_le_of_split_ne hz (L := 4 + CFSG.Open.pRank 3 (Subgroup.center K))
            (hL := by
              simpa using h.w4_twE6_lower K ⟨.twE6, ℓ, n⟩ 3 hK rfl hn2 Nat.prime_three
                (by norm_num) hdvd) ?_ he
          intro r hr hr2 hr3
          have hm := twoLocalPrimeRank_le_rk2Mult hK hr hr2
          by_cases hd : r ∣ 2 ^ n + 1
          · have hr5 : 5 ≤ r := by
              by_contra h5
              have h2 : 2 ≤ r := hr.two_le
              have h5' : r < 5 := by omega
              interval_cases r
              · exact hr2 rfl
              · exact hr3 rfl
              · exact absurd hr (by norm_num)
            have hle : CFSG.Open.twoLocalPrimeRank r K ≤ 5 :=
              h.w4_twE6_upper K ⟨.twE6, ℓ, n⟩ r hK rfl hn2 hr hr5 hd
            omega
          · have hm2 : rk2Ord r n ≠ 2 := by
              intro h2
              exact hd ((rk2Ord_eq_two_iff hr hr2).1 h2)
            have hle := rk2Mult_twE6_le_four_of_ne_two (lab := ⟨.twE6, ℓ, n⟩) rfl
              (rk2Ord_pos hr hr2 n) hm2
            have hle' : rk2Mult ⟨.twE6, ℓ, n⟩ (rk2Ord r n) ≤ 4 := by simpa using hle
            have hm' : CFSG.Open.twoLocalPrimeRank r K ≤ 4 := hm.trans hle'
            omega
      ·
        exact absurd he (by
          have := evenRank_le_two_of_small hK (Or.inr (Or.inl rfl)); omega)
      ·
        exact (huntw trivial).elim
      ·
        exact absurd he (by
          have := evenRank_le_two_of_small hK (Or.inr (Or.inr (Or.inl rfl))); omega)
      ·
        exact absurd he (by
          have := evenRank_le_two_of_small hK (Or.inr (Or.inr (Or.inr (Or.inl rfl)))); omega)
      ·
        exact (huntw trivial).elim
      ·
        exact (huntw trivial).elim
      ·
        exact absurd he (by
          have := evenRank_le_two_of_small hK
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))); omega)
    ·
      cases t
      all_goals simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
      ·
        by_cases hℓ4 : 4 ≤ ℓ
        · refine evenRank_add_le_of_split (L := ℓ - 1 + CFSG.Open.pRank p (Subgroup.center K))
            (hL := by
              simpa using h.w3_twD K ⟨.twD, ℓ, n⟩ p hK rfl hℓ4 hp hp2 (Or.inr hdvd)) ?_ he
          refine upper_of_mult_le hK (M := ℓ) ?_ (by omega)
          intro r hr hr2
          exact rk2Mult_le_rank (lab := ⟨.twD, ℓ, n⟩) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
            (by show 1 ≤ ℓ; omega) (rk2Ord_pos hr hr2 n)
        · have hle : CFSG.Open.evenRank K ≤ ℓ :=
            evenRank_le_rank_of_twD hK rfl (by show 1 ≤ ℓ; omega)
          omega
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
      ·
        exact absurd he (by
          have := evenRank_le_two_of_small hK (Or.inr (Or.inl rfl)); omega)
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
      ·
        exact absurd he (by
          have := evenRank_le_two_of_small hK (Or.inr (Or.inr (Or.inl rfl))); omega)
      ·
        exact absurd he (by
          have := evenRank_le_two_of_small hK (Or.inr (Or.inr (Or.inr (Or.inl rfl)))); omega)
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
      ·
        exfalso
        rcases htag with h | h | h | h <;> simp_all
    ·
      exact absurd hn hn1

end CFSG.LocalAnalysis.GLTheoremA

end
