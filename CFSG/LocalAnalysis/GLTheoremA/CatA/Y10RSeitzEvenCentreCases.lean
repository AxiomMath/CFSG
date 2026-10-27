module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Arith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Arith2
public import CFSG.RankThree.PartOne.S11d.OddCenterGriess
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.StandardType CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank

theorem even_exceptionalOrders_label_cases {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (h : 2 ∣ (exceptionalOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).1 *
      (exceptionalOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).2) :
    lab = ⟨.A, 1, 2⟩ ∨ lab = ⟨.A, 2, 1⟩ ∨ lab = ⟨.A, 2, 2⟩ ∨ lab = ⟨.A, 3, 1⟩ ∨
    lab = ⟨.D, 3, 1⟩ ∨ lab = ⟨.twD, 2, 1⟩ ∨ lab = ⟨.twD, 3, 1⟩ ∨ lab = ⟨.twA, 3, 1⟩ ∨
    lab = ⟨.B, 3, 1⟩ ∨ lab = ⟨.C, 3, 1⟩ ∨ lab = ⟨.G2, 0, 2⟩ ∨ lab = ⟨.twB2, 0, 3⟩ ∨
    lab = ⟨.D, 4, 1⟩ ∨ lab = ⟨.F4, 0, 1⟩ ∨ lab = ⟨.twA, 5, 1⟩ ∨ lab = ⟨.twE6, 0, 1⟩ := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals
    simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
    rcases hlab with ⟨hn, hcond⟩
    simp only [markTag, markRank, markChar, markDeg] at h ⊢
    unfold exceptionalOrders at h
    split at h <;> simp_all
  all_goals try split_ifs at *
  all_goals try omega
  all_goals tauto

private theorem rk2Cnt_F4_le_two_of_lt {m : ℕ} (hm : m < 25) (hm3 : 3 ≤ m) :
    rk2Cnt [(2, true), (6, true), (8, true), (12, true)] m ≤ 2 := by
  interval_cases m <;> decide

private theorem rk2Cnt_twE6_le_three_of_lt {m : ℕ} (hm : m < 25) (hm3 : 3 ≤ m) :
    rk2Cnt [(2, true), (5, false), (6, true), (8, true), (9, false), (12, true)] m ≤ 3 := by
  interval_cases m <;> decide

private theorem rk2Cnt_F4_le_two {m : ℕ} (hm : 3 ≤ m) :
    rk2Cnt [(2, true), (6, true), (8, true), (12, true)] m ≤ 2 := by
  by_cases h : m < 25
  · exact rk2Cnt_F4_le_two_of_lt h hm
  · have h0 := rk2Cnt_large [(2, true), (6, true), (8, true), (12, true)] 24
      (by intro f hf; simp at hf; rcases hf with rfl | rfl | rfl | rfl <;> norm_num)
      (m := m) (by omega)
    omega

private theorem rk2Cnt_twE6_le_three {m : ℕ} (hm : 3 ≤ m) :
    rk2Cnt [(2, true), (5, false), (6, true), (8, true), (9, false), (12, true)] m ≤ 3 := by
  by_cases h : m < 25
  · exact rk2Cnt_twE6_le_three_of_lt h hm
  · have h0 := rk2Cnt_large [(2, true), (5, false), (6, true), (8, true), (9, false), (12, true)]
      24 (by intro f hf; simp at hf; rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
      (m := m) (by omega)
    omega

private theorem rk2Mult_le_three_or_four {lab : GLALabel} {m : ℕ} (hm : 0 < m)
    (h : lab = ⟨.A, 1, 2⟩ ∨ lab = ⟨.A, 2, 1⟩ ∨ lab = ⟨.A, 2, 2⟩ ∨ lab = ⟨.A, 3, 1⟩ ∨
      lab = ⟨.D, 3, 1⟩ ∨ lab = ⟨.twD, 2, 1⟩ ∨ lab = ⟨.twD, 3, 1⟩ ∨ lab = ⟨.twA, 3, 1⟩ ∨
      lab = ⟨.B, 3, 1⟩ ∨ lab = ⟨.C, 3, 1⟩ ∨ lab = ⟨.G2, 0, 2⟩ ∨ lab = ⟨.twB2, 0, 3⟩ ∨
      lab = ⟨.D, 4, 1⟩ ∨ lab = ⟨.F4, 0, 1⟩ ∨ lab = ⟨.twA, 5, 1⟩ ∨ lab = ⟨.twE6, 0, 1⟩) :
    rk2Mult lab m ≤ 3 ∨ lab = ⟨.D, 4, 1⟩ ∨ lab = ⟨.F4, 0, 1⟩ ∨ lab = ⟨.twA, 5, 1⟩ ∨
      lab = ⟨.twE6, 0, 1⟩ := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    by_cases h2 : m ≤ 2
    · interval_cases m <;> decide
    · have hm3 : 3 ≤ m := by omega
      simp only [rk2Mult]
      split_ifs with hm1
      · norm_num
      · change 2 / m ≤ 3
        exact le_trans (Nat.div_le_self _ _) (by norm_num)
  · left
    by_cases h2 : m ≤ 2
    · interval_cases m <;> decide
    · have hm3 : 3 ≤ m := by omega
      simp only [rk2Mult]
      split_ifs with hm1
      · norm_num
      · change 3 / m ≤ 3
        exact Nat.div_le_self _ _
  · left
    by_cases h2 : m ≤ 2
    · interval_cases m <;> decide
    · have hm3 : 3 ≤ m := by omega
      simp only [rk2Mult]
      split_ifs with hm1
      · norm_num
      · change 3 / m ≤ 3
        exact Nat.div_le_self _ _
  · left
    by_cases h2 : m ≤ 2
    · interval_cases m <;> decide
    · have hm3 : 3 ≤ m := by omega
      simp only [rk2Mult]
      split_ifs with hm1
      · norm_num
      · change 4 / m ≤ 3
        rw [Nat.div_le_iff_le_mul]
        · omega
        · omega
  · left
    by_cases h2 : m ≤ 2
    · interval_cases m <;> decide
    · have hm3 : 3 ≤ m := by omega
      have hle := rk2Mult_bcd_le (lab := ⟨.D, 3, 1⟩) (Or.inr (Or.inr (Or.inl rfl))) hm3
      norm_num at hle
      omega
  · left
    by_cases h2 : m ≤ 2
    · interval_cases m <;> decide
    · have hm3 : 3 ≤ m := by omega
      have hle := rk2Mult_bcd_le (lab := ⟨.twD, 2, 1⟩) (Or.inr (Or.inr (Or.inr rfl))) hm3
      norm_num at hle
      omega
  · left
    by_cases h2 : m ≤ 2
    · interval_cases m <;> decide
    · have hm3 : 3 ≤ m := by omega
      have hle := rk2Mult_bcd_le (lab := ⟨.twD, 3, 1⟩) (Or.inr (Or.inr (Or.inr rfl))) hm3
      norm_num at hle
      omega
  · left
    by_cases h2 : m ≤ 2
    · interval_cases m <;> decide
    · have hm3 : 3 ≤ m := by omega
      have hle := rk2Mult_twA_le (lab := ⟨.twA, 3, 1⟩) rfl hm3
      norm_num at hle
      omega
  · left
    by_cases h2 : m ≤ 2
    · interval_cases m <;> decide
    · have hm3 : 3 ≤ m := by omega
      have hle := rk2Mult_bcd_le (lab := ⟨.B, 3, 1⟩) (Or.inl rfl) hm3
      norm_num at hle
      omega
  · left
    by_cases h2 : m ≤ 2
    · interval_cases m <;> decide
    · have hm3 : 3 ≤ m := by omega
      have hle := rk2Mult_bcd_le (lab := ⟨.C, 3, 1⟩) (Or.inr (Or.inl rfl)) hm3
      norm_num at hle
      omega
  · exact Or.inl (le_trans (rk2Mult_le_two_of_small (lab := ⟨.G2, 0, 2⟩) (Or.inl rfl) hm)
      (by norm_num))
  · exact Or.inl (le_trans (rk2Mult_le_two_of_small (lab := ⟨.twB2, 0, 3⟩)
      (Or.inr (Or.inr (Or.inl rfl))) hm) (by norm_num))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

private theorem rk2Mult_D4_ge_four {m : ℕ} (h : 4 ≤ rk2Mult ⟨.D, 4, 1⟩ m) : m ≤ 2 := by
  by_contra hm
  have hm3 : 3 ≤ m := by omega
  have hle := rk2Mult_bcd_le (lab := ⟨.D, 4, 1⟩) (Or.inr (Or.inr (Or.inl rfl))) hm3
  norm_num at hle
  omega

private theorem rk2Mult_F4_ge_four {m : ℕ} (h : 4 ≤ rk2Mult ⟨.F4, 0, 1⟩ m) : m ≤ 2 := by
  by_contra hm
  have hm3 : 3 ≤ m := by omega
  have hle : rk2Mult ⟨.F4, 0, 1⟩ m ≤ 2 := by
    simpa [rk2Mult] using rk2Cnt_F4_le_two hm3
  omega

private theorem rk2Mult_twA5_ge_four {m : ℕ} (hm : 0 < m) (h : 4 ≤ rk2Mult ⟨.twA, 5, 1⟩ m) :
    m = 2 := by
  by_cases hm1 : m = 1
  · rw [hm1] at h
    simp only [rk2Mult] at h
    norm_num at h
  · by_cases hm2 : m = 2
    · exact hm2
    · have hm3 : 3 ≤ m := by
        by_contra h3
        interval_cases m <;> simp_all
      have hle := rk2Mult_twA_le (lab := ⟨.twA, 5, 1⟩) rfl hm3
      have hle' : rk2Mult ⟨.twA, 5, 1⟩ m ≤ 2 := by simpa using hle
      omega

private theorem rk2Mult_twE6_ge_four {m : ℕ} (h : 4 ≤ rk2Mult ⟨.twE6, 0, 1⟩ m) : m ≤ 2 := by
  by_contra hm
  have hm3 : 3 ≤ m := by omega
  have hle : rk2Mult ⟨.twE6, 0, 1⟩ m ≤ 3 := by
    simpa [rk2Mult] using rk2Cnt_twE6_le_three hm3
  omega


theorem seitzEvenCentre_cases {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hZ : Even (Nat.card (Subgroup.center K))) (h4 : 4 ≤ rk2Mult lab (rk2Ord q lab.n)) :
    q = 3 ∧ (lab = ⟨.D, 4, 1⟩ ∨ lab = ⟨.F4, 0, 1⟩ ∨ lab = ⟨.twA, 5, 1⟩ ∨ lab = ⟨.twE6, 0, 1⟩) := by
  have hQ : CFSG.Open.IsQuasisimple K := hasLabel_isQuasisimple hK
  obtain ⟨lab', hlab', R, _, I, F, θ, hs, _, hP, hM⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists_markedModel hK
  have hlab_eq : lab' = lab := hP
  subst lab'
  have hM' : MarkedModel lab (K ⧸ Subgroup.center K) := MarkedModel.of_mulEquiv θ.symm hM
  have hmpos : 0 < rk2Ord q lab.n := rk2Ord_pos hq hq2 lab.n
  by_cases hder : lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der
  · have hle : rk2Mult lab (rk2Ord q lab.n) ≤ 2 :=
      CFSG.LocalAnalysis.GLTheoremA.rk2Mult_le_two_of_small
        (Or.inr (Or.inr (Or.inr (Or.inr hder)))) hmpos
    omega
  · have hchar : markChar lab = 2 := by
      obtain ⟨t, l, n⟩ := lab
      cases t <;> simp_all [markChar]
    have hM2 : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) (markTag lab) (markRank lab) 2
        (markDeg lab) := by
      simpa only [MarkedModel, hchar] using hM'
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
      (K ⧸ Subgroup.center K) (markTag lab) (markRank lab) 2 (markDeg lab) hM2
    have hcard : Nat.card (griessHopfMultiplier (K ⧸ Subgroup.center K)) =
        ((genericOrders (markTag lab) (markRank lab) 2 (markDeg lab)).1 *
          (genericOrders (markTag lab) (markRank lab) 2 (markDeg lab)).2) *
        ((exceptionalOrders (markTag lab) (markRank lab) 2 (markDeg lab)).1 *
          (exceptionalOrders (markTag lab) (markRank lab) 2 (markDeg lab)).2) := by
      rw [Nat.card_congr eM.toEquiv,
        CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional']
    have hgodd : ¬ 2 ∣ (genericOrders (markTag lab) (markRank lab) 2 (markDeg lab)).1 *
        (genericOrders (markTag lab) (markRank lab) 2 (markDeg lab)).2 := by
      refine CFSG.RankThree.PartOne.FieldFix.genericOrders_odd _ _ _ hM2.admissible.2.1 ?_ ?_
      · intro ht
        have hadm := hM2.admissible.2.2
        rw [ht] at hadm
        omega
      · obtain ⟨t, r, n⟩ := lab
        cases t <;> simp only [markTag] <;> first | decide | (split_ifs <;> decide)
    have hgpos : 0 < (genericOrders (markTag lab) (markRank lab) 2 (markDeg lab)).1 *
        (genericOrders (markTag lab) (markRank lab) 2 (markDeg lab)).2 :=
      Nat.pos_of_ne_zero fun h => hgodd (h ▸ dvd_zero 2)
    have hepos : 0 < (exceptionalOrders (markTag lab) (markRank lab) 2 (markDeg lab)).1 *
        (exceptionalOrders (markTag lab) (markRank lab) 2 (markDeg lab)).2 := by
      unfold exceptionalOrders
      split <;> norm_num
    haveI : Finite (griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    have hQ' : CFSG.IsQuasisimple K :=
      (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
    have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ'
      (MulEquiv.refl (K ⧸ Subgroup.center K))
    rw [hcard] at hdvd
    have h2dvd : 2 ∣ (exceptionalOrders (markTag lab) (markRank lab) 2 (markDeg lab)).1 *
        (exceptionalOrders (markTag lab) (markRank lab) 2 (markDeg lab)).2 := by
      have h2Z : 2 ∣ Nat.card (Subgroup.center K) := even_iff_two_dvd.1 hZ
      rcases (Nat.Prime.dvd_mul Nat.prime_two).1 (h2Z.trans hdvd) with h | h
      · exact absurd h hgodd
      · exact h
    have h2dvd' : 2 ∣ (exceptionalOrders (markTag lab) (markRank lab) (markChar lab)
        (markDeg lab)).1 * (exceptionalOrders (markTag lab) (markRank lab) (markChar lab)
        (markDeg lab)).2 := by
      simpa only [hchar] using h2dvd
    have h16 := even_exceptionalOrders_label_cases hlab' h2dvd'
    rcases rk2Mult_le_three_or_four hmpos h16 with hle | hfour
    · omega
    · have hm2 : rk2Ord q lab.n = 2 := by
        rcases hfour with rfl | rfl | rfl | rfl
        · have hmle := rk2Mult_D4_ge_four (m := rk2Ord q (⟨.D, 4, 1⟩ : GLALabel).n) h4
          have hmne : rk2Ord q (⟨.D, 4, 1⟩ : GLALabel).n ≠ 1 := rk2Ord_one_ne_one hq
          have hpos := rk2Ord_pos hq hq2 (⟨.D, 4, 1⟩ : GLALabel).n
          omega
        · have hmle := rk2Mult_F4_ge_four (m := rk2Ord q (⟨.F4, 0, 1⟩ : GLALabel).n) h4
          have hmne : rk2Ord q (⟨.F4, 0, 1⟩ : GLALabel).n ≠ 1 := rk2Ord_one_ne_one hq
          have hpos := rk2Ord_pos hq hq2 (⟨.F4, 0, 1⟩ : GLALabel).n
          omega
        · exact rk2Mult_twA5_ge_four (m := rk2Ord q (⟨.twA, 5, 1⟩ : GLALabel).n)
            (rk2Ord_pos hq hq2 _) h4
        · have hmle := rk2Mult_twE6_ge_four (m := rk2Ord q (⟨.twE6, 0, 1⟩ : GLALabel).n) h4
          have hmne : rk2Ord q (⟨.twE6, 0, 1⟩ : GLALabel).n ≠ 1 := rk2Ord_one_ne_one hq
          have hpos := rk2Ord_pos hq hq2 (⟨.twE6, 0, 1⟩ : GLALabel).n
          omega
      have hq3 : q = 3 := by
        have h1 : rk2Ord q 1 = 2 := by
          rcases hfour with rfl | rfl | rfl | rfl <;> simpa using hm2
        exact (rk2Ord_one_eq_two_iff hq hq2).1 h1
      exact ⟨hq3, hfour⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F
