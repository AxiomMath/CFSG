module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLiePSL
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCArith
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevLin
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevToral

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSL StatedScalars)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.RankThreeUC.S15

section Formula

variable {F : Type} [Field F] [Finite F] {p n : ℕ}

theorem pRank_statedProj_SL_formula (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (hpF : ¬ p ∣ Nat.card F) (hdiv : ¬ p ∣ Nat.gcd n (Nat.card F - 1)) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n F))) =
      if p ∣ Nat.card F - 1 then n - 1 else n / orderOf (Nat.card F : ZMod p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
  have hZ : ¬ p ∣ Nat.card ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) :=
    RankChevLinProof.not_dvd_card_scalars_statedSL hn (by rwa [hc])
  refine (CFSG.SectionRank.pRank_quotient_eq _ hZ).trans ?_
  split_ifs with h
  · exact pRank_top_statedSL_eq_pred hn (OFRC.natCast_ne_zero_of_not_dvd_card hp hpF) h
  · have := pRank_statedSL_of_not_dvd hp hp2 (by rwa [hc]) (by rwa [hc]) n
    rwa [hc] at this

end Formula

theorem pRank_statedProj_SL_eq_of_pow {F F₀ : Type} [Field F] [Field F₀] [Finite F] [Finite F₀]
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (hcard : Nat.card F = Nat.card F₀ ^ p)
    (hpF : ¬ p ∣ Nat.card F) (hdiv : ¬ p ∣ Nat.gcd n (Nat.card F - 1)) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n F))) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n F₀))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hF₀ : ¬ p ∣ Nat.card F₀ := fun h => hpF (hcard ▸ h.trans (dvd_pow_self _ hp.ne_zero))
  have hq₀ : 1 ≤ Nat.card F₀ := Nat.card_pos
  have hiff : p ∣ Nat.card F - 1 ↔ p ∣ Nat.card F₀ - 1 := by
    rw [hcard]
    exact OFRC.dvd_pow_prime_sub_one_iff hq₀
  have hdiv₀ : ¬ p ∣ Nat.gcd n (Nat.card F₀ - 1) := fun h =>
    hdiv (Nat.dvd_gcd (h.trans (Nat.gcd_dvd_left _ _))
      (hiff.2 (h.trans (Nat.gcd_dvd_right _ _))))
  rw [pRank_statedProj_SL_formula hp hp2 hn hpF hdiv,
    pRank_statedProj_SL_formula hp hp2 hn hF₀ hdiv₀, if_congr hiff rfl rfl, hcard,
    OFRC.orderOf_natCast_pow_prime]

theorem outerFixedRankCrossAt_PSL : OuterFixedRankCrossAt .PSL := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ hdivL α hαp hαin hrk
  have hcl : StatedClassicalModel K .PSL n ℓ f :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  have hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f - 1) := hdivL
  obtain ⟨⟨hℓp, hf, hn2, -, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have hcl' : StatedClassicalModel K .PSL n ℓ f :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨hpf, F₀, hF₀, hF₀fin, hcard, hrank⟩ : p ∣ f ∧ ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀),
      Nat.card F₀ = ℓ ^ (f / p) ∧ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n F₀))) ≤
        CFSG.Open.pRank p (fixedSubgroup α) := by
    by_cases hn3 : 3 ≤ n
    · exact psl_three_pRank_fixed hn3 hcl' hp (by omega) hdiv α hαp hαin
    · obtain rfl : n = 2 := by omega
      exact psl_two_pRank_fixed hcl' hp (by omega) α hαp hαin
  have hFcard' : Nat.card F = Nat.card F₀ ^ p := by
    rw [hFcard, hcard, ← pow_mul, Nat.div_mul_cancel hpf]
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hFcard]
    exact OFRC.not_dvd_pow_of_ne hp hℓp hℓ
  have hdivF : ¬ p ∣ Nat.gcd n (Nat.card F - 1) := by
    rw [hFcard]
    exact hdiv
  have hK : CFSG.Open.pRank p (⊤ : Subgroup K) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n F))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  have heq := pRank_statedProj_SL_eq_of_pow hp (by omega) (by omega) hFcard' hpF hdivF
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
