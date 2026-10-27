module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLiePSU
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCArith
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevUni
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevToral

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSU StatedScalars)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.RankThreeUC.S15

theorem pRank_statedProj_SU_formula {F : Type} [Field F] [Finite F] {p ℓ n q : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hℓ : ℓ.Prime) (hqℓ : ∃ f, q = ℓ ^ f) (hn : 1 ≤ n)
    (hF : Nat.card F = q ^ 2) (hpq : ¬ p ∣ q) (hdiv : ¬ p ∣ Nat.gcd n (q + 1)) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU n q F))) =
      if p ∣ q + 1 then n - 1 else n / orderOf (-(q : ZMod p)) := by
  classical
  obtain ⟨f, rfl⟩ := hqℓ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
  have hZ : ¬ p ∣ Nat.card ((StatedScalars (Fin n) F).subgroupOf (StatedSU n (ℓ ^ f) F)) := by
    intro h
    obtain ⟨h1, h2⟩ := RankChevUniProof.card_scalars_statedSU_dvd hℓ hF hn
    exact hdiv (Nat.dvd_gcd (h.trans h1) (h.trans h2))
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hF]
    exact fun h => hpq (hp.dvd_of_dvd_pow h)
  refine (CFSG.SectionRank.pRank_quotient_eq _ hZ).trans ?_
  split_ifs with h
  · exact pRank_top_statedSU_eq_pred hn (OFRC.natCast_ne_zero_of_not_dvd_card hp hpF) hF h
  · exact pRank_statedSU_of_not_dvd hp hp2 (by rwa [hc]) hpq h n hn

theorem pRank_statedProj_SU_eq_of_pow {F F₀ : Type} [Field F] [Field F₀] [Finite F] [Finite F₀]
    {p ℓ n q q₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ.Prime) (hqℓ : ∃ f, q = ℓ ^ f)
    (hq₀ℓ : ∃ f, q₀ = ℓ ^ f) (hn : 1 ≤ n) (hF : Nat.card F = q ^ 2) (hF₀ : Nat.card F₀ = q₀ ^ 2)
    (hq : q = q₀ ^ p) (hpq : ¬ p ∣ q) (hdiv : ¬ p ∣ Nat.gcd n (q + 1)) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU n q F))) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU n q₀ F₀))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq₀ : ¬ p ∣ q₀ := fun h => hpq (hq ▸ h.trans (dvd_pow_self _ hp.ne_zero))
  have hiff : p ∣ q + 1 ↔ p ∣ q₀ + 1 := by
    rw [hq]
    exact OFRC.dvd_pow_prime_add_one_iff
  have hdiv₀ : ¬ p ∣ Nat.gcd n (q₀ + 1) := fun h =>
    hdiv (Nat.dvd_gcd (h.trans (Nat.gcd_dvd_left _ _)) (hiff.2 (h.trans (Nat.gcd_dvd_right _ _))))
  rw [pRank_statedProj_SU_formula hp hp2 hℓ hqℓ hn hF hpq hdiv,
    pRank_statedProj_SU_formula hp hp2 hℓ hq₀ℓ hn hF₀ hpq₀ hdiv₀, if_congr hiff rfl rfl, hq,
    OFRC.orderOf_neg_natCast_pow_prime]

theorem outerFixedRankCrossAt_PSU : OuterFixedRankCrossAt .PSU := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ hdivL α hαp hαin hrk
  have hcl : StatedClassicalModel K .PSU n ℓ f :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  have hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1) := hdivL
  have hcl' := hcl
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hℓp, hf, hn3, hne⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have hpq : ¬ p ∣ ℓ ^ f := OFRC.not_dvd_pow_of_ne hp hℓp hℓ
  have hK : CFSG.Open.pRank p (⊤ : Subgroup K) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU n (ℓ ^ f) F))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  have hpf : p ∣ f := by
    rcases HardMathSupport.Lang.Coordinator.outerFixedOrderBoundAt_PSU K n ℓ f hadm hmodel hT p
      hp (by omega) hdivL (fun h => by simp at h) α hαp hαin with ⟨f₀, hf₀, -⟩ | ⟨h, -⟩
    · exact ⟨f₀, hf₀⟩
    · exact absurd h (by simp)
  have hq₀ : ¬(n = 3 ∧ ℓ ^ (f / p) = 2) := by
    rintro ⟨rfl, h2⟩
    have hq : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by rw [← pow_mul, Nat.div_mul_cancel hpf]
    have hnot : ¬ p ∣ ℓ ^ f + 1 := by
      rw [hq, OFRC.dvd_pow_prime_add_one_iff, h2]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    have hform := pRank_statedProj_SU_formula (F := F) hp (by omega) hℓp ⟨f, rfl⟩ (by omega)
      hFcard hpq hdiv
    rw [if_neg hnot] at hform
    have hz : -((ℓ ^ f : ℕ) : ZMod p) ≠ 1 := fun h1 => hnot ((OFRC.dvd_add_one_iff_neg_eq_one _).2 h1)
    have h3 : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU 3 (ℓ ^ f) F))) ≤ 1 := by
      rw [hform]
      exact OFRC.three_div_orderOf_le_one _ hz
    omega
  obtain ⟨hpf, F₀, hF₀, hF₀fin, hcard, hrank⟩ :=
    psu_pRank_fixed hcl' hp (by omega) hdiv hq₀ α hαp hαin
  have hq : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by rw [← pow_mul, Nat.div_mul_cancel hpf]
  have heq := pRank_statedProj_SU_eq_of_pow (F := F) (F₀ := F₀) hp (by omega) hℓp ⟨f, rfl⟩
    ⟨f / p, rfl⟩ (by omega) hFcard hcard hq hpq hdiv
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
