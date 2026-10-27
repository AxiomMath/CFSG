module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.CoverSplit
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.LinCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open CFSG.HardMathSupport.Timmesfeld.LinearRank

theorem not_dvd_exceptional_of_dvd_generic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {t : StatedLieTag} {n r f : ℕ} (h : p ∣ (genericOrders t n r f).1) :
    ¬ p ∣ (exceptionalOrders t n r f).1 ∧ ¬ p ∣ (exceptionalOrders t n r f).2 := by
  have hle := Multiplier.exceptionalOrders_le t n r f
  have key : ∀ a : ℕ, 0 < a → a ≤ 4 → p ∣ a → p = 3 := by
    intro a ha0 ha4 hpa
    have hpa' := Nat.le_of_dvd ha0 hpa
    have h2 := hp.two_le
    have hp4 : p ≤ 4 := hpa'.trans ha4
    interval_cases p
    · exact absurd rfl hp2
    · rfl
    · exact absurd hp (by norm_num)
  constructor
  · intro hd
    have := key _ hle.1.1 hle.1.2 hd
    subst this
    exact (Multiplier.not_three_dvd_exceptional_of_dvd_generic h).1 hd
  · intro hd
    have := key _ hle.2.1 hle.2.2 hd
    subst this
    exact (Multiplier.not_three_dvd_exceptional_of_dvd_generic h).2 hd

theorem classical_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n r f : ℕ}
    (hm : CFSG.Blueprint.LieModel X t n r f) (ht : t = .PSL ∨ t = .PSU) :
    StatedClassicalModel X t n r f :=
  CFSG.Blueprint.LieModel.statedClassicalModel hm (by rcases ht with rfl | rfl <;> decide)

theorem factorization_card_table {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : StatedLieTag}
    {n r f : ℕ} (hadm : StatedLieAdmissible t n r f) (ht : t = .PSL ∨ t = .PSU)
    (ha : p ∣ (genericOrders t n r f).1) :
    ((genericOrders t n r f).1 * (genericOrders t n r f).2 *
      ((exceptionalOrders t n r f).1 * (exceptionalOrders t n r f).2)).factorization p ≤
      (genericOrders t n r f).1.factorization p := by
  have hb : (genericOrders t n r f).2 = 1 := by rcases ht with rfl | rfl <;> rfl
  have h1 : (genericOrders t n r f).1 ≠ 0 :=
    (Multiplier.genericOrders_fst_pos hadm).ne'
  obtain ⟨hc, hd⟩ := not_dvd_exceptional_of_dvd_generic hp hp2 ha
  have h3 : (exceptionalOrders t n r f).1 ≠ 0 :=
    (Multiplier.exceptionalOrders_le t n r f).1.1.ne'
  have h4 : (exceptionalOrders t n r f).2 ≠ 0 :=
    (Multiplier.exceptionalOrders_le t n r f).2.1.ne'
  rw [hb, mul_one, Nat.factorization_mul (by omega) (mul_ne_zero h3 h4),
    Nat.factorization_mul h3 h4]
  simp [Nat.factorization_eq_zero_of_not_dvd hc, Nat.factorization_eq_zero_of_not_dvd hd]

theorem lieCoverRankHighLin_aux (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type} [Group L]
    [Finite L] (hperf : Group.IsPerfect L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : p ∣ Nat.card (Subgroup.center L))
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)))
    {t : StatedLieTag} {n r f : ℕ}
    (hm : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n r f) (ht : t = .PSL ∨ t = .PSU)
    (ha : p ∣ (genericOrders t n r f).1) :
    CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤ n - 1 ∧
      n - 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) := by
  have hcl := classical_of_lieModel hm ht
  have hadm := hcl.1
  have hr : r.Prime := hadm.1
  have hq0 : 1 ≤ r ^ f := Nat.one_le_pow _ _ hr.pos
  rcases ht with rfl | rfl
  · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hcl
    have hn2 : 2 ≤ n := hadm.2.2.1
    have hga : (genericOrders .PSL n r f).1 = Nat.gcd n (r ^ f - 1) := rfl
    have hpn : p ∣ n := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_left _ _)
    have hpq : p ∣ r ^ f - 1 := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_right _ _)
    have hH : (Nat.card K = r ^ f ∧ StatedSL n K = StatedSL n K ∧ p ∣ r ^ f - 1) ∨
        (Nat.card K = (r ^ f) ^ 2 ∧ StatedSL n K = StatedSU n (r ^ f) K ∧ p ∣ r ^ f + 1) :=
      Or.inl ⟨hK, rfl, hpq⟩
    have hup : CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤ n - 1 := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e']
      exact pRank_statedProj_le hp hp2 (by omega) hH
    have hn : 4 ≤ n := by omega
    refine ⟨hup, ?_⟩
    have hmm : CFSG.Models.LieModel (StatedProj (StatedSL n K)) .PSL n r f :=
      Multiplier.lieModel_of_classical ⟨hadm, K, inferInstance, inferInstance, hK,
        ⟨MulEquiv.refl _⟩⟩
    obtain ⟨hfin, hcard⟩ := Multiplier.finite_and_card_hopf hGA hmm
    have hdv : (genericOrders .PSL n r f).1 ∣
        Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) :=
      Multiplier.dvd_card_scalars (q := r ^ f) (by omega) hq0
        (Or.inl ⟨hK, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
    have : Fact p.Prime := ⟨hp⟩
    have := hfin
    have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSL n K)))).factorization p ≤
        (Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))).factorization p := by
      rw [hcard]
      refine (factorization_card_table hp hp2 hadm (Or.inl rfl) ha).trans ?_
      exact (Nat.factorization_le_iff_dvd (Multiplier.genericOrders_fst_pos hadm).ne'
        Nat.card_pos.ne').2 hdv p
    exact rank_ge_cover hperf hr hp hp2 hn (H := StatedSL n K) hH e' hZ hM
  · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hcl
    have hn3 : 3 ≤ n := hadm.2.2.1
    have hga : (genericOrders .PSU n r f).1 = Nat.gcd n (r ^ f + 1) := rfl
    have hpn : p ∣ n := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_left _ _)
    have hpq : p ∣ r ^ f + 1 := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_right _ _)
    have hH : (Nat.card K = r ^ f ∧ StatedSU n (r ^ f) K = StatedSL n K ∧ p ∣ r ^ f - 1) ∨
        (Nat.card K = (r ^ f) ^ 2 ∧ StatedSU n (r ^ f) K = StatedSU n (r ^ f) K ∧
          p ∣ r ^ f + 1) :=
      Or.inr ⟨hK, rfl, hpq⟩
    have hup : CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤ n - 1 := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e']
      exact pRank_statedProj_le hp hp2 (by omega) hH
    have hn : 4 ≤ n := by omega
    refine ⟨hup, ?_⟩
    have hmm : CFSG.Models.LieModel (StatedProj (StatedSU n (r ^ f) K)) .PSU n r f :=
      Multiplier.lieModel_of_classical ⟨hadm, K, inferInstance, inferInstance, hK,
        ⟨MulEquiv.refl _⟩⟩
    obtain ⟨hfin, hcard⟩ := Multiplier.finite_and_card_hopf hGA hmm
    have hdv : (genericOrders .PSU n r f).1 ∣
        Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K)) :=
      Multiplier.dvd_card_scalars (q := r ^ f) (by omega) hq0
        (Or.inr ⟨hK, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
    have : Fact p.Prime := ⟨hp⟩
    have := hfin
    have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSU n (r ^ f) K)))).factorization p ≤
        (Nat.card ((StatedScalars (Fin n) K).subgroupOf
          (StatedSU n (r ^ f) K))).factorization p := by
      rw [hcard]
      refine (factorization_card_table hp hp2 hadm (Or.inr rfl) ha).trans ?_
      exact (Nat.factorization_le_iff_dvd (Multiplier.genericOrders_fst_pos hadm).ne'
        Nat.card_pos.ne').2 hdv p
    exact rank_ge_cover hperf hr hp hp2 hn (H := StatedSU n (r ^ f) K) hH e' hZ hM

theorem lieCoverRankHighLin (hGA : CFSG.Open.GriessAllModelsStatement) : LieCoverRankHighLin := by
  intro L _ _ hq _ p hp hp2 hdvd h3 hex
  have hperf : Group.IsPerfect L := ⟨hq.1⟩
  obtain ⟨n, r, f, h⟩ := hex
  rcases h with ⟨hm, hg⟩ | ⟨hm, hg⟩
  · obtain ⟨h1, h2⟩ := lieCoverRankHighLin_aux hGA hperf hp hp2 hdvd h3 hm (Or.inl rfl) hg
    exact h1.trans h2
  · obtain ⟨h1, h2⟩ := lieCoverRankHighLin_aux hGA hperf hp hp2 hdvd h3 hm (Or.inr rfl) hg
    exact h1.trans h2

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
