module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.LinearCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open CFSG.Assembly.LowTwoRank CFSG.Models CFSG.Blueprint.Multiplier
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open CFSG.Open (GriessAllModelsStatement)

theorem rank_ge_of_model (hGA : GriessAllModelsStatement) {L : Type} [Group L] [Finite L]
    (hperf : Group.IsPerfect L) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hZ : IsPGroup r (Subgroup.center L)) {X : Type} [Group X]
    (e : L ⧸ Subgroup.center L ≃* X) {t : StatedLieTag} {n p f : ℕ}
    (hm : LieModel X t n p f) (ht : t = .PSL ∨ t = .PSU) (hn : 4 ≤ n)
    (ha : r ∣ (genericOrders t n p f).1) (hb : ¬ r ∣ (genericOrders t n p f).2)
    (hc : ¬ r ∣ (exceptionalOrders t n p f).1) (hd : ¬ r ∣ (exceptionalOrders t n p f).2) :
    n - 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup L) := by
  have hp : p.Prime := hm.1.1
  have hq0 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have key : ∀ (M : ℕ), M = (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) →
      M.factorization r = (genericOrders t n p f).1.factorization r := by
    intro M hM
    have h1 : (genericOrders t n p f).1 ≠ 0 := (genericOrders_fst_pos hm.1).ne'
    have h2 : (genericOrders t n p f).2 ≠ 0 := (genericOrders_snd_le t n p f).1.ne'
    have h3 : (exceptionalOrders t n p f).1 ≠ 0 := (exceptionalOrders_le t n p f).1.1.ne'
    have h4 : (exceptionalOrders t n p f).2 ≠ 0 := (exceptionalOrders_le t n p f).2.1.ne'
    rw [hM, Nat.factorization_mul (mul_ne_zero h1 h2) (mul_ne_zero h3 h4),
      Nat.factorization_mul h1 h2, Nat.factorization_mul h3 h4]
    simp [Nat.factorization_eq_zero_of_not_dvd hb, Nat.factorization_eq_zero_of_not_dvd hc,
      Nat.factorization_eq_zero_of_not_dvd hd]
  have hn0 : n ≠ 0 := by omega
  rcases ht with rfl | rfl
  ·
    obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hm
    swap
    · exact absurd h0 hn0
    obtain ⟨hadm, K, _, _, hK, ⟨e'⟩⟩ := hcl
    have hmm : LieModel (StatedProj (StatedSL n K)) .PSL n p f :=
      lieModel_of_classical ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
    obtain ⟨hfin, hcard⟩ := finite_and_card_hopf hGA hmm
    have hga : (genericOrders .PSL n p f).1 = Nat.gcd n (p ^ f - 1) := rfl
    have hrn : r ∣ n := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_left _ _)
    have hrq : r ∣ p ^ f - 1 := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_right _ _)
    have hD : (genericOrders .PSL n p f).1.factorization r ≤
        (Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))).factorization r := by
      have hdv : r ^ (genericOrders .PSL n p f).1.factorization r ∣
          Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) := by
        refine dvd_card_scalars (q := p ^ f) (by omega) hq0 (Or.inl ⟨hK, rfl, ?_, ?_⟩)
        · exact (Nat.ordProj_dvd _ r).trans (hga ▸ Nat.gcd_dvd_left _ _)
        · exact (Nat.ordProj_dvd _ r).trans (hga ▸ Nat.gcd_dvd_right _ _)
      exact (hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdv
    have : Fact r.Prime := ⟨hr⟩
    have := hfin
    have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSL n K)))).factorization r ≤
        (Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))).factorization r := by
      rw [hcard, key _ rfl]
      exact hD
    exact rank_of_cover hperf hp hr hr2 hn (H := StatedSL n K) (Or.inl ⟨hK, rfl, hrq⟩)
      (e.trans e') hZ hM
  ·
    obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hm
    swap
    · exact absurd h0 hn0
    obtain ⟨hadm, K, _, _, hK, ⟨e'⟩⟩ := hcl
    have hmm : LieModel (StatedProj (StatedSU n (p ^ f) K)) .PSU n p f :=
      lieModel_of_classical ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
    obtain ⟨hfin, hcard⟩ := finite_and_card_hopf hGA hmm
    have hga : (genericOrders .PSU n p f).1 = Nat.gcd n (p ^ f + 1) := rfl
    have hrn : r ∣ n := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_left _ _)
    have hrq : r ∣ p ^ f + 1 := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_right _ _)
    have hD : (genericOrders .PSU n p f).1.factorization r ≤
        (Nat.card ((StatedScalars (Fin n) K).subgroupOf
          (StatedSU n (p ^ f) K))).factorization r := by
      have hdv : r ^ (genericOrders .PSU n p f).1.factorization r ∣
          Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)) := by
        refine dvd_card_scalars (q := p ^ f) (by omega) hq0 (Or.inr ⟨hK, rfl, ?_, ?_⟩)
        · exact (Nat.ordProj_dvd _ r).trans (hga ▸ Nat.gcd_dvd_left _ _)
        · exact (Nat.ordProj_dvd _ r).trans (hga ▸ Nat.gcd_dvd_right _ _)
      exact (hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdv
    have : Fact r.Prime := ⟨hr⟩
    have := hfin
    have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSU n (p ^ f) K)))).factorization r ≤
        (Nat.card ((StatedScalars (Fin n) K).subgroupOf
          (StatedSU n (p ^ f) K))).factorization r := by
      rw [hcard, key _ rfl]
      exact hD
    exact rank_of_cover hperf hp hr hr2 hn (H := StatedSU n (p ^ f) K)
      (Or.inr ⟨hK, rfl, hrq⟩) (e.trans e') hZ hM

end CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
