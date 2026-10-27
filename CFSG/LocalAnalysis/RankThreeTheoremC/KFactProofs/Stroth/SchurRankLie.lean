module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinHighCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRank

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (factorization_card_table)
open CFSG.HardMathSupport.Timmesfeld.LinearRank (rank_ge_cover)
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open CFSG.Open (GriessAllModelsStatement)

theorem dvd_first_generic_of_five_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {t : StatedLieTag}
    {n r f : ℕ} (hadm : StatedLieAdmissible t n r f)
    (h : p ∣ (genericOrders t n r f).1 * (genericOrders t n r f).2 *
      ((exceptionalOrders t n r f).1 * (exceptionalOrders t n r f).2)) :
    (t = .PSL ∨ t = .PSU) ∧ p ∣ (genericOrders t n r f).1 := by
  have hnd : ∀ x : ℕ, 0 < x → x ≤ 4 → ¬ p ∣ x := fun x h0 h4 hd => by
    have := Nat.le_of_dvd h0 hd
    omega
  obtain ⟨hb1, hb2⟩ := genericOrders_snd_le t n r f
  obtain ⟨⟨hc1, hc2⟩, ⟨hd1, hd2⟩⟩ := exceptionalOrders_le t n r f
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · by_cases hL : t = .PSL
      · exact ⟨Or.inl hL, h⟩
      by_cases hU : t = .PSU
      · exact ⟨Or.inr hU, h⟩
      exact (hnd _ (genericOrders_fst_pos hadm) (genericOrders_fst_le_four hL hU n r f) h).elim
    · exact (hnd _ hb1 (by omega) h).elim
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact (hnd _ hc1 hc2 h).elim
    · exact (hnd _ hd1 hd2 h).elim

theorem four_le_pRank_of_classical (hGA : GriessAllModelsStatement) {L : Type} [Group L] [Finite L]
    (hperf : Group.IsPerfect L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : p ∣ Nat.card (Subgroup.center L)) {t : StatedLieTag} {n r f : ℕ}
    (hcl : StatedClassicalModel (L ⧸ Subgroup.center L) t n r f) (ht : t = .PSL ∨ t = .PSU)
    (ha : p ∣ (genericOrders t n r f).1) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) := by
  have hp2 : p ≠ 2 := by omega
  have hadm := hcl.1
  have hr : r.Prime := hadm.1
  have hq0 : 1 ≤ r ^ f := Nat.one_le_pow _ _ hr.pos
  rcases ht with rfl | rfl
  · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hcl
    have hn2 : 2 ≤ n := hadm.2.2.1
    have hga : (genericOrders .PSL n r f).1 = Nat.gcd n (r ^ f - 1) := rfl
    have hpn : p ∣ n := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_left _ _)
    have hpq : p ∣ r ^ f - 1 := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_right _ _)
    have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd (by omega) hpn)
    have hH : (Nat.card K = r ^ f ∧ StatedSL n K = StatedSL n K ∧ p ∣ r ^ f - 1) ∨
        (Nat.card K = (r ^ f) ^ 2 ∧ StatedSL n K = StatedSU n (r ^ f) K ∧ p ∣ r ^ f + 1) :=
      Or.inl ⟨hK, rfl, hpq⟩
    have hmm : CFSG.Models.LieModel (StatedProj (StatedSL n K)) .PSL n r f :=
      lieModel_of_classical ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
    obtain ⟨hfin, hcard⟩ := finite_and_card_hopf hGA hmm
    have hdv : (genericOrders .PSL n r f).1 ∣
        Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) :=
      dvd_card_scalars (q := r ^ f) (by omega) hq0
        (Or.inl ⟨hK, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
    have : Fact p.Prime := ⟨hp⟩
    have := hfin
    have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSL n K)))).factorization p ≤
        (Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))).factorization p := by
      rw [hcard]
      refine (factorization_card_table hp hp2 hadm (Or.inl rfl) ha).trans ?_
      exact (Nat.factorization_le_iff_dvd (genericOrders_fst_pos hadm).ne'
        Nat.card_pos.ne').2 hdv p
    have hrank := rank_ge_cover hperf hr hp hp2 (by omega) (H := StatedSL n K) hH e' hZ hM
    omega
  · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hcl
    have hn3 : 3 ≤ n := hadm.2.2.1
    have hga : (genericOrders .PSU n r f).1 = Nat.gcd n (r ^ f + 1) := rfl
    have hpn : p ∣ n := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_left _ _)
    have hpq : p ∣ r ^ f + 1 := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_right _ _)
    have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd (by omega) hpn)
    have hH : (Nat.card K = r ^ f ∧ StatedSU n (r ^ f) K = StatedSL n K ∧ p ∣ r ^ f - 1) ∨
        (Nat.card K = (r ^ f) ^ 2 ∧ StatedSU n (r ^ f) K = StatedSU n (r ^ f) K ∧
          p ∣ r ^ f + 1) :=
      Or.inr ⟨hK, rfl, hpq⟩
    have hmm : CFSG.Models.LieModel (StatedProj (StatedSU n (r ^ f) K)) .PSU n r f :=
      lieModel_of_classical ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
    obtain ⟨hfin, hcard⟩ := finite_and_card_hopf hGA hmm
    have hdv : (genericOrders .PSU n r f).1 ∣
        Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K)) :=
      dvd_card_scalars (q := r ^ f) (by omega) hq0
        (Or.inr ⟨hK, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
    have : Fact p.Prime := ⟨hp⟩
    have := hfin
    have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSU n (r ^ f) K)))).factorization p ≤
        (Nat.card ((StatedScalars (Fin n) K).subgroupOf
          (StatedSU n (r ^ f) K))).factorization p := by
      rw [hcard]
      refine (factorization_card_table hp hp2 hadm (Or.inr rfl) ha).trans ?_
      exact (Nat.factorization_le_iff_dvd (genericOrders_fst_pos hadm).ne'
        Nat.card_pos.ne').2 hdv p
    have hrank := rank_ge_cover hperf hr hp hp2 (by omega) (H := StatedSU n (r ^ f) K) hH e' hZ hM
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRank
