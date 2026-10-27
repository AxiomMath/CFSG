module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Gen
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open MatrixGroups

private theorem noElemSq_psl_two_field {K : Type} [Field K] [Finite K] {q f : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hK : Nat.card K = q ^ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ q) (h4 : f * Nat.gcd 2 (q ^ f - 1) ∣ 4) :
    NoElemSq p (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  have : Fact p.Prime := ⟨hp⟩
  refine noElemSq_of_inner hp (CFSG.GorensteinWalter.psl2_center_eq_bot K) ?_ ?_
  · intro hdvd
    have hout := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor hq K hK).1
    have h : p ∣ 2 ^ 2 := hdvd.trans (hout.trans h4)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · intro P hP
    obtain ⟨R, hPR⟩ := hP.exists_le_sylow
    have := CFSG.SectionRank.OddCover.psl_two_sylow_isCyclic hq hq2 hK hp2 hpq R
    exact Subgroup.isCyclic_of_le hPR

theorem noElemSq_psl_two (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ q) : NoElemSq p PSL(2, ZMod q) :=
  noElemSq_psl_two_field (Fact.out : q.Prime) hq2 (by rw [Nat.card_zmod, pow_one]) hp hp2 hpq
    (by rw [one_mul, pow_one]; exact (Nat.gcd_dvd_left 2 _).trans (by norm_num))

theorem noElemSq_psl_two_sq (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ q) : NoElemSq p PSL(2, GaloisField q 2) :=
  noElemSq_psl_two_field (Fact.out : q.Prime) hq2 (GaloisField.card q 2 two_ne_zero) hp hp2 hpq
    (Nat.mul_dvd_mul_left 2 (Nat.gcd_dvd_left 2 _))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
