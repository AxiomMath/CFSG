module

public import CFSG.CharacterTheory.Semidihedral.PrimeResidual

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUni

open Subgroup CFSG.Semidihedral

theorem map_mem_of_pow_eq_one {p : ℕ} [Fact p.Prime] {Y A : Type} [Group Y] [Finite Y] [Group A]
    (H : Subgroup A) [H.Normal] (hcomm : ∀ a b : A, a * b * a⁻¹ * b⁻¹ ∈ H)
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤) (ψ : Y →* A) {y : Y}
    (hy : y ^ p = 1) : ψ y ∈ H := by
  have hp : p.Prime := Fact.out
  have hres : primeResidual p Y = ⊤ := hperf _ primeResidual_quotient_isPGroup
  set q : Y →* A ⧸ H := (QuotientGroup.mk' H).comp ψ with hq
  have hcommQ : ∀ a b : A ⧸ H, Commute a b := by
    intro a b
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    show (a : A ⧸ H) * b = b * a
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h := hcomm b⁻¹ a⁻¹
    simpa [mul_assoc] using h
  have hord : ∀ g ∈ primeResidual p Y, ¬ p ∣ orderOf (q g) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact fun hd => hg (hd.trans (orderOf_map_dvd q g))
    | one => simpa using hp.not_dvd_one
    | mul a b _ _ ha hb =>
      intro hd
      rw [map_mul] at hd
      have h1 := (hcommQ (q a) (q b)).orderOf_mul_dvd_lcm
      have h2 : p ∣ orderOf (q a) * orderOf (q b) :=
        hd.trans (h1.trans (Nat.lcm_dvd_mul _ _))
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h | h
      · exact ha h
      · exact hb h
    | inv a _ ha => simpa [orderOf_inv] using ha
  have hy1 : ¬ p ∣ orderOf (q y) := hord y (hres ▸ mem_top y)
  have hdvd : orderOf (q y) ∣ p :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hy, map_one])
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · have hq1 : q y = 1 := orderOf_eq_one_iff.1 h
    exact (QuotientGroup.eq_one_iff _).1 hq1
  · exact absurd (h ▸ dvd_refl p) hy1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUni
