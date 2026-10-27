module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem hasDiagOuterThree_unitaryPSU {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) (h3n : 3 ∣ n) (h3q : 3 ∣ p ^ f + 1) :
    HasDiagOuterThree (unitaryPSU h n) := by
  obtain ⟨⟨eT⟩, -, hcard, -⟩ := unitary_full_diagonal_outer_order h hn hq
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hT
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hD
  have h3 : 3 ∣ Nat.card (D ⧸ (inner T).subgroupOf D) := by
    rw [hcard]
    exact Nat.dvd_gcd h3n h3q
  have hfin : Finite (D ⧸ (inner T).subgroupOf D) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Nat.gcd_pos_of_pos_left _ (by omega)).ne')
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  refine HasDiagOuterThree.of_mulEquiv eT ⟨(α : MulAut T), fun k hk => ?_⟩
  have h1 : α ^ 2 ^ k ∈ (inner T).subgroupOf D :=
    hk
  have h2 : orderOf (QuotientGroup.mk α :
      D ⧸ (inner T).subgroupOf D) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact h1
  rw [hx] at h2
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
