module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Local.RankTwoPCoreSeriesAbelianTop
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} {L : Type*} [Group L] [Finite L]

theorem notMem_elementaryAbelianRanks_iff {d : ℕ} {M : Type*} [Group M] :
    d ∉ elementaryAbelianRanks p M ↔
      ∀ H : Subgroup M, IsEmpty (H ≃* (Fin d → Multiplicative (ZMod p))) := by
  simp [mem_elementaryAbelianRanks, not_nonempty_iff]

theorem elementaryAbelianPRank_le_two_of_three_notMem {M : Type*} [Group M] [Finite M]
    (hp : p.Prime) (h : 3 ∉ elementaryAbelianRanks p M) : elementaryAbelianPRank p M ≤ 2 := by
  by_contra hlt
  exact h (mem_elementaryAbelianRanks_of_le (Nat.not_le.1 hlt)
    (elementaryAbelianPRank_mem_elementaryAbelianRanks hp.one_lt))

theorem normalizer_sup_pComplCore_eq_top [Group.IsSolvable L] (hp : p.Prime)
    (hodd : Odd (Nat.card L)) (P : Sylow p L)
    (hP3 : 3 ∉ elementaryAbelianRanks p ↥(P : Subgroup L)) :
    normalizer ((P : Subgroup L) : Set L) ⊔ pComplCore p L = ⊤ := by
  have := Fact.mk hp
  have hPcard : Nat.card (P : Subgroup L) = p ^ (Nat.card L).factorization p :=
    P.card_eq_multiplicity
  by_cases hdvd : p ∣ Nat.card L
  ·
    have hpodd : Odd p := hp.odd_of_ne_two (by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd))
    have hrank : elementaryAbelianPRank p L ≤ 2 := by
      rw [← elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hp hPcard]
      exact elementaryAbelianPRank_le_two_of_three_notMem hp hP3
    have hR : pComplPCore p L = pComplCore p L ⊔ (P : Subgroup L) :=
      pComplPCore_eq_sup_of_sylow hp hpodd hodd hrank P
    have hPR : (P : Subgroup L) ≤ pComplPCore p L := hR ▸ le_sup_right
    have hPRcard : Nat.card (P : Subgroup L)
        = p ^ (Nat.card (pComplPCore p L)).factorization p :=
      natCard_eq_pow_factorization_of_le hp hPR hPcard
    have hfrat := normalizer_sup_eq_top_of_normal (p := p) hPR hPRcard
    rw [hR] at hfrat
    refine le_antisymm le_top ?_
    rw [← hfrat, sup_comm (pComplCore p L) (P : Subgroup L), ← sup_assoc]
    exact sup_le_sup_right (sup_le le_rfl le_normalizer) _
  ·
    have h1 : (P : Subgroup L) = ⊥ := by
      refine Subgroup.card_eq_one.1 ?_
      rw [hPcard, Nat.factorization_eq_zero_of_not_dvd hdvd, pow_zero]
    rw [h1, Subgroup.normalizer_eq_top, top_sup_eq]

theorem coe_normalizer_mul_coe_pComplCore_eq_univ_of_three_notMem [Group.IsSolvable L]
    (hp : p.Prime) (hodd : Odd (Nat.card L)) (P : Sylow p L)
    (hP3 : 3 ∉ elementaryAbelianRanks p ↥(P : Subgroup L)) :
    ((normalizer ((P : Subgroup L) : Set L) : Subgroup L) : Set L)
        * (pComplCore p L : Set L) = Set.univ := by
  rw [← Subgroup.mul_normal, normalizer_sup_pComplCore_eq_top hp hodd P hP3, Subgroup.coe_top]

theorem coe_pComplCore_mul_coe_normalizer_eq_univ_of_three_notMem [Group.IsSolvable L]
    (hp : p.Prime) (hodd : Odd (Nat.card L)) (P : Sylow p L)
    (hP3 : 3 ∉ elementaryAbelianRanks p ↥(P : Subgroup L)) :
    (pComplCore p L : Set L)
        * ((normalizer ((P : Subgroup L) : Set L) : Subgroup L) : Set L) = Set.univ := by
  rw [← Subgroup.normal_mul, sup_comm, normalizer_sup_pComplCore_eq_top hp hodd P hP3,
    Subgroup.coe_top]

theorem exists_mem_normalizer_mul_mem_pComplCore [Group.IsSolvable L] (hp : p.Prime)
    (hodd : Odd (Nat.card L)) (P : Sylow p L)
    (hP3 : 3 ∉ elementaryAbelianRanks p ↥(P : Subgroup L)) (x : L) :
    ∃ n ∈ normalizer ((P : Subgroup L) : Set L), ∃ y ∈ pComplCore p L, x = n * y := by
  have hx : x ∈ ((normalizer ((P : Subgroup L) : Set L) : Subgroup L) : Set L)
      * (pComplCore p L : Set L) := by
    rw [coe_normalizer_mul_coe_pComplCore_eq_univ_of_three_notMem hp hodd P hP3]; trivial
  obtain ⟨n, hn, y, hy, hxy⟩ := hx
  exact ⟨n, hn, y, hy, hxy.symm⟩

theorem exists_mem_pComplCore_mul_mem_normalizer [Group.IsSolvable L] (hp : p.Prime)
    (hodd : Odd (Nat.card L)) (P : Sylow p L)
    (hP3 : 3 ∉ elementaryAbelianRanks p ↥(P : Subgroup L)) (x : L) :
    ∃ y ∈ pComplCore p L, ∃ n ∈ normalizer ((P : Subgroup L) : Set L), x = y * n := by
  have hx : x ∈ (pComplCore p L : Set L)
      * ((normalizer ((P : Subgroup L) : Set L) : Subgroup L) : Set L) := by
    rw [coe_pComplCore_mul_coe_normalizer_eq_univ_of_three_notMem hp hodd P hP3]; trivial
  obtain ⟨y, hy, n, hn, hxy⟩ := hx
  exact ⟨y, hy, n, hn, hxy.symm⟩

theorem normalizer_sup_pComplCore_eq_top_of_natCard_eq [Group.IsSolvable L] (hp : p.Prime)
    (hodd : Odd (Nat.card L)) {P : Subgroup L}
    (hPcard : Nat.card P = p ^ (Nat.card L).factorization p)
    (hP3 : 3 ∉ elementaryAbelianRanks p ↥P) :
    normalizer (P : Set L) ⊔ pComplCore p L = ⊤ := by
  have := Fact.mk hp
  have h := normalizer_sup_pComplCore_eq_top hp hodd (Sylow.ofCard P hPcard) ?_
  · rwa [Sylow.coe_ofCard] at h
  · rwa [Sylow.coe_ofCard]

end

end CFSG.FeitThompson
