module

public import CFSG.LocalAnalysis.GL83PartI.I713.Chain
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic

public section

namespace GL83.I713

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {p : ℕ}

theorem normal_of_subgroupOf_top {X : Type*} [Group X] {H R : Subgroup X} (hR : R = ⊤)
    (h : (H.subgroupOf R).Normal) : H.Normal := by
  subst hR
  exact ⟨fun d hd x => h.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨x, Subgroup.mem_top x⟩⟩

theorem coprime_of_le_two {k : ℕ} (hk0 : k ≠ 0) (hk : k ≤ 2) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.Coprime k p := by
  have : 1 ≤ k := Nat.pos_of_ne_zero hk0
  interval_cases k
  · exact Nat.coprime_one_left p
  · exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)

theorem outClauseFor_projectiveSL_of_diag {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (hdiag : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.gcd n (Nat.card K - 1) →
      2 ≤ pRank p (⊤ : Subgroup (projectiveSL n K))) :
    OutClauseFor (projectiveSL n K) := by
  intro p hp hp2 hK
  by_cases hpd : p ∣ Nat.gcd n (Nat.card K - 1)
  · exact absurd (hdiag p hp hp2 hpd) (by omega)
  have hgen := (automorphism_generation (K := K) hn).1
  obtain ⟨hID, -, hDnorm, hEnorm, -, hcyc, -, hindex, -⟩ := standard_outer_quotients (n := n) (K := K)
  have : (linearAutGroup n K).Normal := normal_of_subgroupOf_top hgen hDnorm
  have : (semilinearAutGroup n K).Normal := normal_of_subgroupOf_top hgen hEnorm
  rw [hgen, ← Subgroup.relIndex, Subgroup.relIndex_top_right] at hindex
  refine pRank_outer_le_one_of_chain hp hID linearAutGroup_le_semilinearAutGroup hcyc ?_
    (coprime_of_le_two (Subgroup.index_ne_zero_of_finite) hindex hp hp2)
  exact Nat.Coprime.coprime_dvd_left
    (UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := K) (by omega : 1 ≤ n))
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd).symm

end GL83.I713
