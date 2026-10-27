module

public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Holt

open MulAction CFSG.Open
open scoped Pointwise

namespace NotStarCases

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

section Transfer

variable {X : Type*} [Group X] [Finite X]

theorem not_mem_commutator_of_index_two {P Q : Subgroup X} (hP : IsPGroup 2 P)
    (hPidx : ¬ 2 ∣ P.index) (hQP : Q ≤ P) (hQidx : Q.relIndex P = 2) {a : X} (haP : a ∈ P)
    (haQ : a ∉ Q)
    (ha2 : a * a = 1) (hconj : ∀ g : X, g⁻¹ * a * g ∉ Q) : a ∉ commutator X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (Q.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two hQidx
  have hQn : ∀ t ∈ P, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := fun t ht q hq =>
    Subgroup.mem_subgroupOf.1
      (hn.conj_mem ⟨q, hQP hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨t, ht⟩)
  obtain h | ⟨g, hgQ, -⟩ := CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hP hPidx hQn
    ⟨a, haP, fun t ht => by
      by_cases htQ : t ∈ Q
      · exact ⟨0, by simpa using htQ⟩
      · exact ⟨1, by
          simpa using CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hQidx haP ht haQ htQ⟩⟩
    haP haQ (fun g k _ => by
      rw [pow_mul, pow_two, ha2, one_pow, mul_one, inv_mul_cancel]
      exact one_mem _)
    (fun g hgP _ => Or.inr (CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hQidx haP hgP haQ
      (hconj g)))
  · obtain ⟨N, hN, hcyc, -, haN⟩ := h
    intro hc
    apply haN
    let := hcyc.commGroup
    have : IsMulCommutative (X ⧸ N) := ⟨⟨fun x y => mul_comm x y⟩⟩
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le.mp this) hc
  · exact (hconj g hgQ).elim

end Transfer

end NotStarCases

end CFSG.Holt
