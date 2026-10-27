module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Witness

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem threeTwoWitness_quotient_center {A : Type} [Group A] [Finite A] (Q : Subgroup A)
    (hQ2 : IsPGroup 2 Q) (hQ : ¬ Q ≤ Subgroup.center A) (g : A)
    (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hg3 : g ^ 3 = 1) (hgc : g ∉ Subgroup.center A) :
    ThreeTwoWitness (A ⧸ Subgroup.center A) := by
  let π : A →* A ⧸ Subgroup.center A := QuotientGroup.mk' (Subgroup.center A)
  refine ThreeTwoWitness.mk' (P := Q.map π) ?_ (hQ2.map π) (x := π g) ?_ ?_
  · intro h
    apply hQ
    intro q hq
    have : π q ∈ Q.map π := Subgroup.mem_map_of_mem π hq
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff q).1 this
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hg3, map_one]
    · intro h
      exact hgc ((QuotientGroup.eq_one_iff g).1 h)
  · refine mem_normalizer_of_conj_le fun y hy => ?_
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨g * q * g⁻¹, hg q hq, ?_⟩
    simp [π]

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
