module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Pointwise

theorem IsL2Pair.mem_of_mem_normalizer_of_mul_self_eq_one {X : Type} [Group X] {S : Subgroup X}
    {q : ℕ} (h : IsL2Pair X S q) {g : X} (hg : g ∈ Subgroup.normalizer (S : Set X))
    (hgg : g * g = 1) : g ∈ S := by
  obtain ⟨Q, hQ⟩ := h.exists_sylow_eq
  have : Finite X := h.finite
  have hP : IsPGroup 2 (Subgroup.zpowers g) := by
    rintro ⟨a, ha⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    refine ⟨1, Subtype.ext ?_⟩
    show (g ^ j) ^ 2 ^ 1 = 1
    have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact hgg
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg2, one_zpow]
  have h1 := hP.inf_normalizer_sylow Q
  have hQS : (Q : Set X) = (S : Set X) := by
    rw [← hQ]
    rfl
  have hgN : g ∈ Subgroup.normalizer (Q : Set X) := by
    rw [hQS]
    exact hg
  have hmem : g ∈ Subgroup.zpowers g ⊓ Subgroup.normalizer (Q : Set X) :=
    ⟨Subgroup.mem_zpowers g, hgN⟩
  rw [h1] at hmem
  rw [← hQ]
  exact hmem.2

end CFSG.CGT.Timmesfeld75
