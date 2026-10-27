module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthLinear
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitarySummand

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open Module CFSG.LocalAnalysis.ComponentInitial

theorem exists_lowRank_of_normal_nonabelian_unitary {E U : Type*} [Field E] [AddCommGroup U]
    [Module E U] [FiniteDimensional E U] {σ : E →+* E} {B : U →ₛₗ[σ] U →ₗ[E] E} {m : ℕ}
    (e : Basis (Fin m) E U) (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) {μ : E}
    (hμ : μ ≠ 1) (hμn : σ μ * μ = 1) {N : Subgroup (LinearMap.GeneralLinearGroup E U)}
    (hnormal : ∀ f ∈ sesqUnitaryGroup B, ∀ n ∈ N, f * n * f⁻¹ ∈ N)
    (hna : ∃ n₁ ∈ N, ∃ n₂ ∈ N, n₁ * n₂ ≠ n₂ * n₁) :
    ∃ n ∈ N, 0 < finrank E (LinearMap.range ((n : Module.End E U) - 1)) ∧
      finrank E (LinearMap.range ((n : Module.End E U) - 1)) < 3 := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμn
  refine exists_lowRank_of_normal_nonabelian e hμ (F := sesqUnitaryGroup B) (N := N)
    hnormal ?_ ?_ hna
  · intro i
    obtain ⟨d, hd, hde⟩ := exists_pseudoReflection_diag e hμ0 i
    refine ⟨d, ?_, hd⟩
    refine mem_sesqUnitaryGroup_of_basis e he (Equiv.refl _) (fun k => if k = i then μ else 1)
      (fun k => ?_) (fun k => ?_)
    · by_cases hk : k = i
      · simpa [hk] using hμn
      · simp [hk]
    · simpa using hde k
  · intro i j hij
    obtain ⟨t, ht, hte⟩ := exists_pseudoReflection_swap e hij
    refine ⟨t, ?_, ht⟩
    refine mem_sesqUnitaryGroup_of_basis e he (Equiv.swap i j) (fun _ => 1)
      (fun k => by simp) (fun k => ?_)
    simpa using hte k

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
