module

public import CFSG.LieType.AlgebraicGroups.ClosedCone

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u v w

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem polyEval_sum_pow_smul {ι : Type w} (s : Finset ι) (n : ι → ℕ) (w : ι → V) (t : k)
    (f : MvPolynomial (Module.Dual k V) k) :
    polyEval k (∑ i ∈ s, t ^ n i • w i) f =
      Polynomial.eval t ((MvPolynomial.aeval fun φ : Module.Dual k V =>
        ∑ i ∈ s, Polynomial.C (φ (w i)) * Polynomial.X ^ n i) f) := by
  rw [← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun φ => ?_
  simp only [polyEval, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_smul, smul_eq_mul,
    map_mul, Polynomial.coe_aeval_eq_eval, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, mul_comm]

theorem IsZariskiClosed.mem_of_forall_ne_zero [Infinite k] {C : Set V} (hC : IsZariskiClosed k C)
    {ι : Type w} (s : Finset ι) (n : ι → ℕ) (w : ι → V)
    (h : ∀ t : k, t ≠ 0 → ∑ i ∈ s, t ^ n i • w i ∈ C) (t : k) :
    ∑ i ∈ s, t ^ n i • w i ∈ C := by
  obtain ⟨S, rfl⟩ := hC
  intro f hf
  rw [polyEval_sum_pow_smul]
  set P := (MvPolynomial.aeval fun φ : Module.Dual k V =>
    ∑ i ∈ s, Polynomial.C (φ (w i)) * Polynomial.X ^ n i) f
  have hP : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P
      ((Set.finite_singleton (0 : k)).infinite_compl.mono fun t ht => ?_)
    have h₀ := h t ht f hf
    rw [polyEval_sum_pow_smul] at h₀
    exact h₀
  rw [hP, Polynomial.eval_zero]

theorem IsZariskiClosed.sum_lowest_mem [Infinite k] {C : Set V} (hC : IsZariskiClosed k C)
    (hcone : IsCone k C) {ι : Type w} (s : Finset ι) (hs : s.Nonempty) (e : ι → ℤ) (w : ι → V)
    (h : ∀ t : k, t ≠ 0 → ∑ i ∈ s, t ^ e i • w i ∈ C) :
    ∑ i ∈ s with ∀ j ∈ s, e i ≤ e j, w i ∈ C := by
  set a := s.inf' hs e
  have ha : ∀ i ∈ s, a ≤ e i := fun i hi => s.inf'_le e hi
  have hcurve : ∀ t : k, t ≠ 0 → ∑ i ∈ s, t ^ (e i - a).toNat • w i ∈ C := by
    intro t ht
    convert hcone (t ^ (-a)) _ (h t ht) using 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [smul_smul, ← zpow_add₀ ht, ← zpow_natCast,
      Int.toNat_of_nonneg (sub_nonneg.mpr (ha i hi)), sub_eq_neg_add]
  convert hC.mem_of_forall_ne_zero s (fun i => (e i - a).toNat) w hcurve 0 using 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hmin : ∀ j ∈ s, e i ≤ e j
  · have hia : e i = a := le_antisymm (Finset.le_inf' hs e hmin) (ha i hi)
    rw [if_pos hmin, hia, sub_self, Int.toNat_zero, pow_zero, one_smul]
  · obtain ⟨j, hj, hji⟩ : ∃ j ∈ s, e j < e i := by simpa using hmin
    have hpos : (e i - a).toNat ≠ 0 := by
      have := ha j hj
      omega
    rw [if_neg hmin, zero_pow hpos, zero_smul]

theorem IsZariskiClosed.sum_highest_mem [Infinite k] {C : Set V} (hC : IsZariskiClosed k C)
    (hcone : IsCone k C) {ι : Type w} (s : Finset ι) (hs : s.Nonempty) (e : ι → ℤ) (w : ι → V)
    (h : ∀ t : k, t ≠ 0 → ∑ i ∈ s, t ^ e i • w i ∈ C) :
    ∑ i ∈ s with ∀ j ∈ s, e j ≤ e i, w i ∈ C := by
  have h' := hC.sum_lowest_mem hcone s hs (fun i => -e i) w fun t ht => by
    simpa only [inv_zpow'] using h t⁻¹ (inv_ne_zero ht)
  simpa only [neg_le_neg_iff] using h'

end CFSG.LieType.AlgebraicGroups.ClosedCone
