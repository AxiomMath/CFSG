module

public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

public section

namespace CFSG.UnitaryInvolutionIndex

open Module Module.End

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem isSemisimple_of_pow_eq_one {f : End k V} {n : ℕ} (hn : (n : k) ≠ 0) (hf : f ^ n = 1) :
    f.IsSemisimple := by
  refine isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C 1 hn one_ne_zero).squarefree ?_
  simp [hf]

theorem iSup_eigenspace_eq_top_of_pow_eq_one [IsAlgClosed k] [FiniteDimensional k V]
    {f : End k V} {n : ℕ} (hn : (n : k) ≠ 0) (hf : f ^ n = 1) : ⨆ μ, f.eigenspace μ = ⊤ :=
  (isSemisimple_of_pow_eq_one hn hf).iSup_eigenspace_eq_top

theorem pow_eq_one_of_hasEigenvector {f : End k V} {n : ℕ} (hf : f ^ n = 1) {μ : k} {v : V}
    (hv : f.HasEigenvector μ v) : μ ^ n = 1 := by
  have h := hv.pow_apply n
  rw [hf, one_apply] at h
  have h0 : (μ ^ n - 1) • v = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hv.2)

variable {ι : Type*} [Fintype ι]

theorem card_le_finrank_of_hasEigenvector [FiniteDimensional k V] (f : End k V) {μ : ι → k}
    (hμ : Function.Injective μ) {v : ι → V} (hv : ∀ i, f.HasEigenvector (μ i) (v i)) :
    Fintype.card ι ≤ finrank k V :=
  (f.eigenvectors_linearIndependent' μ hμ v hv).fintype_card_le_finrank

section Eigenbasis

variable {f : End k V} {μ : ι → k} {v : ι → V}

theorem mul_sub_eq_zero_of_apply_sum (hμ : Function.Injective μ)
    (hv : ∀ i, f.HasEigenvector (μ i) (v i)) {c : ι → k} {ν : k}
    (hu : f (∑ i, c i • v i) = ν • ∑ i, c i • v i) (j : ι) : c j * (μ j - ν) = 0 := by
  refine Fintype.linearIndependent_iff.mp (f.eigenvectors_linearIndependent' μ hμ v hv)
    (fun i => c i * (μ i - ν)) ?_ j
  simp only [map_sum, map_smul, (hv _).apply_eq_smul, Finset.smul_sum] at hu
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hu
  rw [← hu]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_sub, sub_smul, mul_smul, mul_smul, smul_comm ν]

variable [FiniteDimensional k V] (hμ : Function.Injective μ)
  (hv : ∀ i, f.HasEigenvector (μ i) (v i)) (hcard : Fintype.card ι = finrank k V)
include hμ hv hcard

theorem exists_eq_sum_smul (u : V) : ∃ c : ι → k, u = ∑ i, c i • v i := by
  have hli := f.eigenvectors_linearIndependent' μ hμ v hv
  have hspan : Submodule.span k (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  have hu : u ∈ Submodule.span k (Set.range v) := hspan ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hu
  exact ⟨c, hc.symm⟩

theorem exists_eq_smul_of_apply_eq_smul (i : ι) {u : V} (hu : f u = μ i • u) :
    ∃ a : k, u = a • v i := by
  classical
  obtain ⟨c, rfl⟩ := exists_eq_sum_smul hμ hv hcard u
  refine ⟨c i, Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)⟩
  have h := mul_sub_eq_zero_of_apply_sum hμ hv hu j
  rw [(mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr (hμ.ne hj)), zero_smul]

theorem exists_eq_of_hasEigenvector {ν : k} {u : V} (hu : f.HasEigenvector ν u) :
    ∃ i, ν = μ i := by
  obtain ⟨c, rfl⟩ := exists_eq_sum_smul hμ hv hcard u
  by_contra! hne
  apply hu.2
  refine Finset.sum_eq_zero fun j _ => ?_
  have h := mul_sub_eq_zero_of_apply_sum hμ hv hu.apply_eq_smul j
  rw [(mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr (hne j).symm), zero_smul]

theorem exists_apply_eq_smul_of_commute {g : End k V} (hg : Commute g f) (i : ι) :
    ∃ a : k, g (v i) = a • v i := by
  refine exists_eq_smul_of_apply_eq_smul hμ hv hcard i ?_
  rw [← mul_apply, ← hg.eq, mul_apply, (hv i).apply_eq_smul, map_smul]

theorem commute_of_commute_of_card_eq_finrank {g h : End k V} (hg : Commute g f)
    (hh : Commute h f) : Commute g h := by
  let b := basisOfLinearIndependentOfCardEqFinrank' v
    (f.eigenvectors_linearIndependent' μ hμ v hv) hcard
  refine b.ext fun i => ?_
  obtain ⟨a, ha⟩ := exists_apply_eq_smul_of_commute hμ hv hcard hg i
  obtain ⟨c, hc⟩ := exists_apply_eq_smul_of_commute hμ hv hcard hh i
  simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank', mul_apply, ha, hc, map_smul,
    smul_smul, mul_comm a c]

end Eigenbasis

end CFSG.UnitaryInvolutionIndex
