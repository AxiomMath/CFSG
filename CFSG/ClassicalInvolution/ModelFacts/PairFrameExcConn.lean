module

public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LieType.Chevalley.SignKernelStabilizer

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exists_fixed_conj {G : Type*} [Group G] (F : G →* G) {M : Subgroup G} {y d v : G}
    (hv : v * y * v⁻¹ = d) (hM : ∀ m ∈ M, m * d * m⁻¹ = d)
    (hlang : ∀ u ∈ M, ∃ m ∈ M, u = m⁻¹ * F m) (hu : F v * v⁻¹ ∈ M) :
    ∃ m ∈ M, F (m * v) = m * v ∧ (m * v) * y * (m * v)⁻¹ = d := by
  obtain ⟨m, hm, h⟩ := hlang _ (M.inv_mem hu)
  refine ⟨m, hm, ?_, ?_⟩
  · rw [map_mul]
    have h1 : F m = m * (F v * v⁻¹)⁻¹ := by rw [h]; group
    rw [h1]
    group
  · calc m * v * y * (m * v)⁻¹ = m * (v * y * v⁻¹) * m⁻¹ := by group
      _ = d := by rw [hv, hM m hm]




section Tau

variable {τ : Tag} {k : Type} [Field k]

theorem iform_eq_sum_single (θ v : Fin τ.rank → ℤ) :
    iform θ v = ∑ j, v j * iform θ (Pi.single j 1) := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

@[expose] noncomputable def thetaDiag (θ : Fin τ.rank → ℤ) (c : kˣ) : Fin τ.rank → kˣ :=
  fun i => c ^ iform θ (Pi.single i 1)

theorem rootChar_thetaDiag (θ : Fin τ.rank → ℤ) (c : kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (thetaDiag θ c) v = c ^ iform θ v := by
  rw [iform_eq_sum_single, rootChar]
  simp only [thetaDiag, ← zpow_mul]
  rw [← Finset.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm]




theorem rootChar_mul (a b : Fin τ.rank → kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootReflection_mem_kernelReflectionGroup {a : Fin τ.rank → kˣ} {σ : Fin τ.rank → ℤ}
    (hσ : σ ∈ rootCharKernel a) : rootReflection σ ∈ kernelReflectionGroup a := by
  obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 hσ.1
  rw [← hwj, ← conj_simple_eq_rootReflection]
  exact Subgroup.subset_closure ⟨w, j, hwj ▸ hσ, rfl⟩

theorem exists_unit_pow_ne_one [Infinite k] (N : ℕ) :
    ∃ c : kˣ, ∀ j : ℕ, 1 ≤ j → j ≤ N → c ^ j ≠ 1 := by
  classical
  let S : Finset k := insert 0 ((Finset.Icc 1 N).biUnion fun j =>
    (Polynomial.X ^ j - 1 : Polynomial k).roots.toFinset)
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
  have hx0 : x ≠ 0 := fun h => hx (Finset.mem_insert.2 (Or.inl h))
  refine ⟨Units.mk0 x hx0, fun j hj1 hjN h => hx ?_⟩
  refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨j, Finset.mem_Icc.2 ⟨hj1, hjN⟩, ?_⟩)
  have hne : (Polynomial.X ^ j - 1 : Polynomial k) ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.eval 0) h0
    simp [zero_pow (by omega : j ≠ 0)] at this
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  have := congrArg Units.val h
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this
  rw [this, sub_self]

theorem toralCentralizer_le_toralRootGroup (a : Fin τ.rank → kˣ)
    (h : ∀ w : WeylGroup τ, w ∈ rootCharStabilizer a → w ∈ kernelReflectionGroup a) :
    toralCentralizer τ k a ≤ toralRootGroup τ k a := by
  intro g hg
  obtain ⟨-, -, -, -, φ, hφs, hφ⟩ := Chevalley_toral_centralizer_root_generated_quotient τ k a
  obtain ⟨q, hq⟩ := hφs (QuotientGroup.mk ⟨g, hg⟩)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hw : (w : WeylGroup τ) ∈ kernelReflectionGroup a := h w w.2
  have h1 : (QuotientGroup.mk w : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hw
  rw [h1, map_one, eq_comm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
  exact hq


end Tau

end CFSG.ClassicalInvolution.ModelFacts.Levi
