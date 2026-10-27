module

public import CFSG.LieType.Chevalley.RootIntClosure

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {n : ℕ}

theorem gram_eq_mul (D D' : Fin n → Fin τ.rank → ℤ) (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ i, D i = ∑ j, M i j • D' j) :
    (Matrix.of fun i j => iform (D i) (D j)) =
      M * (Matrix.of fun i j => iform (D' i) (D' j)) * M.transpose := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hM,
    iform_finset_sum_left, iform_finset_sum_right, iform_smul_left, iform_smul_right,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem det_gram_eq_det_sq_mul (D D' : Fin n → Fin τ.rank → ℤ) (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ i, D i = ∑ j, M i j • D' j) :
    (Matrix.of fun i j => iform (D i) (D j)).det =
      M.det ^ 2 * (Matrix.of fun i j => iform (D' i) (D' j)).det := by
  rw [gram_eq_mul D D' M hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem det_smul_eq_sum_adjugate (D D' : Fin n → Fin τ.rank → ℤ) (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ i, D i = ∑ j, M i j • D' j) (j : Fin n) :
    M.det • D' j = ∑ i, M.adjugate j i • D i := by
  have h := congrFun (congrFun (Matrix.adjugate_mul M) j)
  simp only [hM, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have e : ∀ k, ∑ i, (M.adjugate j i * M i k) • D' k = (M.det • (1 : Matrix (Fin n) (Fin n) ℤ)) j k • D' k :=
    fun k => by rw [← Finset.sum_smul, ← h k, Matrix.mul_apply]
  simp only [e, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem exists_simpleRoots_coeff {Ψ Ψ' : Set (Fin τ.rank → ℤ)} (hΨ' : IsRootComponent Ψ')
    (hsub : Ψ ⊆ Ψ') (e : simpleRoots Ψ ≃ Fin n) (e' : simpleRoots Ψ' ≃ Fin n) :
    ∃ M : Matrix (Fin n) (Fin n) ℤ, ∀ i,
      ((e.symm i : simpleRoots Ψ) : Fin τ.rank → ℤ) =
        ∑ j, M i j • ((e'.symm j : simpleRoots Ψ') : Fin τ.rank → ℤ) := by
  classical
  have hc : ∀ i : Fin n, ∃ c : (Fin τ.rank → ℤ) → ℤ,
      ((e.symm i : simpleRoots Ψ) : Fin τ.rank → ℤ) = ∑ β ∈ simpleRoots Ψ', c β • β :=
    fun i => exists_coords hΨ' (hsub (simpleRoots_subset (e.symm i).2))
  choose c hc using hc
  refine ⟨fun i j => c i (e'.symm j), fun i => ?_⟩
  rw [hc i, ← Finset.sum_coe_sort (simpleRoots Ψ')]
  exact (Equiv.sum_comp e'.symm fun β => c i β • (β : Fin τ.rank → ℤ)).symm

theorem subset_of_isUnit_det (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ Ψ' : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hΨ' : IsRootComponent Ψ')
    (e : simpleRoots Ψ ≃ Fin n) (e' : simpleRoots Ψ' ≃ Fin n) (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ i, ((e.symm i : simpleRoots Ψ) : Fin τ.rank → ℤ) =
      ∑ j, M i j • ((e'.symm j : simpleRoots Ψ') : Fin τ.rank → ℤ))
    (hu : M.det = 1 ∨ M.det = -1) : Ψ' ⊆ Ψ := by
  classical
  set D : Fin n → Fin τ.rank → ℤ := fun i => ((e.symm i : simpleRoots Ψ) : Fin τ.rank → ℤ)
  set D' : Fin n → Fin τ.rank → ℤ := fun j => ((e'.symm j : simpleRoots Ψ') : Fin τ.rank → ℤ)
  have hDmem : ∀ i, D i ∈ AddSubgroup.closure Ψ := fun i =>
    AddSubgroup.subset_closure (simpleRoots_subset (e.symm i).2)
  have hD' : ∀ j, D' j ∈ AddSubgroup.closure Ψ := by
    intro j
    have h := det_smul_eq_sum_adjugate D D' M hM j
    have hs : M.det • D' j ∈ AddSubgroup.closure Ψ := by
      rw [h]
      exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (hDmem i) _
    rcases hu with hu | hu
    · rwa [hu, one_smul] at hs
    · rw [hu, neg_one_smul] at hs
      simpa using AddSubgroup.neg_mem _ hs
  intro β hβ
  obtain ⟨c, hc⟩ := exists_coords hΨ' hβ
  have hmem : β ∈ AddSubgroup.closure Ψ := by
    rw [hc, ← Finset.sum_coe_sort (simpleRoots Ψ')]
    refine AddSubgroup.sum_mem _ fun γ _ => AddSubgroup.zsmul_mem _ ?_ _
    have := hD' (e' γ)
    simpa [D'] using this
  exact mem_of_isRoot_mem_addClosure hτ hΨ.isRoot hΨ.neg_mem hΨ.add_mem (hΨ'.isRoot β hβ) hmem

end CFSG.LieType.Chevalley
