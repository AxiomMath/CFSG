module

public import CFSG.LinearAlgebra.CoprimeActions.PermutationFunctionFixedDimension
public import CFSG.LinearAlgebra.CoprimeActions.DistinctEigenspaceCommutantDimension

public section

namespace CFSG.LinearAlgebra.CoprimeActions.BasisPermutationCommutantDimension

open Module

variable {F V I : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [Finite I]

theorem finrank_eq (b : Basis I F (Module.End F V)) (T : V ≃ₗ[F] V) (σ : Equiv.Perm I)
    (hb : ∀ i, T.toLinearMap ∘ₗ b i ∘ₗ T.symm.toLinearMap = b (σ i)) :
    finrank F (DistinctEigenspaceCommutantDimension.commutant T.toLinearMap) =
      finrank F (PermutationFunctionFixedDimension.fixedSpace F σ) := by
  classical
  haveI := Fintype.ofFinite I
  set c : Module.End F V → Module.End F V := fun S => T.toLinearMap ∘ₗ S ∘ₗ T.symm.toLinearMap
    with hcdef
  have hcadd : ∀ S R, c (S + R) = c S + c R := by
    intro S R; ext v; simp [hcdef]
  have hcsmul : ∀ (a : F) S, c (a • S) = a • c S := by
    intro a S; ext v; simp [hcdef]
  have hc : ∀ (S : Module.End F V) i, b.equivFun (c S) (σ i) = b.equivFun S i := by
    intro S i
    have hS : c S = ∑ k, b.equivFun S k • b (σ k) := by
      conv_lhs => rw [← b.sum_equivFun S]
      have : c (∑ k, b.equivFun S k • b k) = ∑ k, c (b.equivFun S k • b k) := by
        exact map_sum (AddMonoidHom.mk' c hcadd) _ _
      rw [this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcsmul, ← hb k]
    rw [hS]
    simp [Finsupp.single_apply, Equiv.apply_eq_iff_eq]
  have hmem : ∀ S : Module.End F V, S ∈ DistinctEigenspaceCommutantDimension.commutant T.toLinearMap ↔
      b.equivFun S ∈ PermutationFunctionFixedDimension.fixedSpace F σ := by
    intro S
    rw [DistinctEigenspaceCommutantDimension.mem_commutant]
    have h1 : S.comp T.toLinearMap = T.toLinearMap.comp S ↔ c S = S := by
      constructor
      · intro h
        ext v
        simp only [hcdef, LinearMap.comp_apply]
        have := LinearMap.congr_fun h (T.symm v)
        simp at this
        simp [this]
      · intro h
        ext v
        have := LinearMap.congr_fun h (T v)
        simp [hcdef] at this
        simp [this]
    rw [h1]
    constructor
    · intro h x
      have := hc S x
      rw [h] at this
      exact this
    · intro h
      apply b.equivFun.injective
      funext j
      obtain ⟨i, rfl⟩ := σ.surjective j
      rw [hc]
      exact (h i).symm
  have : DistinctEigenspaceCommutantDimension.commutant T.toLinearMap =
      (PermutationFunctionFixedDimension.fixedSpace F σ).comap b.equivFun.toLinearMap := by
    ext S; exact hmem S
  rw [this, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

theorem prime_formula (b : Basis I F (Module.End F V)) (T : V ≃ₗ[F] V) (σ : Equiv.Perm I)
    (hb : ∀ i, T.toLinearMap ∘ₗ b i ∘ₗ T.symm.toLinearMap = b (σ i))
    (r : ℕ) (hr : r.Prime) (hσ : σ ^ r = 1) (i0 : I) (hfix : ∀ i, σ i = i ↔ i = i0) :
    r * finrank F (DistinctEigenspaceCommutantDimension.commutant T.toLinearMap) =
      finrank F V ^ 2 + r - 1 := by
  haveI := Fintype.ofFinite I
  rw [finrank_eq b T σ hb,
    PermutationFunctionFixedDimension.prime_semiregular_formula σ r hr hσ i0 hfix]
  have h1 : Nat.card I = finrank F V ^ 2 := by
    rw [Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis b, Module.finrank_linearMap F F V V,
      sq]
  rw [h1]

end CFSG.LinearAlgebra.CoprimeActions.BasisPermutationCommutantDimension
