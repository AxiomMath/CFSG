module

public import CFSG.HardMathSupport.GuralnickMalle.ElemAbelianTwo
public import CFSG.HardMathSupport.GuralnickMalle.CyclicTwoBounds

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module
open scoped TensorProduct

variable {K : Type*} [Field K] [CharP K 2]

theorem mapsTo_iterFixed {V : Type*} [AddCommGroup V] [Module K V] {r : ℕ}
    (T : Fin r → V ≃ₗ[K] V) (hc : ∀ a b, T a * T b = T b * T a)
    (j : Fin r) {i : ℕ} : ∀ v ∈ iterFixed T i, (T j : V →ₗ[K] V) v ∈ iterFixed T i := by
  intro v hv
  rw [mem_iterFixed] at hv ⊢
  intro k hk
  calc T k (T j v) = (T k * T j) v := rfl
    _ = (T j * T k) v := by rw [hc k j]
    _ = T j (T k v) := rfl
    _ = T j v := by rw [hv k hk]

theorem finrank_iterFixed_le_two_mul_succ {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {r : ℕ} (T : Fin r → V ≃ₗ[K] V)
    (hT2 : ∀ i, T i * T i = 1) (hTc : ∀ i j, T i * T j = T j * T i) {i : ℕ} (hi : i < r) :
    Module.finrank K (iterFixed T i) ≤ 2 * Module.finrank K (iterFixed T (i + 1)) := by
  let A : Submodule K V := iterFixed T i
  have hA : ∀ v ∈ A, (T ⟨i, hi⟩ : V →ₗ[K] V) v ∈ A := by
    intro v hv
    exact mapsTo_iterFixed T hTc ⟨i, hi⟩ v hv
  have hS : ((T ⟨i, hi⟩ : V →ₗ[K] V).restrict hA).comp
      ((T ⟨i, hi⟩ : V →ₗ[K] V).restrict hA) = 1 := by
    apply restrict_comp_self
    simpa [Module.End.mul_eq_comp, Module.End.one_eq_id] using
      congrArg (fun e : V ≃ₗ[K] V => (e : V →ₗ[K] V)) (hT2 ⟨i, hi⟩)
  have h := finrank_le_two_mul_finrank_ker_sub_one
    ((T ⟨i, hi⟩ : V →ₗ[K] V).restrict hA) hS
  have hker : Module.finrank K
      (LinearMap.ker (((T ⟨i, hi⟩ : V →ₗ[K] V).restrict hA) - 1)) =
      Module.finrank K (iterFixed T (i + 1)) := by
    have h' := finrank_ker_restrict_sub_one
      (f := (T ⟨i, hi⟩ : V →ₗ[K] V)) (A := A) hA
    rw [show A ⊓ LinearMap.ker ((T ⟨i, hi⟩ : V →ₗ[K] V) - 1) = iterFixed T (i + 1) from
      (iterFixed_succ (T := T) hi).symm] at h'
    exact h'
  rw [hker] at h
  change Module.finrank K A ≤ 2 * Module.finrank K (iterFixed T (i + 1))
  exact h

end CFSG.HardMathSupport.GuralnickMalle
