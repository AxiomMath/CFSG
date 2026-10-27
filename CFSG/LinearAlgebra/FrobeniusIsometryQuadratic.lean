module

public import CFSG.LinearAlgebra.FrobeniusIsometryNormalizer
public import CFSG.Assembly.LowTwoRankDefs
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.LinearAlgebra

open Module

variable {K : Type*} [Field K] [Fintype K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_mem_orthogonalGroup_conj_eq_pow_card (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {E : Subgroup (V ≃ₗ[K] V)} [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hodd : Odd (Nat.card E))
    (hEQ : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, (∀ x ∈ E, g * x * g⁻¹ = x ^ Fintype.card K) ∧
      ∀ v, (∀ x ∈ E, x v = v) → g v = v := by
  classical
  have := Fintype.ofFinite E
  have hQE : ∀ x ∈ E, ∀ v, Q (x v) = Q v := fun x hx =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hEQ hx)
  have hiso : ∀ x ∈ E, ∀ v w, QuadraticMap.polarBilin Q (x v) (x w) =
      QuadraticMap.polarBilin Q v w := fun x hx v w => by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hQE x hx]
  obtain ⟨g, hg, hconj, hfix⟩ := exists_isometry_conj_eq_pow_card (QuadraticMap.polarBilin Q)
    (fun v w => QuadraticMap.polar_comm Q v w) (fun v hv => hQ.1 v hv) hcomm hodd hiso
  have hgx : ∀ x ∈ E, ∀ v, g (x v) = (x ^ Fintype.card K) (g v) := fun x hx v => by
    have h := congrArg (fun f : V ≃ₗ[K] V => f (g v)) (hconj x hx)
    simpa using h
  have hpol : ∀ x y, Q (x + y) = Q x + Q y + QuadraticMap.polar Q x y := fun x y => by
    unfold QuadraticMap.polar
    ring
  have hgp : ∀ v w, QuadraticMap.polar Q (g v) (g w) = QuadraticMap.polar Q v w := fun v w => by
    simpa only [QuadraticMap.polarBilin_apply_apply] using hg v w
  let δ : V →+ K :=
    { toFun := fun v => Q (g v) - Q v
      map_zero' := by simp
      map_add' := fun v w => by
        simp only [map_add, hpol, hgp]
        ring }
  have hδ : ∀ v, δ v = Q (g v) - Q v := fun v => rfl
  have hδE : ∀ x ∈ E, ∀ v, δ (x v) = δ v := fun x hx v => by
    rw [hδ, hδ, hgx x hx, hQE _ (pow_mem hx _), hQE x hx]
  have hsum : ∀ v, (∑ x : E, (x : V ≃ₗ[K] V) v) + ∑ x : E, (v - (x : V ≃ₗ[K] V) v) = v := by
    intro v
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul K, FrobeniusIsometry.natCast_eq_one_of_odd hodd, one_smul,
      add_sub_cancel]
  have hfixsum : ∀ v, ∀ y ∈ E, y (∑ x : E, (x : V ≃ₗ[K] V) v) = ∑ x : E, (x : V ≃ₗ[K] V) v :=
    fun v y hy => by
      rw [map_sum]
      exact Fintype.sum_equiv (Equiv.mulLeft (⟨y, hy⟩ : E)) _ _ fun x => rfl
  refine ⟨g, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_, hconj, hfix⟩
  have h1 : δ (∑ x : E, (x : V ≃ₗ[K] V) v) = 0 := by
    rw [hδ, hfix _ (hfixsum v), sub_self]
  have h2 : ∀ x : E, δ (v - (x : V ≃ₗ[K] V) v) = 0 := fun x => by
    rw [map_sub, hδE x x.2, sub_self]
  have h0 : δ v = 0 := by
    rw [← hsum v, map_add, h1, map_sum, Finset.sum_eq_zero fun x _ => h2 x, add_zero]
  exact sub_eq_zero.mp h0

end CFSG.LinearAlgebra
