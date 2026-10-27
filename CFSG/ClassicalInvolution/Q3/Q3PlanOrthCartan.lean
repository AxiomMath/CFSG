module

public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.SpecialOrthogonal
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ClassicalInvolution.Q3

open QuadraticMap TauCeti.QuadraticMap
open scoped commutatorElement

section Commutator

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem mul_self_mem_commutator_orthogonalGroup [FiniteDimensional F V] [NeZero (2 : F)]
    (hQ : Q.Nondegenerate) {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    g * g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  let f : ↥O →* Abelianization ↥O := Abelianization.of
  have hext : f = f⁻¹ := by
    refine TauCeti.QuadraticMap.orthogonalGroup_hom_ext Q hQ fun v _ => ?_
    have h1 : f (reflectionOrthogonal Q v) * f (reflectionOrthogonal Q v) = 1 := by
      rw [← map_mul, reflectionOrthogonal_mul_self, map_one]
    rw [MonoidHom.inv_apply]
    exact (mul_eq_one_iff_eq_inv.mp h1)
  have h2 : f ⟨g, hg⟩ * f ⟨g, hg⟩ = 1 := by
    have := congrArg (fun φ : ↥O →* Abelianization ↥O => φ ⟨g, hg⟩) hext
    simp only [MonoidHom.inv_apply] at this
    exact mul_eq_one_iff_eq_inv.mpr this
  have h3 : (⟨g, hg⟩ * ⟨g, hg⟩ : ↥O) ∈ commutator ↥O := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul]
    exact h2
  rw [← Subgroup.map_subtype_commutator O]
  exact ⟨_, h3, rfl⟩

theorem mem_commutator_orthogonalGroup_of_pow_three [FiniteDimensional F V] [NeZero (2 : F)]
    (hQ : Q.Nondegenerate) {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg3 : g ^ 3 = 1) :
    g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have h2 := mul_self_mem_commutator_orthogonalGroup hQ hg
  have h4 : g * g * (g * g) = g := by
    calc g * g * (g * g) = g ^ 3 * g := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = g := by rw [hg3, one_mul]
  rw [← h4]
  exact Subgroup.mul_mem _ h2 h2

end Commutator

section Lift

variable {K G : Type*} [Group K] [Group G]

theorem exists_mem_centralizer_of_pow_three (θ : K →* G) (hker : θ.ker ≤ Subgroup.center K)
    (hker2 : ∀ c ∈ θ.ker, c * c = 1) {z : K} {g : G} (hg3 : g ^ 3 = 1) (hgr : g ∈ θ.range)
    (hcomm : g * θ z = θ z * g) : ∃ y ∈ Subgroup.centralizer ({z} : Set K), θ y = g := by
  obtain ⟨x, hx⟩ := hgr
  set y : K := x ^ 4 with hy
  have hθy : θ y = g := by
    rw [hy, map_pow, hx, show (4 : ℕ) = 3 + 1 by rfl, pow_add, hg3, one_mul, pow_one]
  have hx3 : x ^ 3 ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx, hg3]
  have hy3 : y * y * y = 1 := by
    have h := hker2 _ hx3
    calc y * y * y = (x ^ 3 * x ^ 3) * (x ^ 3 * x ^ 3) := by rw [hy]; group
      _ = 1 := by rw [h, one_mul]
  set c : K := z⁻¹ * (y * z * y⁻¹) with hcdef
  have hcker : c ∈ θ.ker := by
    rw [MonoidHom.mem_ker, hcdef, map_mul, map_inv, map_mul, map_mul, map_inv, hθy,
      show g * θ z * g⁻¹ = θ z by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one], inv_mul_cancel]
  have hcc : c * c = 1 := hker2 c hcker
  have hcz : ∀ w : K, w * c = c * w := fun w => Subgroup.mem_center_iff.mp (hker hcker) w
  have hyz : y * z * y⁻¹ = z * c := by rw [hcdef]; group
  have hyc : y * c * y⁻¹ = c := by rw [hcz y, mul_inv_cancel_right]
  have h1 : y * (z * c) * y⁻¹ = z * c * c := by
    calc y * (z * c) * y⁻¹ = (y * z * y⁻¹) * (y * c * y⁻¹) := by group
      _ = z * c * c := by rw [hyz, hyc]
  have h2 : y * (z * c * c) * y⁻¹ = z * c := by
    calc y * (z * c * c) * y⁻¹ = (y * (z * c) * y⁻¹) * (y * c * y⁻¹) := by group
      _ = z * c * c * c := by rw [h1, hyc]
      _ = z * c := by
        rw [mul_assoc z c c, hcc, mul_one]
  have h3 : z = z * c := by
    calc z = (y * y * y) * z * (y * y * y)⁻¹ := by rw [hy3]; group
      _ = y * (y * (y * z * y⁻¹) * y⁻¹) * y⁻¹ := by group
      _ = z * c := by rw [hyz, h1, h2]
  have hc1 : c = 1 := by
    have : z * c = z * 1 := by rw [mul_one]; exact h3.symm
    exact mul_left_cancel this
  refine ⟨y, ?_, hθy⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have : y * z * y⁻¹ = z := by rw [hyz, hc1, mul_one]
  exact mul_inv_eq_iff_eq_mul.mp this

end Lift

section Image

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {K : Type*}
  [Group K]

theorem mem_map_centralizer_of_pow_three [FiniteDimensional F V] [NeZero (2 : F)]
    (hQ : Q.Nondegenerate) (θ : K →* (V ≃ₗ[F] V)) (hker : θ.ker ≤ Subgroup.center K)
    (hker2 : ∀ c ∈ θ.ker, c * c = 1)
    (hrange : θ.range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) {z : K} {g : V ≃ₗ[F] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : g ^ 3 = 1)
    (hcomm : g * θ z = θ z * g) : g ∈ (Subgroup.centralizer ({z} : Set K)).map θ := by
  have hgr : g ∈ θ.range := by
    rw [hrange]
    exact mem_commutator_orthogonalGroup_of_pow_three hQ hgO hg3
  obtain ⟨y, hy, hyg⟩ := exists_mem_centralizer_of_pow_three θ hker hker2 hg3 hgr hcomm
  exact ⟨y, hy, hyg⟩

end Image

end CFSG.ClassicalInvolution.Q3
