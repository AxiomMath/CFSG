module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix QuadraticMap CFSG.LieType.Universal.Spin

variable {K : Type} [Field K]

@[expose] noncomputable def bilinTri (K : Type) [Field K] (a : K) :
    LinearMap.BilinForm K (Fin 3 → K) :=
  LinearMap.mk₂ K
    (fun v w => v 0 * w 0 - v 0 * w 1 + v 1 * w 1 + a * (v 2 * w 2))
    (fun v₁ v₂ w => by simp only [Pi.add_apply]; ring)
    (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun v w₁ w₂ => by simp only [Pi.add_apply]; ring)
    (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

@[expose] noncomputable def quadTri (K : Type) [Field K] (a : K) : QuadraticForm K (Fin 3 → K) :=
  (bilinTri K a).toQuadraticMap

theorem quadTri_apply (a : K) (x : Fin 3 → K) :
    quadTri K a x = x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2 + a * x 2 ^ 2 := by
  simp only [quadTri, bilinTri, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.mk₂_apply]
  ring

theorem polar_quadTri (a : K) (x y : Fin 3 → K) :
    polar (quadTri K a) x y =
      2 * x 0 * y 0 - x 0 * y 1 - y 0 * x 1 + 2 * x 1 * y 1 + 2 * a * (x 2 * y 2) := by
  rw [quadTri, LinearMap.BilinMap.polar_toQuadraticMap]
  simp only [bilinTri, LinearMap.mk₂_apply]
  ring

theorem nondegenerate_polarBilin_quadTri (hK : ringChar K ≠ 2) (h3 : (3 : K) ≠ 0) {a : K}
    (ha : a ≠ 0) : (polarBilin (quadTri K a)).Nondegenerate := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  refine nondegenerate_polarBilin_of_forall fun v hv => ?_
  have e0 := hv (Pi.single 0 1)
  have e1 := hv (Pi.single 1 1)
  have e2 := hv (Pi.single 2 1)
  simp [polar_quadTri] at e0 e1 e2
  have hv2 : v 2 = 0 := by
    rcases e2 with (h | h) | h
    · exact absurd h h2
    · exact absurd h ha
    · exact h
  have hv0 : v 0 = 0 := by
    have : (3 : K) * v 0 = 0 := by linear_combination 2 * e0 + e1
    exact (mul_eq_zero.mp this).resolve_left h3
  have hv1 : v 1 = 0 := by
    have : (2 : K) * v 1 = 0 := by linear_combination e1 + hv0
    exact (mul_eq_zero.mp this).resolve_left h2
  funext i
  fin_cases i <;> simp [hv0, hv1, hv2]

private theorem natCard_orthogonalGroup_quadTri [Finite K] (hK : ringChar K ≠ 2) (h3 : (3 : K) ≠ 0)
    {a : K} (ha : a ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadTri K a)) =
      2 * Nat.card K * (Nat.card K ^ 2 - 1) := by
  have hQ := nondegenerate_polarBilin_quadTri hK h3 ha
  have hdim : Module.finrank K (Fin 3 → K) = 2 * 1 + 1 := by
    rw [Module.finrank_fin_fun]
  have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := K)
    (V := Fin 3 → K) hK hQ hdim
  simp only [pow_one, one_pow, Finset.Icc_self, Finset.prod_singleton] at hcard
  have hq : 1 ≤ Nat.card K ^ 2 :=
    one_le_pow₀ (le_of_lt (Finite.one_lt_card (α := K)))
  have hcast : ((2 * Nat.card K * (Nat.card K ^ 2 - 1) : ℕ) : ℤ) =
      2 * (Nat.card K : ℤ) * ((Nat.card K : ℤ) ^ 2 - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hq, Nat.cast_pow]
    norm_num
  rw [← hcast] at hcard
  exact_mod_cast hcard

theorem exists_isometry_orderOf_eq_quadTri [Finite K] (hK : ringChar K ≠ 2) (h3 : (3 : K) ≠ 0)
    {a : K} (ha : a ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hdvd : ℓ ∣ Nat.card K * (Nat.card K ^ 2 - 1)) :
    ∃ M : Matrix.GeneralLinearGroup (Fin 3) K,
      (∀ x : Fin 3 → K, quadTri K a ((M : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = quadTri K a x) ∧
        orderOf M = ℓ := by
  have hcard := natCard_orthogonalGroup_quadTri hK h3 ha
  have hdvdG : ℓ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadTri K a)) := by
    rw [hcard]
    simpa only [mul_assoc] using dvd_mul_of_dvd_right hdvd 2
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Finite (TauCeti.QuadraticMap.orthogonalGroup (quadTri K a)) :=
    Finite.of_injective (TauCeti.QuadraticMap.orthogonalToGeneralLinear (quadTri K a))
      (TauCeti.QuadraticMap.orthogonalToGeneralLinear_injective (quadTri K a))
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := TauCeti.QuadraticMap.orthogonalGroup (quadTri K a)) ℓ hdvdG
  refine ⟨TauCeti.QuadraticMap.orthogonalToGeneralLinear (quadTri K a) g, ?_, ?_⟩
  · intro x
    rw [TauCeti.QuadraticMap.coe_orthogonalToGeneralLinear, LinearMap.toMatrix'_mulVec]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2 x
  · rw [orderOf_injective (TauCeti.QuadraticMap.orthogonalToGeneralLinear (quadTri K a))
      (TauCeti.QuadraticMap.orthogonalToGeneralLinear_injective (quadTri K a)) g, hg]

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
