module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Embed
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Models

variable {K K' V : Type} [Field K] [Field K'] [Algebra K K'] {σ : K' ≃+* K'} [AddCommGroup V]
  [Module K V] {Q : QuadraticForm K V}

namespace UnitaryEmbedding

variable (D : UnitaryEmbedding Q σ)

theorem polar_incl (hσ : ∀ c, σ (σ c) = c) (x y : Fin 3 → K') :
    algebraMap K K' (polar Q (D.incl x) (D.incl y)) = herm σ x y + σ (herm σ x y) := by
  have h := D.Q_incl (x + y)
  rw [map_add, QuadraticMap.map_add Q, map_add, map_add, D.Q_incl, D.Q_incl] at h
  rw [herm_add_left, herm_add_right, herm_add_right, herm_conj σ hσ x y] at h
  linear_combination h

theorem Q_incl_eq_zero {x : Fin 3 → K'} (hx : herm σ x x = 0) : Q (D.incl x) = 0 := by
  apply (algebraMap K K').injective
  rw [D.Q_incl, hx, map_zero]

theorem incl_algebraMap_smul (t : K) (v : Fin 3 → K') :
    D.incl (algebraMap K K' t • v) = t • D.incl v := by
  rw [algebraMap_smul, map_smul]

theorem polar_left_eq (x : V) (y : Fin 3 → K') :
    polar Q x (D.incl y) = polar Q (D.incl (D.coords x)) (D.incl y) := by
  rw [polar_comm, D.polar_coords y x, polar_comm]

theorem theta_tv (hσ : ∀ c, σ (σ c) = c) {a : Fin 3 → K'} (ha : herm σ a a = 0) (l m : K')
    (hc : (σ l * m - σ m * l) + σ (σ l * m - σ m * l) = 0) :
    D.theta (tv hσ ha hc) = eichler Q (D.incl (l • a)) (D.incl (m • a)) := by
  have hla : herm σ (l • a) (l • a) = 0 := by rw [herm_smul_left, herm_smul_right, ha]; ring
  have hma : herm σ (m • a) (m • a) = 0 := by rw [herm_smul_left, herm_smul_right, ha]; ring
  have hlm : herm σ (l • a) (m • a) = 0 := by rw [herm_smul_left, herm_smul_right, ha]; ring
  have hu : Q (D.incl (l • a)) = 0 := D.Q_incl_eq_zero hla
  have hw0 : Q (D.incl (m • a)) = 0 := D.Q_incl_eq_zero hma
  have hw : polar Q (D.incl (l • a)) (D.incl (m • a)) = 0 := by
    apply (algebraMap K K').injective
    rw [D.polar_incl hσ, hlm, map_zero, map_zero, add_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hu hw, theta_apply, tv_smul, hw0, zero_mul, add_zero]
  set z := D.coords x with hz
  have hpol : ∀ n : K', algebraMap K K' (polar Q x (D.incl (n • a))) =
      n * herm σ z a + σ n * herm σ a z := by
    intro n
    rw [D.polar_left_eq, D.polar_incl hσ, herm_smul_right, map_mul, ← herm_conj σ hσ z a]
  rw [← D.incl_algebraMap_smul, ← D.incl_algebraMap_smul, add_sub_cancel_left]
  have key : D.incl (((σ l * m - σ m * l) * herm σ a z) • a) =
      D.incl (algebraMap K K' (polar Q x (D.incl (l • a))) • m • a) -
        D.incl (algebraMap K K' (polar Q x (D.incl (m • a))) • l • a) := by
    rw [← map_sub, hpol, hpol]
    congr 1
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [key]
  abel

end UnitaryEmbedding

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
