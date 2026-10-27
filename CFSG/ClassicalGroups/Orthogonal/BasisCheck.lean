module

public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem quad_apply_eq_of_basis (Q : QuadraticForm K (ι → K)) (f : (ι → K) →ₗ[K] (ι → K))
    (h1 : ∀ i, Q (f (Pi.single i 1)) = Q (Pi.single i 1))
    (h2 : ∀ i j, polar Q (f (Pi.single i 1)) (f (Pi.single j 1)) =
      polar Q (Pi.single i 1) (Pi.single j 1)) (v : ι → K) : Q (f v) = Q v := by
  set D : QuadraticMap K (ι → K) K := Q.comp f - Q with hD
  have hDapp : ∀ x, D x = Q (f x) - Q x := fun x => by
    simp [hD, QuadraticMap.comp_apply]
  have hpolarDef : ∀ x y, polar D x y = polar Q (f x) (f y) - polar Q x y := fun x y => by
    simp only [polar, hDapp, map_add]
    ring
  have hpolar : ∀ x y, polar D x y = 0 := by
    have hB : polarBilin D = 0 := by
      refine (Pi.basisFun K ι).ext fun i => (Pi.basisFun K ι).ext fun j => ?_
      simp only [Pi.basisFun_apply, LinearMap.zero_apply, polarBilin_apply_apply]
      rw [hpolarDef, h2 i j, sub_self]
    intro x y
    have := congrArg (fun B : LinearMap.BilinMap K (ι → K) K => B x y) hB
    simpa using this
  let Dh : (ι → K) →+ K :=
    { toFun := D
      map_zero' := QuadraticMap.map_zero D
      map_add' := fun x y => by rw [QuadraticMap.map_add D, hpolar, add_zero] }
  have hDh : ∀ x, Dh x = D x := fun x => rfl
  have hv : v = ∑ i, v i • (Pi.single i 1 : ι → K) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hD0 : D v = 0 := by
    rw [← hDh, hv, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hDh, QuadraticMap.map_smul, hDapp, h1 i, sub_self, smul_zero]
  have := hDapp v
  rw [hD0] at this
  exact sub_eq_zero.mp this.symm

theorem mem_orthogonalGroup_of_basis (Q : QuadraticForm K (ι → K))
    (g : (ι → K) ≃ₗ[K] (ι → K))
    (h1 : ∀ i, Q (g (Pi.single i 1)) = Q (Pi.single i 1))
    (h2 : ∀ i j, polar Q (g (Pi.single i 1)) (g (Pi.single j 1)) =
      polar Q (Pi.single i 1) (Pi.single j 1)) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (quad_apply_eq_of_basis Q g.toLinearMap h1 h2)

end CFSG.ClassicalGroups.Orthogonal
