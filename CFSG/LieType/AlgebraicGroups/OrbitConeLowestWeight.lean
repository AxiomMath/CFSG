module

public import CFSG.LieType.AlgebraicGroups.NormalizerFixedScalar

public noncomputable section

open WithConv TauCeti.Comodule CFSG.LieType.AlgebraicGroups.ClosedCone
open CFSG.LieType.AlgebraicGroups.NormalizerFixedScalar

namespace CFSG.LieType.AlgebraicGroups.OrbitConeLowestWeight

universe u

variable {k : Type u} [Field k] {M : Type u} [CommRing M] [HopfAlgebra k M]
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]

variable (W) in
@[expose] def weightProj (μ : M →ₐc[k] LaurentPolynomial k) (m : Multiplicative ℤ) :
    W →ₗ[k] W :=
  letI := TauCeti.Comodule.Corestrict (M := W)
    (weightCoordinate μ : M →ₗc[k] _root_.MonoidAlgebra k (Multiplicative ℤ))
  TauCeti.Comodule.weightProj k (Multiplicative ℤ) W m

theorem mem_weightSpace_iff_mem_corestrict (μ : M →ₐc[k] LaurentPolynomial k)
    (m : Multiplicative ℤ) (v : W) :
    v ∈ weightSpace W μ m ↔
      v ∈ @TauCeti.Comodule.weightSpace k (Multiplicative ℤ) W _ _ _
        (TauCeti.Comodule.Corestrict (M := W)
          (weightCoordinate μ : M →ₗc[k] _root_.MonoidAlgebra k (Multiplicative ℤ))) m := by
  let := TauCeti.Comodule.Corestrict (M := W)
    (weightCoordinate μ : M →ₗc[k] _root_.MonoidAlgebra k (Multiplicative ℤ))
  rw [TauCeti.Comodule.mem_weightSpace, TauCeti.Comodule.corestrict_coact_apply,
    TauCeti.DiagonalizableGroup.mem_weightSpace]

theorem weightProj_of_mem (μ : M →ₐc[k] LaurentPolynomial k) {m : Multiplicative ℤ} {v : W}
    (hv : v ∈ weightSpace W μ m) : weightProj W μ m v = v :=
  letI := TauCeti.Comodule.Corestrict (M := W)
    (weightCoordinate μ : M →ₗc[k] _root_.MonoidAlgebra k (Multiplicative ℤ))
  TauCeti.Comodule.weightProj_of_mem (R := k) ((mem_weightSpace_iff_mem_corestrict μ m v).mp hv)

theorem weightProj_of_mem_of_ne (μ : M →ₐc[k] LaurentPolynomial k) {m m' : Multiplicative ℤ}
    (hne : m' ≠ m) {v : W} (hv : v ∈ weightSpace W μ m) : weightProj W μ m' v = 0 :=
  letI := TauCeti.Comodule.Corestrict (M := W)
    (weightCoordinate μ : M →ₗc[k] _root_.MonoidAlgebra k (Multiplicative ℤ))
  TauCeti.Comodule.weightProj_of_mem_of_ne (R := k) hne
    ((mem_weightSpace_iff_mem_corestrict μ m v).mp hv)

theorem weightProj_finsupp_sum (μ : M →ₐc[k] LaurentPolynomial k) {f : Multiplicative ℤ →₀ W}
    (hf : ∀ m, f m ∈ weightSpace W μ m) (m : Multiplicative ℤ) :
    weightProj W μ m (f.sum fun _ x => x) = f m := by
  classical
  rw [Finsupp.sum, map_sum]
  by_cases hm : m ∈ f.support
  · rw [Finset.sum_eq_single m (fun b _ hb => weightProj_of_mem_of_ne μ (Ne.symm hb) (hf b))
      (fun h => absurd hm h), weightProj_of_mem μ (hf m)]
  · rw [Finset.sum_eq_zero fun b hb => weightProj_of_mem_of_ne μ
      (by rintro rfl; exact hm hb) (hf b)]
    exact (Finsupp.notMem_support_iff.mp hm).symm

end CFSG.LieType.AlgebraicGroups.OrbitConeLowestWeight
