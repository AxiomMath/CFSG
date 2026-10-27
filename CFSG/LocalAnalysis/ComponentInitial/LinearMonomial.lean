module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

section Monomial

variable {G : Type*} [CommGroup G] {r : ℕ}

@[expose] def monomialHom (M : Matrix (Fin r) (Fin r) ℤ) : (Fin r → G) →* (Fin r → G) where
  toFun t i := ∏ j, t j ^ M i j
  map_one' := by
    ext i
    simp
  map_mul' s t := by
    ext i
    simp [mul_zpow, Finset.prod_mul_distrib]

@[simp] theorem monomialHom_apply (M : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → G) (i : Fin r) :
    monomialHom M t i = ∏ j, t j ^ M i j := rfl

theorem zpow_finsetSum (a : G) {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

end Monomial

theorem index_range_toLin'_eq_natAbs_det {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ)
    (hM : M.det ≠ 0) :
    (LinearMap.range (Matrix.toLin' M)).toAddSubgroup.index = M.det.natAbs := by
  have hinj : Function.Injective (Matrix.toLin' M) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    exact hM (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, by simpa using hv⟩)
  let e := LinearEquiv.ofInjective (Matrix.toLin' M) hinj
  have h := Submodule.natAbs_det_equiv (LinearMap.range (Matrix.toLin' M)) e
  have hcomp : (LinearMap.range (Matrix.toLin' M)).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap (e : (Fin r → ℤ) →+ LinearMap.range (Matrix.toLin' M)) =
      Matrix.toLin' M := by
    ext v i
    rfl
  rw [hcomp, LinearMap.det_toLin'] at h
  exact h.symm

theorem index_range_monomialHom_dvd (K : Type*) [Field K] [Finite K] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) :
    (∀ (t : Fin r → Kˣ) (i : Fin r), monomialHom M t i = ∏ j, t j ^ M i j) ∧
      (monomialHom (G := Kˣ) M).range.index ∣ M.det.natAbs := by
  refine ⟨fun _ _ => rfl, ?_⟩
  rcases eq_or_ne M.det 0 with h0 | h0
  · rw [h0, Int.natAbs_zero]
    exact dvd_zero _
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  let ψ : (Fin r → ℤ) →+ Additive (Fin r → Kˣ) :=
    { toFun := fun n => Additive.ofMul fun i => ζ ^ n i
      map_zero' := by
        ext i
        simp
      map_add' := fun a b => by
        ext i
        simp [zpow_add] }
  have hψ : Function.Surjective ψ := by
    intro x
    choose n hn using fun i => Subgroup.mem_zpowers_iff.mp (hζ (Additive.toMul x i))
    refine ⟨n, ?_⟩
    ext i
    exact congrArg Units.val (hn i)
  let H := Subgroup.toAddSubgroup (monomialHom (G := Kˣ) M).range
  have hle : (LinearMap.range (Matrix.toLin' M)).toAddSubgroup ≤ H.comap ψ := by
    rintro _ ⟨n, rfl⟩
    refine ⟨Additive.toMul (ψ n), ?_⟩
    ext i
    simp only [monomialHom_apply, Matrix.toLin'_apply, ψ, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, toMul_ofMul, Matrix.mulVec, dotProduct]
    rw [zpow_finsetSum]
    refine congrArg Units.val (Finset.prod_congr rfl fun j _ => ?_)
    rw [← zpow_mul, mul_comm]
  have hidx : (monomialHom (G := Kˣ) M).range.index = (H.comap ψ).index := by
    rw [AddSubgroup.index_comap_of_surjective _ hψ, Subgroup.index_toAddSubgroup]
  rw [hidx, ← index_range_toLin'_eq_natAbs_det M h0]
  exact AddSubgroup.index_dvd_of_le hle

end CFSG.LocalAnalysis.ComponentInitial
