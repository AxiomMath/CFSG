module

public import CFSG.LinearAlgebra.CoordinateSemilinearMatrixAction
public import CFSG.LinearAlgebra.CyclicIrreducibleNormalizer

public noncomputable section

namespace CFSG.LinearAlgebra

open Matrix CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.PartOne.KCLinComm

variable {n : ℕ} {K : Type} [Field K]

@[expose] def algEquivToRingAut (K A : Type*) [CommSemiring K] [Semiring A] [Algebra K A] :
    (A ≃ₐ[K] A) →* RingAut A where
  toFun e := e.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem algEquivToRingAut_injective (K A : Type*) [CommSemiring K] [Semiring A] [Algebra K A] :
    Function.Injective (algEquivToRingAut K A) := by
  intro e f h
  exact AlgEquiv.toRingEquiv_injective h

theorem coordinateSemilinearAct_mem_commutant (g : coordinateSemilinearGroup n K)
    {U : Subgroup (GL (Fin n) K)}
    (hUinv : ∀ u ∈ U, coordinateSemilinearGLAct n K g⁻¹ u ∈ U)
    {X : Matrix (Fin n) (Fin n) K} (hX : X ∈ commutant U) :
    coordinateSemilinearAct n K g X ∈ commutant U := by
  rw [mem_commutant] at hX ⊢
  intro u hu
  let v : GL (Fin n) K := coordinateSemilinearGLAct n K g⁻¹ u
  have hv : v ∈ U := hUinv u hu
  have hvmat : (v : Matrix (Fin n) (Fin n) K) =
      coordinateSemilinearAct n K g⁻¹ (u : Matrix (Fin n) (Fin n) K) :=
    coe_coordinateSemilinearGLAct n K g⁻¹ u
  have hgv : coordinateSemilinearAct n K g (v : Matrix (Fin n) (Fin n) K) =
      (u : Matrix (Fin n) (Fin n) K) := by
    rw [hvmat, ← RingAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      RingAut.one_apply]
  calc
    (u : Matrix (Fin n) (Fin n) K) * coordinateSemilinearAct n K g X
        = coordinateSemilinearAct n K g (v : Matrix (Fin n) (Fin n) K) *
            coordinateSemilinearAct n K g X := by rw [hgv]
    _ = coordinateSemilinearAct n K g
          ((v : Matrix (Fin n) (Fin n) K) * X) := by rw [map_mul]
    _ = coordinateSemilinearAct n K g
          (X * (v : Matrix (Fin n) (Fin n) K)) := by rw [(hX v hv).symm]
    _ = coordinateSemilinearAct n K g X *
          coordinateSemilinearAct n K g (v : Matrix (Fin n) (Fin n) K) := by rw [map_mul]
    _ = coordinateSemilinearAct n K g X * (u : Matrix (Fin n) (Fin n) K) := by rw [hgv]

theorem coordinateSemilinearAct_mem_commutant_iff (g : coordinateSemilinearGroup n K)
    {U : Subgroup (GL (Fin n) K)}
    (hU : ∀ u ∈ U, coordinateSemilinearGLAct n K g u ∈ U)
    (hUinv : ∀ u ∈ U, coordinateSemilinearGLAct n K g⁻¹ u ∈ U)
    {X : Matrix (Fin n) (Fin n) K} :
    X ∈ commutant U ↔ coordinateSemilinearAct n K g X ∈ commutant U := by
  constructor
  · exact coordinateSemilinearAct_mem_commutant g hUinv
  · intro hX
    have hmem := coordinateSemilinearAct_mem_commutant g⁻¹ (by simpa using hU) hX
    have hcomp : coordinateSemilinearAct n K g⁻¹ (coordinateSemilinearAct n K g X) = X := by
      rw [← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, RingAut.one_apply]
    rwa [hcomp] at hmem

@[expose] noncomputable def semilinearCommutantRingAut {A : Type*} [Group A]
    (rho : A →* coordinateSemilinearGroup n K) (U : Subgroup (GL (Fin n) K))
    (hU : ∀ a : A, ∀ u ∈ U, coordinateSemilinearGLAct n K (rho a) u ∈ U) (a : A) :
    RingAut (commutant U) :=
  (coordinateSemilinearAct n K (rho a)).restrict (commutant U) (commutant U)
    (fun _ => coordinateSemilinearAct_mem_commutant_iff (rho a) (hU a)
      (by
        intro u hu
        have h := hU a⁻¹ u hu
        rwa [map_inv] at h))

@[expose] noncomputable def semilinearCommutantAction {A : Type*} [Group A]
    (rho : A →* coordinateSemilinearGroup n K) (U : Subgroup (GL (Fin n) K))
    (hU : ∀ a : A, ∀ u ∈ U, coordinateSemilinearGLAct n K (rho a) u ∈ U) :
    A →* RingAut (commutant U) where
  toFun a := semilinearCommutantRingAut rho U hU a
  map_one' := by
    apply RingEquiv.ext
    intro X
    apply Subtype.ext
    change coordinateSemilinearAct n K (rho 1) (X : Matrix (Fin n) (Fin n) K) =
      (X : Matrix (Fin n) (Fin n) K)
    rw [map_one rho, map_one (coordinateSemilinearAct n K), RingAut.one_apply]
  map_mul' a b := by
    apply RingEquiv.ext
    intro X
    apply Subtype.ext
    change coordinateSemilinearAct n K (rho (a * b)) (X : Matrix (Fin n) (Fin n) K) =
      coordinateSemilinearAct n K (rho a)
        (coordinateSemilinearAct n K (rho b) (X : Matrix (Fin n) (Fin n) K))
    rw [map_mul rho, map_mul (coordinateSemilinearAct n K), RingAut.mul_apply]

@[simp]
theorem semilinearCommutantAction_coe_apply {A : Type*} [Group A]
    (rho : A →* coordinateSemilinearGroup n K) (U : Subgroup (GL (Fin n) K))
    (hU : ∀ a : A, ∀ u ∈ U, coordinateSemilinearGLAct n K (rho a) u ∈ U)
    (a : A) (X : commutant U) :
    ((semilinearCommutantAction rho U hU a X : commutant U) :
        Matrix (Fin n) (Fin n) K) =
      coordinateSemilinearAct n K (rho a) (X : Matrix (Fin n) (Fin n) K) := rfl

theorem tau_range_normalizes {A : Type*} [Group A]
    (rho : A →* coordinateSemilinearGroup n K) (U : Subgroup (GL (Fin n) K))
    (hU : ∀ a : A, ∀ u ∈ U, coordinateSemilinearGLAct n K (rho a) u ∈ U)
    (tau : (SemidirectProduct.rightHom.comp rho).ker →* GL (Fin n) K)
    (htau : ∀ j : (SemidirectProduct.rightHom.comp rho).ker,
      rho (j : A) = SemidirectProduct.inl (tau j)) :
    ∀ g ∈ tau.range, ∀ x ∈ U, g * x * g⁻¹ ∈ U := by
  rintro g ⟨j, rfl⟩ x hx
  have h := hU (j : A) x hx
  rwa [htau j, coordinateSemilinearGLAct_inl] at h

@[expose] noncomputable def linearKernelCommutantAction {A : Type*} [Group A]
    (rho : A →* coordinateSemilinearGroup n K) (U : Subgroup (GL (Fin n) K))
    (hU : ∀ a : A, ∀ u ∈ U, coordinateSemilinearGLAct n K (rho a) u ∈ U)
    (tau : (SemidirectProduct.rightHom.comp rho).ker →* GL (Fin n) K)
    (htau : ∀ j : (SemidirectProduct.rightHom.comp rho).ker,
      rho (j : A) = SemidirectProduct.inl (tau j)) :
    (SemidirectProduct.rightHom.comp rho).ker →*
      (commutant U ≃ₐ[K] commutant U) :=
  (cyclicCommutantAction (G := tau.range) (H := U)
      (tau_range_normalizes rho U hU tau htau)).comp tau.rangeRestrict

theorem semilinearCommutantAction_comp_linearKernel_eq {A : Type*} [Group A]
    (rho : A →* coordinateSemilinearGroup n K) (U : Subgroup (GL (Fin n) K))
    (hU : ∀ a : A, ∀ u ∈ U, coordinateSemilinearGLAct n K (rho a) u ∈ U)
    (tau : (SemidirectProduct.rightHom.comp rho).ker →* GL (Fin n) K)
    (htau : ∀ j : (SemidirectProduct.rightHom.comp rho).ker,
      rho (j : A) = SemidirectProduct.inl (tau j)) :
    (semilinearCommutantAction rho U hU).comp
        (SemidirectProduct.rightHom.comp rho).ker.subtype =
      (algEquivToRingAut K (commutant U)).comp
        (linearKernelCommutantAction rho U hU tau htau) := by
  apply MonoidHom.ext
  intro j
  apply RingEquiv.ext
  intro X
  apply Subtype.ext
  change ((semilinearCommutantAction rho U hU (j : A) X : commutant U) :
      Matrix (Fin n) (Fin n) K) =
    ((cyclicCommutantAction (G := tau.range) (H := U)
      (tau_range_normalizes rho U hU tau htau) (tau.rangeRestrict j) X : commutant U) :
        Matrix (Fin n) (Fin n) K)
  rw [semilinearCommutantAction_coe_apply, htau j, coordinateSemilinearAct_inl,
    conjRingAut_apply, cyclicCommutantAction_apply_coe, ← Matrix.coe_units_inv]
  rw [show ((tau.rangeRestrict j : tau.range) : GL (Fin n) K) = tau j from rfl]

theorem linearKernel_semilinearCommutantAction_eq [Finite K] (hn : n.Prime)
    {A : Type*} [Group A]
    (rho : A →* coordinateSemilinearGroup n K) (U : Subgroup (GL (Fin n) K))
    (hU : ∀ a : A, ∀ u ∈ U, coordinateSemilinearGLAct n K (rho a) u ∈ U)
    (hUcyc : IsCyclic U) (hUirr : IsIrreducibleMatrixRep U.subtype)
    (tau : (SemidirectProduct.rightHom.comp rho).ker →* GL (Fin n) K)
    (htau : ∀ j : (SemidirectProduct.rightHom.comp rho).ker,
      rho (j : A) = SemidirectProduct.inl (tau j)) :
    ((semilinearCommutantAction rho U hU).comp
        (SemidirectProduct.rightHom.comp rho).ker.subtype).ker =
      (Subgroup.centralizer (U : Set (GL (Fin n) K))).comap tau := by
  classical
  let hUnorm := tau_range_normalizes rho U hU tau htau
  let ψ := linearKernelCommutantAction rho U hU tau htau
  have hfact := semilinearCommutantAction_comp_linearKernel_eq rho U hU tau htau
  have hkerψ : ψ.ker =
      (Subgroup.centralizer (U : Set (GL (Fin n) K))).comap tau := by
    ext j
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    change cyclicCommutantAction (G := tau.range) (H := U) hUnorm
        (tau.rangeRestrict j) = 1 ↔
      tau j ∈ Subgroup.centralizer (U : Set (GL (Fin n) K))
    rw [← MonoidHom.mem_ker, cyclicCommutantAction_ker_eq hn hUcyc hUirr hUnorm,
      Subgroup.mem_subgroupOf]
    rfl
  have hkerRing : ((algEquivToRingAut K (commutant U)).comp ψ).ker = ψ.ker := by
    ext j
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h
      apply algEquivToRingAut_injective K (commutant U)
      simpa using h
    · intro h
      rw [h, map_one]
  rw [hfact, hkerRing]
  exact hkerψ

theorem natCard_range_semilinearCommutantAction_comp_ker_dvd [Finite K] (hn : n.Prime)
    {A : Type*} [Group A]
    (rho : A →* coordinateSemilinearGroup n K) (U : Subgroup (GL (Fin n) K))
    (hU : ∀ a : A, ∀ u ∈ U, coordinateSemilinearGLAct n K (rho a) u ∈ U)
    (hUcyc : IsCyclic U) (hUirr : IsIrreducibleMatrixRep U.subtype)
    (tau : (SemidirectProduct.rightHom.comp rho).ker →* GL (Fin n) K)
    (htau : ∀ j : (SemidirectProduct.rightHom.comp rho).ker,
      rho (j : A) = SemidirectProduct.inl (tau j)) :
    Nat.card ((semilinearCommutantAction rho U hU).comp
        (SemidirectProduct.rightHom.comp rho).ker.subtype).range ∣ n := by
  classical
  let ψ := linearKernelCommutantAction rho U hU tau htau
  have hfact := semilinearCommutantAction_comp_linearKernel_eq rho U hU tau htau
  rw [hfact, MonoidHom.range_comp,
    Subgroup.card_map_of_injective (algEquivToRingAut_injective K (commutant U))]
  have hcardψ := Subgroup.card_subgroup_dvd_card ψ.range
  rw [natCard_algEquiv_commutant_eq_of_prime_of_cyclic_irreducible hn hUirr hUcyc] at hcardψ
  exact hcardψ

theorem card_ringAut_commutant_eq_six_and_isCyclic [Finite K] (hK : Nat.card K = 4)
    {U : Subgroup (GL (Fin 3) K)} (hUcyc : IsCyclic U)
    (hUirr : IsIrreducibleMatrixRep U.subtype) :
    Nat.card (RingAut (commutant U)) = 6 ∧ IsCyclic (RingAut (commutant U)) := by
  classical
  let : Field (commutant U) := commutantField (isIrreducibleOn_iff.mpr hUirr)
  let : Finite (commutant U) := inferInstance
  have hcard : Nat.card (commutant U) = 2 ^ 6 := by
    rw [natCard_commutant_eq_pow_of_prime_of_cyclic_irreducible Nat.prime_three hUirr hUcyc, hK]
    norm_num
  exact CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
    Nat.prime_two (commutant U) hcard

end CFSG.LinearAlgebra
