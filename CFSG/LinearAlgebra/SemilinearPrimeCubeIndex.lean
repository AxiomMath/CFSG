module

public import CFSG.LinearAlgebra.CardFourAutomorphism
public import CFSG.LinearAlgebra.CoordinateSemilinearMatrixAction
public import CFSG.GroupTheory.PrimeCubeInvolutionQuotient
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard

public noncomputable section

namespace CFSG.LinearAlgebra

open Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

abbrev linearKernel {A : Type*} [Group A] {K : Type} [Field K]
    (rho : A →* coordinateSemilinearGroup 3 K) : Subgroup A :=
  (SemidirectProduct.rightHom.comp rho).ker

theorem exists_normal_index_three_containing_of_semilinear_card_twenty_seven_index_two
    {A : Type*} [Group A] [Finite A]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (rho : A →* coordinateSemilinearGroup 3 K)
    (tau : linearKernel rho →* GL (Fin 3) K)
    (htau : ∀ j : linearKernel rho,
      rho (j : A) = SemidirectProduct.inl (tau j))
    (htau_inj : Function.Injective tau)
    (hindex : (linearKernel rho).index = 2)
    (hcard : Nat.card (linearKernel rho) = 27)
    (hnc : ∃ x y : linearKernel rho, x * y ≠ y * x)
    (Z : Subgroup (linearKernel rho))
    (hZcard : Nat.card Z = 3)
    (hZscalar : ∀ z ∈ Z, ∃ c : Kˣ,
      tau z = GeneralLinearGroup.scalar (Fin 3) c)
    (t : A) (ht : orderOf t = 2) :
    ∃ N : Subgroup A, N.Normal ∧ N.index = 3 ∧ t ∈ N := by
  classical
  have htJ : t ∉ linearKernel rho := by
    intro htmem
    have hdvd : orderOf t ∣ Nat.card (linearKernel rho) :=
      Subgroup.orderOf_dvd_natCard (linearKernel rho) htmem
    rw [ht, hcard] at hdvd
    norm_num at hdvd
  have hright : (rho t).right ≠ 1 := by
    intro h1
    exact htJ (MonoidHom.mem_ker.mpr (by simpa using h1))
  have hmem : ∀ z : linearKernel rho,
      t * (z : A) * t⁻¹ ∈ linearKernel rho := by
    intro z
    change (SemidirectProduct.rightHom.comp rho) (t * (z : A) * t⁻¹) = 1
    have hz1 : (SemidirectProduct.rightHom.comp rho) (z : A) = 1 := z.2
    simp only [MonoidHom.comp_apply, map_mul, map_inv, hz1, mul_one, mul_inv_cancel]
  have hZcenter : Z ≤ Subgroup.center (linearKernel rho) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro j
    apply htau_inj
    obtain ⟨c, hc⟩ := hZscalar z hz
    rw [map_mul, map_mul, hc]
    exact (GeneralLinearGroup.scalar_commute c (tau j)).symm
  have hnc' : ¬ IsMulCommutative (linearKernel rho) := by
    intro hcomm
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy (hcomm.is_comm.comm x y)
  have hcardCenter : Nat.card (Subgroup.center (linearKernel rho)) = 3 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.card_center_of_nonabelian_card_p_cube
      (p := 3) (T := linearKernel rho) (by rw [hcard]; norm_num) hnc'
  have hcenter_eq : Subgroup.center (linearKernel rho) = Z := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hZcenter
    omega
  have hconjmap : ∀ (z : linearKernel rho), z ∈ Z →
      tau (⟨t * (z : A) * t⁻¹, hmem z⟩ : linearKernel rho) = (tau z)⁻¹ := by
    intro z hz
    obtain ⟨c, hc⟩ := hZscalar z hz
    have hσc : Units.map (rho t).right.toMonoidHom c = c⁻¹ :=
      units_map_eq_inv_of_card_four hK (rho t).right hright c
    let j' : linearKernel rho := ⟨t * (z : A) * t⁻¹, hmem z⟩
    have hconj :=
      tau_conj_eq_coordinateSemilinearGLAct 3 K rho tau htau t z j' rfl
    change tau j' = (tau z)⁻¹
    rw [hconj, hc, coordinateSemilinearGLAct_scalar, hσc]
    exact map_inv (GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K) c
  have hZinv : ∀ z : Subgroup.center (linearKernel rho),
      t * ((z : linearKernel rho) : A) * t⁻¹ =
        (((z : linearKernel rho) : A))⁻¹ := by
    intro z
    have hzZ : (z : linearKernel rho) ∈ Z := by
      rw [← hcenter_eq]
      exact z.2
    let j' : linearKernel rho :=
      ⟨t * ((z : linearKernel rho) : A) * t⁻¹, hmem (z : linearKernel rho)⟩
    have hconj := hconjmap (z : linearKernel rho) hzZ
    have hjeq : j' = (z : linearKernel rho)⁻¹ := by
      apply htau_inj
      change tau j' = tau ((z : linearKernel rho)⁻¹)
      rw [hconj, map_inv]
    have hval := congrArg (fun w : linearKernel rho => (w : A)) hjeq
    simpa [j'] using hval
  haveI : (linearKernel rho).Normal :=
    MonoidHom.normal_ker (SemidirectProduct.rightHom.comp rho)
  exact CFSG.GroupTheory.exists_normal_index_three_containing_of_nonabelian_card_twenty_seven_index_two
    (P := linearKernel rho) hcard hnc hindex t ht hZinv

theorem exists_normal_index_three_of_semilinear_card_twenty_seven_index_two
    {A : Type*} [Group A] [Finite A]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (rho : A →* coordinateSemilinearGroup 3 K)
    (tau : linearKernel rho →* GL (Fin 3) K)
    (htau : ∀ j : linearKernel rho,
      rho (j : A) = SemidirectProduct.inl (tau j))
    (htau_inj : Function.Injective tau)
    (hindex : (linearKernel rho).index = 2)
    (hcard : Nat.card (linearKernel rho) = 27)
    (hnc : ∃ x y : linearKernel rho, x * y ≠ y * x)
    (Z : Subgroup (linearKernel rho))
    (hZcard : Nat.card Z = 3)
    (hZscalar : ∀ z ∈ Z, ∃ c : Kˣ,
      tau z = GeneralLinearGroup.scalar (Fin 3) c) :
    ∃ N : Subgroup A, N.Normal ∧ N.index = 3 := by
  classical
  have hA : Nat.card A = 54 := by
    have h := (Subgroup.card_mul_index (linearKernel rho)).symm
    rw [hcard, hindex] at h
    norm_num at h ⊢
    exact h
  have h2 : 2 ∣ Nat.card A := by
    rw [hA]
    norm_num
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 h2
  obtain ⟨N, hN, hidx, -⟩ :=
    exists_normal_index_three_containing_of_semilinear_card_twenty_seven_index_two
      hK rho tau htau htau_inj hindex hcard hnc Z hZcard hZscalar t ht
  exact ⟨N, hN, hidx⟩

end CFSG.LinearAlgebra
