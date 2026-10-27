module

public import CFSG.LieType.Chevalley.BraidWalk
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CoxeterSystem

variable {τ : Tag} {R : Type*} [CommRing R]

theorem rootModule_end_ext {f g : Module.End R (RootModule τ R)}
    (hh : ∀ j, f (hVec τ R j) = g (hVec τ R j))
    (hr : ∀ α, IsRoot τ α → f (rootVec τ R α) = g (rootVec τ R α)) : f = g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rcases b with j | ⟨α, hα⟩
  · exact hh j
  · have h := hr α hα
    rwa [rootVec, dite_eq_left hα] at h

theorem sum_cartan_mul_reflect_apply (i j : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    ∑ k, τ.cartan j k * reflect τ i v k =
      ∑ k, τ.cartan j k * v k - τ.cartan j i * ∑ k, τ.cartan i k * v k := by
  simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero, mul_sub, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

variable (τ R) in
theorem weylElt_one_mul_self (i : Fin τ.rank) :
    weylElt τ R i 1 * weylElt τ R i 1 = torusElt τ R i (-1) := by
  have h₁ : torusElt τ R i (-1) = (weylElt τ R i 1 * weylElt τ R i 1)⁻¹ := by
    rw [mul_inv_rev, weylElt_inv, torusElt]
  have h₂ : torusElt τ R i (-1) * torusElt τ R i (-1) = 1 := by
    rw [← torusElt_mul, neg_one_mul, neg_neg, torusElt_one]
  rw [h₁] at h₂ ⊢
  rw [eq_inv_of_mul_eq_one_left h₂, inv_inv]

variable (τ R) in
theorem weylElt_one_sq (i : Fin τ.rank) : weylElt τ R i 1 ^ 2 = torusElt τ R i (-1) := by
  rw [sq, weylElt_one_mul_self]

variable (τ R) in
theorem weylElt_mul_torusElt (i j : Fin τ.rank) (s t : Rˣ) :
    weylElt τ R i s * torusElt τ R j t =
      torusElt τ R j t * torusElt τ R i (t ^ (-τ.cartan j i)) * weylElt τ R i s := by
  refine Units.ext (rootModule_end_ext (fun k => ?_) (fun α hα => ?_))
  · simp only [Units.val_mul, Module.End.mul_apply, torusElt_hVec, weylElt_hVec, map_sub,
      map_smul]
  · simp only [Units.val_mul, Module.End.mul_apply, torusElt_rootVec _ _ hα, map_smul,
      weylElt_rootVec _ _ hα, torusElt_rootVec _ _ (hα.reflect i), smul_smul]
    congr 1
    rw [sum_cartan_mul_reflect, sum_cartan_mul_reflect_apply]
    have key : (((t ^ (-τ.cartan j i)) ^ (-∑ k, τ.cartan i k * α k) : Rˣ) : R) *
        ((t ^ (∑ k, τ.cartan j k * α k - τ.cartan j i * ∑ k, τ.cartan i k * α k) : Rˣ) : R) =
          ((t ^ (∑ k, τ.cartan j k * α k) : Rˣ) : R) := by
      rw [← Units.val_mul, ← zpow_mul, ← zpow_add]
      congr 2
      ring
    rw [key]
    ring

variable (τ R) in
theorem weylElt_one_mul_torusElt_mul_inv (i j : Fin τ.rank) (t : Rˣ) :
    weylElt τ R i 1 * torusElt τ R j t * (weylElt τ R i 1)⁻¹ =
      torusElt τ R j t * torusElt τ R i (t ^ (-τ.cartan j i)) := by
  rw [weylElt_mul_torusElt, mul_inv_cancel_right]

variable (τ R) in
theorem torusElt_mul_weylElt_one (i : Fin τ.rank) (t : Rˣ) :
    torusElt τ R i t * weylElt τ R i 1 = weylElt τ R i t := by
  rw [torusElt, ← weylElt_inv, inv_mul_cancel_right]

variable (τ R) in
theorem weylElt_mul_self (i : Fin τ.rank) (t : Rˣ) :
    weylElt τ R i t * weylElt τ R i t = torusElt τ R i (-1) := by
  rw [← torusElt_mul_weylElt_one, mul_assoc, ← mul_assoc (weylElt τ R i 1),
    weylElt_mul_torusElt, mul_assoc, mul_assoc, weylElt_one_mul_self, ← mul_assoc,
    ← mul_assoc, ← torusElt_mul, ← torusElt_mul, ← torusElt_mul, τ.cartan_self]
  congr 1
  rw [← sq, ← zpow_natCast, ← zpow_add]
  norm_num

variable (τ R) in
theorem weylElt_mul_mul_inv_mem_torus (i : Fin τ.rank) (s : Rˣ)
    {h : (Module.End R (RootModule τ R))ˣ}
    (hh : h ∈ Subgroup.closure (Set.range fun p : Fin τ.rank × Rˣ => torusElt τ R p.1 p.2)) :
    weylElt τ R i s * h * (weylElt τ R i s)⁻¹ ∈
      Subgroup.closure (Set.range fun p : Fin τ.rank × Rˣ => torusElt τ R p.1 p.2) := by
  set H := Subgroup.closure (Set.range fun p : Fin τ.rank × Rˣ => torusElt τ R p.1 p.2)
  have hle : H ≤ H.comap (MulAut.conj (weylElt τ R i s)).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨k, u⟩, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [weylElt_mul_torusElt, mul_inv_cancel_right]
    exact mul_mem (Subgroup.subset_closure ⟨(k, u), rfl⟩)
      (Subgroup.subset_closure ⟨(i, u ^ (-τ.cartan k i)), rfl⟩)
  exact hle hh

variable (τ R) in
theorem weylElt_mem_normalizer_torus (i : Fin τ.rank) (s : Rˣ) :
    weylElt τ R i s ∈ Subgroup.normalizer
      (Subgroup.closure (Set.range fun p : Fin τ.rank × Rˣ => torusElt τ R p.1 p.2) :
        Set (Module.End R (RootModule τ R))ˣ) := by
  rw [Subgroup.mem_normalizer_iff]
  refine fun h => ⟨weylElt_mul_mul_inv_mem_torus τ R i s, fun hh => ?_⟩
  have := weylElt_mul_mul_inv_mem_torus τ R i (-s) hh
  simpa [← weylElt_inv, mul_assoc] using this

open RootWalk in
theorem prod_alternatingWord_weylElt_of_lt {i j : Fin τ.rank} (hij : i < j) :
    ((alternatingWord i j (TauCeti.coxeterOrder (τ.cartan i j * τ.cartan j i))).map
        fun k => weylElt τ R k 1).prod =
      ((alternatingWord j i (TauCeti.coxeterOrder (τ.cartan i j * τ.cartan j i))).map
        fun k => weylElt τ R k 1).prod := by
  obtain ⟨hh, hr⟩ := braidCheckPair_of_lt hij
  rw [coxeterOrder_eq_braidLength]
  refine Units.ext (rootModule_end_ext (fun k => ?_) (fun α hα => ?_))
  · rw [← hVecSum_single, prod_weylElt_hVecSum, prod_weylElt_hVecSum, hh k]
  · obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
    rw [prod_weylElt_rootVec_root R _ hk, prod_weylElt_rootVec_root R _ hk, hr k hk]

variable (τ R) in
theorem prod_alternatingWord_weylElt (i j : Fin τ.rank) :
    ((alternatingWord i j (TauCeti.coxeterOrder (τ.cartan i j * τ.cartan j i))).map
        fun k => weylElt τ R k 1).prod =
      ((alternatingWord j i (TauCeti.coxeterOrder (τ.cartan i j * τ.cartan j i))).map
        fun k => weylElt τ R k 1).prod := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact prod_alternatingWord_weylElt_of_lt hij
  · rfl
  · rw [mul_comm]
    exact (prod_alternatingWord_weylElt_of_lt hij).symm

end CFSG.LieType.Chevalley
