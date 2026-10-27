module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusionSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityGeometry

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion

open CFSG.ShultStronglyClosedTI CFSG.Open
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

universe v

variable {G : Type v} [Group G]

@[expose] def subgroupInvolutions (S : Subgroup G) : Set G :=
  {x | x ∈ S ∧ orderOf x = 2}

@[expose] def puncturedSubgroup (U : Subgroup G) : Set G :=
  {x | x ∈ U ∧ x ≠ 1}

@[expose] def involutionTranslate (u : G) (U : Subgroup G) : Set G :=
  (fun w : G => u * w) '' (U : Set G)

structure ThreeLocalOrbitData (u : G)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (U : Subgroup G) (z : G) : Prop where
  involution_order : orderOf u = 2
  elementary : IsElementaryAbelian 2 U
  nontrivial : U ≠ ⊥
  subgroup_le : U ≤ centralizerSylowImage u T
  distinguished_mem : z ∈ U
  distinguished_ne_one : z ≠ 1
  involution_not_mem : u ∉ U
  full_partition : subgroupInvolutions (centralizerSylowImage u T) =
    ({u} : Set G) ∪ puncturedSubgroup U ∪
      (fun w : G => u * w) '' puncturedSubgroup U
  distinguished_orbit : puncturedSubgroup U ⊆ involutionPointClass z
  product_orbit : (fun w : G => u * w) '' puncturedSubgroup U ⊆
    involutionPointClass (u * z)
  distinct_classes : u ∉ involutionPointClass z

theorem ThreeLocalOrbitData.distinguished_order
    {u z : G} {T : Sylow 2 (Subgroup.centralizer ({u} : Set G))}
    {U : Subgroup G} (h : ThreeLocalOrbitData u T U z) : orderOf z = 2 := by
  let : IsElementaryAbelian 2 U := h.elementary
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_iff.mpr
    ⟨CFSG.elemPow_eq_one_of_isElementaryAbelian z h.distinguished_mem,
      h.distinguished_ne_one⟩

theorem point_class_eq_of_mem {a b : G} (hab : b ∈ involutionPointClass a) :
    involutionPointClass b = involutionPointClass a := by
  obtain ⟨g, hg⟩ := hab
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := hx
    rw [← hg] at hk
    refine ⟨g * k, ?_⟩
    simpa only [rightConjugateElem, mul_inv_rev, mul_assoc] using hk
  · intro x hx
    obtain ⟨k, hk⟩ := hx
    refine ⟨g⁻¹ * k, ?_⟩
    rw [← hg]
    unfold rightConjugateElem
    calc
      (g⁻¹ * k)⁻¹ * (g⁻¹ * a * g) * (g⁻¹ * k) = k⁻¹ * a * k := by group
      _ = x := hk

theorem ThreeLocalOrbitData.class_intersection_singleton_of_not_fused
    {u z : G} {T : Sylow 2 (Subgroup.centralizer ({u} : Set G))}
    {U : Subgroup G} (h : ThreeLocalOrbitData u T U z)
    (hnotfused : u * z ∉ involutionPointClass u) :
    involutionPointClass u ∩ (centralizerSylowImage u T : Set G) = {u} := by
  have hzdis := full_point_classes_disjoint u z h.distinct_classes
  have hproductdis := full_point_classes_disjoint (u * z) u hnotfused
  ext x
  constructor
  · intro hx
    have hxinv : x ∈ subgroupInvolutions (centralizerSylowImage u T) :=
      ⟨hx.2, order_two_of_mem_pointClass h.involution_order hx.1⟩
    rw [h.full_partition] at hxinv
    rcases hxinv with (hxu | hxU) | hxproduct
    · exact hxu
    · exact (Set.disjoint_left.mp hzdis hx.1 (h.distinguished_orbit hxU)).elim
    · exact (Set.disjoint_left.mp hproductdis (h.product_orbit hxproduct) hx.1).elim
  · intro hx
    have hxu : x = u := Set.mem_singleton_iff.mp hx
    rw [hxu]
    exact ⟨distinguished_mem_pointClass u,
      involution_mem_centralizerSylowImage h.involution_order T⟩

theorem normalizer_le_centralizer_of_class_intersection_singleton
    {u : G} {T : Sylow 2 (Subgroup.centralizer ({u} : Set G))}
    (hu : orderOf u = 2)
    (hsingleton : involutionPointClass u ∩
      (centralizerSylowImage u T : Set G) = {u}) :
    Subgroup.normalizer (centralizerSylowImage u T : Set G) ≤
      Subgroup.centralizer ({u} : Set G) := by
  intro g hg
  have hconjT : rightConjugateElem u g ∈ centralizerSylowImage u T :=
    (Subgroup.mem_normalizer_iff''.mp hg u).mp
      (involution_mem_centralizerSylowImage hu T)
  have heq : rightConjugateElem u g = u :=
    Set.mem_singleton_iff.mp (hsingleton ▸
      (show rightConjugateElem u g ∈ involutionPointClass u ∩
        (centralizerSylowImage u T : Set G) from ⟨⟨g, rfl⟩, hconjT⟩))
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hm := congrArg (fun x : G => g * x) heq
  simpa only [rightConjugateElem, mul_assoc, mul_inv_cancel_left] using hm.symm

theorem ThreeLocalOrbitData.ambient_sylow_of_not_fused [Finite G]
    {u z : G} {T : Sylow 2 (Subgroup.centralizer ({u} : Set G))}
    {U : Subgroup G} (h : ThreeLocalOrbitData u T U z)
    (hnotfused : u * z ∉ involutionPointClass u) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = centralizerSylowImage u T :=
  centralizerSylowImage_ambient_sylow u T
    (normalizer_le_centralizer_of_class_intersection_singleton h.involution_order
      (h.class_intersection_singleton_of_not_fused hnotfused))

end CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion
