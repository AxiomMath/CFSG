module

public import CFSG.ClassicalInvolution.SmallCases.Alternating.OddCore
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

theorem le_centralizer_of_isSubnormal_of_isQuasisimple {G : Type*} [Group G] [Finite G]
    {K C U : Subgroup G} (hK : IsSubnormal K C) (hUC : U ≤ C)
    (hCU : C ≤ Subgroup.normalizer (U : Set G)) (hU : IsPGroup 2 U)
    (hq : CFSG.Open.IsQuasisimple (K ⧸ classicalInvolutionOddCore K)) :
    K ≤ Subgroup.centralizer (U : Set G) := by
  have hKC : K ≤ C := isSubnormal_le hK
  let A : Subgroup K := (Subgroup.centralizer (U : Set G)).subgroupOf K
  have hAn : A.Normal := by
    refine ⟨fun x hx k => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hx ⊢
    intro u hu
    have hk' : (k : G)⁻¹ ∈ Subgroup.normalizer (U : Set G) := inv_mem (hCU (hKC k.2))
    have hu' : (k : G)⁻¹ * u * (k : G) ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp hk' u).mp hu
      simpa using this
    have h1 := hx _ hu'
    calc u * ((k * x * k⁻¹ : K) : G)
        = (k : G) * (((k : G)⁻¹ * u * (k : G)) * (x : G)) * (k : G)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
      _ = (k : G) * ((x : G) * ((k : G)⁻¹ * u * (k : G))) * (k : G)⁻¹ := by rw [h1]
      _ = ((k * x * k⁻¹ : K) : G) * u := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
  have hA : ∀ x : K, Odd (orderOf x) → x ∈ A := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    exact commute_of_odd_orderOf_of_isSubnormal hK hUC hCU hU hq x.2
      (by rwa [Subgroup.orderOf_coe]) 
  have htop := eq_top_of_forall_odd_orderOf_mem hq.1 A hA
  intro x hx
  have hxA : (⟨x, hx⟩ : K) ∈ A := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hxA

theorem false_of_normal_pGroup_centralizer_solvable {F : Type*} [Group F] [Finite F]
    (z : F) (_hz : orderOf z = 2) (K : Subgroup F) (_hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) (U : Subgroup F) (hU : IsPGroup 2 U)
    (hUC : U ≤ Subgroup.centralizer {z})
    (hUn : Subgroup.centralizer {z} ≤ Subgroup.normalizer (U : Set F))
    (hsolv : Group.IsSolvable ↥(Subgroup.centralizer {z} ⊓ Subgroup.centralizer (U : Set F))) :
    False := by
  have hq := isQuasisimple_oddCoreQuotient_of_witness hw hns
  have hle := le_centralizer_of_isSubnormal_of_isQuasisimple hK hUC hUn hU hq
  have hKle : K ≤ Subgroup.centralizer {z} ⊓ Subgroup.centralizer (U : Set F) :=
    le_inf (isSubnormal_le hK) hle
  have := hsolv
  exact hns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKle))

theorem false_of_normal_pGroup_self_centralizing {F : Type*} [Group F] [Finite F]
    (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) (U : Subgroup F) (hU : IsPGroup 2 U)
    (hUC : U ≤ Subgroup.centralizer {z})
    (hUn : Subgroup.centralizer {z} ≤ Subgroup.normalizer (U : Set F))
    (hcon : Subgroup.centralizer {z} ⊓ Subgroup.centralizer (U : Set F) ≤ U) : False := by
  refine false_of_normal_pGroup_centralizer_solvable z hz K hzK hK hw hns U hU hUC hUn ?_
  have h2 : IsPGroup 2 ↥(Subgroup.centralizer {z} ⊓ Subgroup.centralizer (U : Set F)) :=
    hU.to_le hcon
  have := h2.isNilpotent
  infer_instance

theorem false_of_twoConstrained {F : Type*} [Group F] [Finite F]
    (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K)
    (hcon : Subgroup.centralizer {z} ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer {z}) : Set F) ≤
          pCoreOf 2 (Subgroup.centralizer {z})) : False :=
  false_of_normal_pGroup_self_centralizing z hz K hzK hK hw hns
    (pCoreOf 2 (Subgroup.centralizer {z})) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) hcon

end CFSG.ClassicalInvolution
