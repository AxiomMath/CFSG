module

public import CFSG.LocalAnalysis.ComponentClassification.InvolutionLayer
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentTransport

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentInvolution

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem exists_maximal_invariant_two (L K : Subgroup G) (a : G) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 2 S ∧
      a ∈ Subgroup.normalizer (S : Set G) ∧ K ≤ Subgroup.normalizer (S : Set G) ∧
      ∀ T : Subgroup G, T ≤ L → IsPGroup 2 T →
        a ∈ Subgroup.normalizer (T : Set G) → K ≤ Subgroup.normalizer (T : Set G) →
        S ≤ T → T = S := by
  have hbot : (⊥ : Subgroup G) ≤ L ∧ IsPGroup 2 (⊥ : Subgroup G) ∧
      a ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) ∧
      K ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    refine ⟨bot_le, IsPGroup.of_subsingleton 2 (⊥ : Subgroup G), ?_, ?_⟩
    · apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      exact Subgroup.map_bot _
    · intro k _
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      exact Subgroup.map_bot _
  obtain ⟨S, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun S : Subgroup G => S ≤ L ∧ IsPGroup 2 S ∧
      a ∈ Subgroup.normalizer (S : Set G) ∧ K ≤ Subgroup.normalizer (S : Set G)) hbot
  refine ⟨S, hmaximal.prop.1, hmaximal.prop.2.1, hmaximal.prop.2.2.1,
    hmaximal.prop.2.2.2, ?_⟩
  intro T hTL htwo haT hKT hST
  exact ((maximal_iff.mp hmaximal).2 ⟨hTL, htwo, haT, hKT⟩ hST).symm

theorem involution_component_centralizes_invariant_two (a : G) (ha : orderOf a = 2)
    (K S : Subgroup G) (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsComponentOf (K.subgroupOf (Subgroup.centralizer ({a} : Set G))) ⊤)
    (htwo : IsPGroup 2 S) (haS : a ∈ Subgroup.normalizer (S : Set G))
    (hKS : K ≤ Subgroup.normalizer (S : Set G)) :
    K ≤ Subgroup.centralizer (S : Set G) := by
  let N := Subgroup.normalizer (S : Set G)
  let aN : N := ⟨a, haS⟩
  let C := Subgroup.centralizer ({a} : Set G)
  let CN := Subgroup.centralizer ({aN} : Set N)
  let SN := S.subgroupOf N
  let KN := K.subgroupOf N
  have hKNC : KN ≤ CN := by
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)))
  have hrestrict : IsComponentOf (K.subgroupOf (N ⊓ C)) ⊤ :=
    OrdinaryComponentTransport.restrict_nested K (N ⊓ C) C
      (le_inf hKS hKC) inf_le_right hK
  have hlocal : IsComponentOf (KN.subgroupOf CN) ⊤ :=
    OrdinaryComponentTransport.common_centralizer_transport K N a haS hrestrict
  let : SN.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (le_refl N)
  have htwoN : IsPGroup 2 SN := htwo.comap_subtype
  have haN : orderOf aN = 2 := by
    rw [← orderOf_injective N.subtype N.subtype_injective aN]
    exact ha
  have hcentral := InvolutionLayer.component_centralizes_normal_two aN haN SN htwoN
    (KN.subgroupOf CN) hlocal
  intro k hk
  apply Subgroup.mem_centralizer_iff.mpr
  intro s hs
  let kN : N := ⟨k, hKS hk⟩
  let kC : CN := ⟨kN, hKNC hk⟩
  have hkLocal : kC ∈ KN.subgroupOf CN := hk
  have hkImage : kN ∈ (KN.subgroupOf CN).map CN.subtype :=
    Subgroup.mem_map_of_mem CN.subtype hkLocal
  have hsN : (⟨s, Subgroup.le_normalizer hs⟩ : N) ∈ SN := hs
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hcentral hkImage)
    (⟨s, Subgroup.le_normalizer hs⟩ : N) hsN)

theorem invariant_two_component_in_common_centralizer (a : G) (ha : orderOf a = 2)
    (K S : Subgroup G) (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsComponentOf (K.subgroupOf (Subgroup.centralizer ({a} : Set G))) ⊤)
    (htwo : IsPGroup 2 S) (haS : a ∈ Subgroup.normalizer (S : Set G))
    (hKS : K ≤ Subgroup.normalizer (S : Set G)) :
    K ≤ Subgroup.centralizer ((S ⊔ Subgroup.zpowers a : Subgroup G) : Set G) ∧
      IsComponentOf
        (K.subgroupOf
          (Subgroup.centralizer ((S ⊔ Subgroup.zpowers a : Subgroup G) : Set G))) ⊤ := by
  have hcentralS := involution_component_centralizes_invariant_two a ha K S hKC hK htwo haS hKS
  have hcentralA : K ≤ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    intro k hk
    have hcyclic : Subgroup.zpowers a ≤ Subgroup.centralizer ({k} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)).symm)
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcyclic hx)
  have hcentral : K ≤ Subgroup.centralizer ((S ⊔ Subgroup.zpowers a : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp (sup_le
      (Subgroup.le_centralizer_iff.mp hcentralS)
      (Subgroup.le_centralizer_iff.mp hcentralA))
  have hsmaller : Subgroup.centralizer ((S ⊔ Subgroup.zpowers a : Subgroup G) : Set G) ≤
      Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx a
        ((show Subgroup.zpowers a ≤ S ⊔ Subgroup.zpowers a from le_sup_right)
          (Subgroup.mem_zpowers a))).symm
  exact ⟨hcentral, OrdinaryComponentTransport.restrict_nested K _ _ hcentral hsmaller hK⟩

theorem invariant_two_component_in_common_centralizer_layer (a : G) (ha : orderOf a = 2)
    (K S : Subgroup G) (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsComponentOf (K.subgroupOf (Subgroup.centralizer ({a} : Set G))) ⊤)
    (htwo : IsPGroup 2 S) (haS : a ∈ Subgroup.normalizer (S : Set G))
    (hKS : K ≤ Subgroup.normalizer (S : Set G)) :
    K ≤ (Layer.subgroup
      (Subgroup.centralizer ((S ⊔ Subgroup.zpowers a : Subgroup G) : Set G))).map
        (Subgroup.centralizer ((S ⊔ Subgroup.zpowers a : Subgroup G) : Set G)).subtype := by
  obtain ⟨hle, hcomponent⟩ := invariant_two_component_in_common_centralizer
    a ha K S hKC hK htwo haS hKS
  rw [← Subgroup.map_subgroupOf_eq_of_le hle]
  exact Subgroup.map_mono (Layer.component_le hcomponent)

end CFSG.ComponentClassification.AschbacherComponentInvolution
