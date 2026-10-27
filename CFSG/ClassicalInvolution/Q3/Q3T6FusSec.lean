module

public import CFSG.ClassicalInvolution.Q3.Q3T6CoreInp
public import CFSG.ClassicalInvolution.AschTight.S1911P3h

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

instance conjGen_normal' {Y₀ : Type} [Group Y₀] (L : Subgroup Y₀) : (conjGen L).Normal :=
  conjGen_normal L

section Data

variable {G : Type} [Group G] [Finite G]

structure FusSec3 (K : Subgroup G) (z : G) (C : Subgroup G) : Prop where
  member : Q3.IsClassicalMember3 K z
  hyp : HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K)
  edgeless : DEdgeless (CoreAssembly.conjClass K)
  tight : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G)
  zC : z ∈ C
  memberC : Q3.IsClassicalMember3 (secL K C) (⟨z, zC⟩ : C)

namespace FusSec3

variable {K : Subgroup G} {z : G} {C : Subgroup G} (h : FusSec3 K z C)

include h

theorem isUniqueInvolution : IsUniqueInvolution K z :=
  (isClassicalMember3_iff_U.mp h.member).isUniqueInvolution (MemberType.cert_sl2 3 1)

theorem isUniqueInvolution_sec : IsUniqueInvolution (secL K C) (⟨z, h.zC⟩ : C) :=
  (isClassicalMember3_iff_U.mp h.memberC).isUniqueInvolution (MemberType.cert_sl2 3 1)

theorem hypC : HypOmegaModU (.sl2 3 1) (conjFamily (secL K C)) :=
  hypOmegaModU_conjFamily_sec h.member h.hyp h.zC h.memberC

theorem edgelessC : DEdgeless (conjFamily (secL K C)) :=
  dEdgeless_conjFamily_sec h.member h.hyp h.edgeless h.tight h.zC h.memberC

theorem hypGenC : HypOmegaGen (conjFamily (secL K C)) :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) h.hypC

theorem hypGen : HypOmegaGen (CoreAssembly.conjClass K) :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) h.hyp

theorem mem_normalizer_sec {t : ↥C} (htz : (t : G) * z = z * (t : G)) :
    t ∈ Subgroup.normalizer ((secL K C : Subgroup ↥C) : Set ↥C) := by
  have hN : (t : G) ∈ Subgroup.normalizer ((conjSub (((1 : ↥C)) : G) K : Subgroup G) : Set G) := by
    rw [OneMemClass.coe_one, conjSub_one]
    exact h.tight (Subgroup.mem_centralizer_singleton_iff.mpr htz)
  have h1 := mem_normalizer_conjSub_of_sec (K := K) (C := C) 1 t hN
  rwa [conjSub_one] at h1

theorem isUniqueInvolution_conj_sec (c : ↥C) :
    IsUniqueInvolution (conjSub c (secL K C)) (c * (⟨z, h.zC⟩ : C) * c⁻¹) :=
  h.isUniqueInvolution_sec.conj c

theorem isUniqueInvolution_secImg (c : ↥C) :
    IsUniqueInvolution (secImg (conjGen (secL K C)) (conjSub c (secL K C)))
      (QuotientGroup.mk' _ ⟨c * (⟨z, h.zC⟩ : C) * c⁻¹,
        le_conjGen ⟨c, rfl⟩ (h.isUniqueInvolution_conj_sec c).mem⟩) :=
  isUniqueInvolution_map_mk (CFSG.ComponentClassification.OddCore.odd_card _)
    (S1911.isUniqueInvolution_subgroupOf (h.isUniqueInvolution_conj_sec c)
      (le_conjGen ⟨c, rfl⟩))

theorem exists_conj_comm_of_secAct {s : ↥C} (hs2 : s * s = 1) {c : ↥C}
    (hc : (secImg (conjGen (secL K C)) (conjSub c (secL K C))).map
      (secAct (conjGen (secL K C)) s).toMonoidHom =
        secImg (conjGen (secL K C)) (conjSub c (secL K C))) :
    ∃ v ∈ oddCoreOf (conjGen (secL K C)),
      (v * c)⁻¹ * s * (v * c) * (⟨z, h.zC⟩ : C) = (⟨z, h.zC⟩ : C) * ((v * c)⁻¹ * s * (v * c)) := by
  have hu := h.isUniqueInvolution_secImg c
  set φ := secAct (conjGen (secL K C)) s with hφ
  set ū := QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjGen (secL K C)))
    ⟨c * (⟨z, h.zC⟩ : C) * c⁻¹, le_conjGen ⟨c, rfl⟩ (h.isUniqueInvolution_conj_sec c).mem⟩ with hū
  have hφu : φ ū = ū := by
    have hmem : φ ū ∈ secImg (conjGen (secL K C)) (conjSub c (secL K C)) := by
      rw [← hc]
      exact ⟨ū, hu.mem, rfl⟩
    have hsq : φ ū * φ ū = 1 := by rw [← map_mul, hu.sq, map_one]
    have hne : φ ū ≠ 1 := fun h' => hu.ne_one (φ.injective (h'.trans (map_one φ).symm))
    exact (hu.unique _ hmem hsq).resolve_left hne
  have hO := mem_oddCoreOf_of_secAct _ hφu
  have hu2 : c * (⟨z, h.zC⟩ : C) * c⁻¹ * (c * (⟨z, h.zC⟩ : C) * c⁻¹) = 1 :=
    (h.isUniqueInvolution_conj_sec c).sq
  obtain ⟨v, hvO, hv⟩ := exists_conj_commute_of_odd (oddCoreOf_odd_natCard _) hs2 hu2
    (mem_normalizer_oddCoreOf_conjGen _ s) (mem_normalizer_oddCoreOf_conjGen _ _) hO
  refine ⟨v, hvO, ?_⟩
  calc (v * c)⁻¹ * s * (v * c) * (⟨z, h.zC⟩ : C)
      = (v * c)⁻¹ * (s * (v * (c * (⟨z, h.zC⟩ : C) * c⁻¹) * v⁻¹)) * (v * c) := by group
    _ = (v * c)⁻¹ * ((v * (c * (⟨z, h.zC⟩ : C) * c⁻¹) * v⁻¹) * s) * (v * c) := by rw [hv]
    _ = (⟨z, h.zC⟩ : C) * ((v * c)⁻¹ * s * (v * c)) := by group

theorem secAct_z_fixes :
    ∀ x ∈ secImg (conjGen (secL K C)) (secL K C),
      secAct (conjGen (secL K C)) (⟨z, h.zC⟩ : C) x = x := by
  have hu := h.isUniqueInvolution_sec
  rintro _ ⟨m, hm, rfl⟩
  rw [QuotientGroup.mk'_apply, secAct_mk]
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  have hmL : (m : ↥C) ∈ secL K C := Subgroup.mem_subgroupOf.mp hm
  generalize (m : ↥C) = n at hmL ⊢
  have hc : n * (⟨z, h.zC⟩ : C) * n⁻¹ ∈ secL K C :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hmL hu.mem) (Subgroup.inv_mem _ hmL)
  have hsq : n * (⟨z, h.zC⟩ : C) * n⁻¹ * (n * (⟨z, h.zC⟩ : C) * n⁻¹) = 1 := by
    calc n * (⟨z, h.zC⟩ : C) * n⁻¹ * (n * (⟨z, h.zC⟩ : C) * n⁻¹)
        = n * ((⟨z, h.zC⟩ : C) * ⟨z, h.zC⟩) * n⁻¹ := by group
      _ = 1 := by rw [hu.sq]; group
  have h1 : n * (⟨z, h.zC⟩ : C) * n⁻¹ = ⟨z, h.zC⟩ := by
    refine (hu.unique _ hc hsq).resolve_left fun h' => hu.ne_one ?_
    calc (⟨z, h.zC⟩ : ↥C) = n⁻¹ * (n * (⟨z, h.zC⟩ : C) * n⁻¹) * n := by group
      _ = 1 := by rw [h']; group
  calc (⟨z, h.zC⟩ : ↥C) * n * (⟨z, h.zC⟩ : ↥C)⁻¹ =
      ⟨z, h.zC⟩ * (n * (⟨z, h.zC⟩ : C) * n⁻¹)⁻¹ * n := by group
    _ = n := by rw [h1]; group

end FusSec3

namespace FusSec3

theorem of_cStar {K : Subgroup G} {z : G} (hK : Q3.IsClassicalMember3 K z)
    (hΩ : HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K))
    (hDE : DEdgeless (CoreAssembly.conjClass K))
    (hN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G))
    {B : Subgroup G} (hB2 : IsPGroup 2 B) (hBK : B ≤ centralizerModOdd ⊤ K)
    (hzB : z ∈ Subgroup.centralizer (B : Set G)) :
    FusSec3 K z (Subgroup.centralizer (B : Set G)) :=
  ⟨hK, hΩ, hDE, hN, hzB, isClassicalMember3_inf_centralizer_of_cStar hK hB2 hBK rfl hzB⟩

theorem of_cStar_element {K : Subgroup G} {z : G} (hK : Q3.IsClassicalMember3 K z)
    (hΩ : HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K))
    (hDE : DEdgeless (CoreAssembly.conjClass K))
    (hN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G)) {x : G}
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hxK : x ∈ centralizerModOdd ⊤ K)
    (hzx : z ∈ Subgroup.centralizer ({x} : Set G)) :
    FusSec3 K z (Subgroup.centralizer ({x} : Set G)) :=
  ⟨hK, hΩ, hDE, hN, hzx, isClassicalMember3_centralizer_of_cStar hK hx2 hxK hzx⟩

end FusSec3

end Data

end CFSG.ClassicalInvolution.Q3.Q3T6
