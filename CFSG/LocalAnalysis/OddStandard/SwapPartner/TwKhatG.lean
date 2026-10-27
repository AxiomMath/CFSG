module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwKhat
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoRoot

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

private theorem tw_subgroupOf_map_subtype {G : Type*} [Group G] (C : Subgroup G)
    (K : Subgroup ↥C) : (K.map C.subtype).subgroupOf C = K :=
  Subgroup.map_injective C.subtype_injective (by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
    exact Subgroup.map_subtype_le K)

theorem exists_khat_map {G : Type} [Group G] {x : G} {A : Subgroup G}
    (hAx : A ≤ centralizer ({x} : Set G)) (hA : ⁅A, A⁆ = A)
    {K : Subgroup (TwoSec x)} [K.Normal] (hK : ⁅K, K⁆ = K)
    (hAK : (A.subgroupOf (centralizer ({x} : Set G))).map
      (QuotientGroup.mk' (zpowers (selfC x))) ≤ K) :
    ∃ Kh : Subgroup G, Kh ≤ centralizer ({x} : Set G) ∧
      (Kh.subgroupOf (centralizer ({x} : Set G))).Normal ∧ ⁅Kh, Kh⁆ = Kh ∧ A ≤ Kh ∧
      Nonempty (↥Kh ⧸ center ↥Kh ≃* ↥K ⧸ center ↥K) ∧
      (Kh.subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (zpowers (selfC x))) = K := by
  have hxc : ∀ h : ↥(centralizer ({x} : Set G)), h * selfC x = selfC x * h :=
    Subgroup.mem_center_iff.mp (selfC_mem_center x)
  let C : Subgroup G := centralizer ({x} : Set G)
  let Khat : Subgroup ↥C := hatSub (selfC x) K
  let Kh : Subgroup G := Khat.map C.subtype
  have hsub : Kh.subgroupOf C = Khat := tw_subgroupOf_map_subtype C Khat
  have hKhat_perfect : ⁅Khat, Khat⁆ = Khat := hatSub_perfect (x := selfC x) hxc hK
  have hPmap : (A.subgroupOf C).map C.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
    exact hAx
  have hPK : A.subgroupOf C ≤ K.comap (QuotientGroup.mk' (zpowers (selfC x))) :=
    Subgroup.map_le_iff_le_comap.mp hAK
  have hPperf : ⁅A.subgroupOf C, A.subgroupOf C⁆ = A.subgroupOf C := by
    rw [← Subgroup.map_subtype_inj (H := C),
      Subgroup.map_commutator (A.subgroupOf C) (A.subgroupOf C) C.subtype, hPmap, hA]
  have hPle : A.subgroupOf C ≤ Khat := le_hatSub_of_perfect hPperf hPK
  have hA_le_Kh : A ≤ Kh := by
    have h := (Subgroup.map_subtype_le_map_subtype (G' := C)).mpr hPle
    rwa [hPmap] at h
  refine ⟨Kh, Subgroup.map_subtype_le Khat, ?_, ?_, hA_le_Kh, ?_, ?_⟩
  · rw [hsub]
    exact hatSub_normal (x := selfC x) (K := K)
  · show ⁅Khat.map C.subtype, Khat.map C.subtype⁆ = Khat.map C.subtype
    rw [← Subgroup.map_commutator Khat Khat C.subtype, hKhat_perfect]
  · obtain ⟨f⟩ := nonempty_quotient_center_equiv (x := selfC x) (K := K) hxc hK
    let e : ↥Khat ≃* ↥Kh := Subgroup.equivMapOfInjective Khat C.subtype C.subtype_injective
    have hcongr : Nonempty (↥Khat ⧸ center ↥Khat ≃* ↥Kh ⧸ center ↥Kh) :=
      ⟨QuotientGroup.congr (center ↥Khat) (center ↥Kh) e (Subgroup.map_center_eq e)⟩
    obtain ⟨g⟩ := hcongr
    exact ⟨g.symm.trans f⟩
  · rw [hsub]
    exact map_hatSub (x := selfC x) hK

end CFSG.OddStandard.AltStdSec.SwapPartner
