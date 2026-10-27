module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAFixedLayerPComponent

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup

theorem contained_source_involution_stabilizes_correspondence {G : Type*} [Group G] [Finite G]
    {a b : G} {J L : Subgroup G} (h : GSCorr a J b L) (haJ : a ∈ J) :
    a ∈ gsFixedLayer J b ∧ gsFixedLayer J b ≤ L ∧ L = conjugate L a ∧
      L ⊔ conjugate L a = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcorr := h
  obtain ⟨hao, hbo, hab, hJa, hJcomp, hLb, hLcomp, hbN, hcomm, hfix⟩ := hcorr
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJcomp).2.2
  have hbb : b * b = 1 := by rw [← sq, ← hbo, pow_orderOf_eq_one]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hzp : ∀ c ∈ zpowers b, c = 1 ∨ c = b := by
    intro c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, hbb, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hbb, one_zpow, one_mul, zpow_one]
  have hBN : zpowers b ≤ normalizer (J : Set G) := zpowers_le.mpr hbN
  let α : zpowers b →* MulAut J := J.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hα : ∀ (c : zpowers b) (j : J), ((α c j : J) : G) = (c : G) * j * (c : G)⁻¹ :=
    fun c j => Subgroup.normalizerMonoidHom_apply_apply_coe J _ j
  have hB2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  have htriv : ∀ (c : zpowers b) (j : J),
      ((α c j : J) : J ⧸ pPrimeCore 2 J) = (j : J ⧸ pPrimeCore 2 J) := by
    intro c j
    rcases hzp c c.2 with hc | hc
    · have hc1 : c = 1 := Subtype.ext hc
      rw [hc1, map_one]
      rfl
    · rw [eq_comm, QuotientGroup.eq]
      obtain ⟨o, ho, hoeq⟩ := Subgroup.mem_map.mp (hcomm (j : G) j.2)
      have hoe : o = j⁻¹ * α c j := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hα, hc, hbinv]
        rw [hbinv] at hoeq
        change J.subtype o = _
        rw [hoeq]
        group
      rwa [hoe] at ho
  have hCmem : ∀ j : J, j ∈ (centralizer ({b} : Set G)).subgroupOf J ↔ ∀ c : zpowers b,
      α c j = j := by
    intro j
    rw [Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h c
      apply Subtype.ext
      rw [hα]
      rcases hzp c c.2 with hc | hc
      · rw [hc]
        group
      · rw [hc, ← h, mul_inv_cancel_right]
    · intro h
      have h1 := congrArg Subtype.val (h ⟨b, mem_zpowers b⟩)
      rw [hα] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  set CJ := (centralizer ({b} : Set G)).subgroupOf J with hCJ
  set TJ := (pLayer CJ 2).map CJ.subtype with hTJ
  have hclosure := NestedFixedLayer.fixed_prime_layer_eq_closure 2 hB2 α hJq htriv CJ hCmem TJ hTJ
  have haT : (⟨a, haJ⟩ : J) ∈ TJ := by
    rw [hclosure]
    apply Subgroup.subset_closure
    refine ⟨?_, 1, ?_⟩
    · change a ∈ centralizer ({b} : Set G)
      rw [mem_centralizer_singleton_iff]
      exact hab
    · rw [Subgroup.orderOf_mk, hao, pow_one]
  have hTb : TJ.map J.subtype = gsFixedLayer J b := by
    rw [hTJ, Subgroup.map_map, gsFixedLayer]
    let φ : CJ ≃* (J ⊓ centralizer ({b} : Set G) : Subgroup G) :=
      { toFun := fun x => ⟨x, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    have hcomp : J.subtype.comp CJ.subtype =
        (J ⊓ centralizer ({b} : Set G)).subtype.comp φ.toMonoidHom := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, FixedLayerPComponent.map_pLayer_mulEquiv 2 φ]
  have haTb : a ∈ gsFixedLayer J b := by
    rw [← hTb]
    exact ⟨⟨a, haJ⟩, haT, rfl⟩
  have haK : a ∈ L ⊔ conjugate L a := by
    have h1 : a ∈ gsFixedLayer (L ⊔ conjugate L a) a := hfix ▸ haTb
    exact (mem_inf.mp (gsFixedLayer_le_inf _ a h1)).1
  set Hb := centralizer ({b} : Set G) with hHb
  have haHb : a ∈ Hb := mem_centralizer_singleton_iff.mpr hab
  let a' : Hb := ⟨a, haHb⟩
  set L' := L.subgroupOf Hb with hL'
  set L'' := L'.map (MulAut.conj a'⁻¹).toMonoidHom with hL''
  have hL''eq : L'' = (conjugate L a).subgroupOf Hb := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, hx⟩
      exact ⟨⟨l, hLb hl⟩, hl, Subtype.ext hx⟩
  have hL''comp : IsPComponent 2 L'' :=
    ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
      (MulAut.conj a'⁻¹)).1 L').mp hLcomp
  have hconjle : conjugate L a ≤ Hb := by
    rintro _ ⟨l, hl, rfl⟩
    exact mul_mem (mul_mem (inv_mem haHb) (hLb hl)) (inv_mem (inv_mem haHb))
  have hsupmap : (L' ⊔ L'').map Hb.subtype = L ⊔ conjugate L a := by
    rw [Subgroup.map_sup, hL''eq, hL', Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hLb, inf_of_le_left hconjle]
  have ha'K : a' ∈ L' ⊔ L'' :=
    (Subgroup.mem_map_iff_mem Hb.subtype_injective).mp (by rw [hsupmap]; exact haK)
  have hL''L' : L'' = L' := by
    by_contra hne
    have hsub : L''.IsSubnormal :=
      ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 L'').mp
        hL''comp).1
    rcases CatalogueBPrimeJoin.contains_or_normalizes_core 2 L' L'' hLcomp hsub with
      hle | ⟨hnorm, -⟩
    · exact hne (CatalogueBPrimeJoin.eq_of_le 2 L' L'' hLcomp hL''comp hle).symm
    · have hK : L' ⊔ L'' ≤ normalizer (L' : Set Hb) := sup_le le_normalizer hnorm
      have ha'N : a'⁻¹ ∈ normalizer (L' : Set Hb) := inv_mem (hK ha'K)
      exact hne (Subgroup.mem_normalizer_iff_map_conj_eq.mp ha'N)
  have hLa : conjugate L a = L := by
    have h1 : (conjugate L a).subgroupOf Hb = L.subgroupOf Hb := by
      rw [← hL''eq, hL''L']
    have h2 := congrArg (Subgroup.map Hb.subtype) h1
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hconjle, inf_of_le_left hLb] at h2
  have hK : L ⊔ conjugate L a = L := by rw [hLa, sup_idem]
  exact ⟨haTb, GSCorr.gsFixedLayer_le h hK, hLa.symm, hK⟩

end CFSG.ComponentClassification.UnbalancedGS
