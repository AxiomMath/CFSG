module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Swap
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Shape
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.M10Shape
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonCatM10

public section

namespace CFSG.EvenSporadicStandard.SolomonRed

open Subgroup CFSG CFSG.LocalCores CFSG.Open

@[expose] noncomputable def mulEquivQuotientOddCore {D : Type*} [Group D]
    (h : fusionOddCore D = ⊥) : D ≃* D ⧸ fusionOddCore D :=
  MulEquiv.ofBijective (QuotientGroup.mk' (fusionOddCore D))
    ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', h]),
      QuotientGroup.mk'_surjective _⟩

theorem solomonM10_of_cat (h : CatM10AlmostSimple) : Fin76b.SolomonM10 := by
  intro K _ _ hK z hz hZ hO hHyp
  have hz2 : z * z = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hz, sq] at h1
    exact h1
  have hne : z ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hz
    omega
  have hsimple6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hnab6 : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a :=
    exists_noncommute_of_center_eq_bot (alternatingGroup.center_eq_bot (by simp))
  obtain ⟨Ab, ⟨iso⟩, hzAb, hidx, hsq⟩ := hHyp
  let θ' := mulEquivQuotientOddCore hO
  let A : Subgroup ↥(centralizer ({z} : Set K)) := Ab.map θ'.symm.toMonoidHom
  let eA : ↥A ≃* alternatingGroup (Fin 6) := (θ'.symm.subgroupMap Ab).symm.trans iso
  have hAsimple : IsSimpleGroup ↥A := eA.isSimpleGroup
  have hAnab : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab6
    exact ⟨(eA.symm a : ↥(centralizer ({z} : Set K))), (eA.symm a).2,
      (eA.symm b : ↥(centralizer ({z} : Set K))), (eA.symm b).2, fun h1 => hab (by
        have h2 : eA.symm a * eA.symm b = eA.symm b * eA.symm a := Subtype.ext h1
        have h3 := congrArg eA h2
        simpa using h3)⟩
  have hzbar : θ' (zz z) = Fin76b.zbarC K z := rfl
  have hAZ : ∀ x : ↥(centralizer ({z} : Set K)),
      x ∈ A ⊔ zpowers (zz z) ↔ θ' x ∈ Ab ⊔ zpowers (Fin76b.zbarC K z) := by
    intro x
    have h1 : A ⊔ zpowers (zz z) = (Ab ⊔ zpowers (Fin76b.zbarC K z)).map θ'.symm.toMonoidHom := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      congr 2
      rw [← hzbar]
      exact (θ'.symm_apply_apply (zz z)).symm
    rw [h1, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have hidx' : (A ⊔ zpowers (zz z)).index = 2 := by
    have h1 : A ⊔ zpowers (zz z) = (Ab ⊔ zpowers (Fin76b.zbarC K z)).map θ'.symm.toMonoidHom := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      congr 2
      rw [← hzbar]
      exact (θ'.symm_apply_apply (zz z)).symm
    rw [h1]
    exact (Subgroup.index_map_of_bijective (f := θ'.symm.toMonoidHom) θ'.symm.bijective _).trans
      hidx
  have hsq' : ∀ x : ↥(centralizer ({z} : Set K)), x * x ∈ zpowers (zz z) →
      x ∈ A ⊔ zpowers (zz z) := by
    intro x hx
    rw [hAZ]
    apply hsq
    have h1 : θ' (x * x) ∈ (zpowers (zz z)).map θ'.toMonoidHom := ⟨_, hx, rfl⟩
    rw [MonoidHom.map_zpowers] at h1
    rwa [map_mul] at h1
  have hAnormal : A.Normal := m10_normal zz_comm hAsimple hAnab hidx'
  have hAcent := m10_cent zz_comm hAsimple hAnab hidx' hsq'
  let B : Subgroup K := A.map (centralizer ({z} : Set K)).subtype
  have hBA : ↥B ≃* ↥A :=
    (Subgroup.equivMapOfInjective A (centralizer ({z} : Set K)).subtype
      (centralizer ({z} : Set K)).subtype_injective).symm
  have hB : Setting K z B := by
    refine ⟨hz2, hne, ?_, ?_, hBA.isSimpleGroup, ?_, ?_,
      fun N hN hodd => odd_of_zstar_eq_bot hZ hN hodd, center_of_zstar_eq_bot hZ⟩
    · rintro _ ⟨a, _, rfl⟩
      exact a.2
    · rintro d hd _ ⟨a, ha, rfl⟩
      exact ⟨⟨d, hd⟩ * a * ⟨d, hd⟩⁻¹, hAnormal.conj_mem a ha _, rfl⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := hAnab
      exact ⟨(a : K), ⟨a, ha, rfl⟩, (b : K), ⟨b, hb, rfl⟩, fun h1 => hab (Subtype.ext h1)⟩
    · intro d hd hcomm
      have h1 := hAcent ⟨d, hd⟩ fun a ha => Subtype.ext (hcomm (a : K) ⟨a, ha, rfl⟩)
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h1
      refine mem_zpowers_iff.2 ⟨k, ?_⟩
      have h2 := congrArg Subtype.val hk
      simpa [zz] using h2
  rcases dichotomy hB with ⟨S, hS⟩ | ⟨S₁, S₂, hs⟩
  ·
    have := hS.simple
    have := hS.normal
    have hcatS : CFSG.Blueprint.Catalog ↥S :=
      CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK S (MonoidHom.id ↥S)
        Function.surjective_id
    exact h K S hS.normal hS.simple hcatS hS.cent z hz hO ⟨Ab, ⟨iso⟩, hzAb, hidx, hsq⟩
  ·
    have hEc : (layer K).Characteristic := layer_characteristic
    have hEn : (layer K).Normal := inferInstance
    have hdisj := hs.disjoint hB
    have hle : S₂ ≤ centralizer (S₁ : Set K) := fun b hb =>
      mem_centralizer_iff.2 fun a ha => hs.commute a ha b hb
    let φ₁ : ↥S₁ ≃* alternatingGroup (Fin 6) := hs.iso.some.trans (hBA.trans eA)
    let φ₂ : ↥S₂ ≃* alternatingGroup (Fin 6) :=
      ((MulEquiv.subgroupCongr hs.conj_eq).trans
        (Subgroup.equivMapOfInjective S₁ (MulAut.conj z).toMonoidHom
          (MulAut.conj z).injective).symm).trans φ₁
    refine ⟨?_, Or.inl ⟨layer K, hEn, ⟨?_⟩, centralizer_layer_eq_bot hB.fitting_eq_bot⟩⟩
    ·
      let U' : Subgroup ↥(centralizer ({z} : Set K)) :=
        (normalizer (S₁ : Set K)).subgroupOf (centralizer ({z} : Set K))
      have hz2D : zz z * zz z = 1 := Subtype.ext hz2
      have hdisj' : Disjoint U' (zpowers (zz z)) := by
        rw [disjoint_iff, eq_bot_iff]
        intro x ⟨hxU, hxZ⟩
        rcases (mem_zpowers_iff_of_mul_self_eq_one hz2D).1 hxZ with h1 | h1
        · exact h1 ▸ one_mem _
        · exfalso
          have : (x : K) ∈ normalizer (S₁ : Set K) := hxU
          rw [h1] at this
          exact hs.z_not_mem_normalizer this
      have hsup' : U' ⊔ zpowers (zz z) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rcases hs.cover hB (x : K) with h1 | h1
        · exact mem_sup_left (show x ∈ U' from h1)
        · have h2 : zz z * x ∈ U' := h1
          have h3 : x = (zz z)⁻¹ * (zz z * x) := (inv_mul_cancel_left _ _).symm
          rw [h3]
          exact mul_mem (mem_sup_right (inv_mem (mem_zpowers _))) (mem_sup_left h2)
      refine ⟨U'.map θ'.toMonoidHom, ?_, ?_⟩
      · rw [disjoint_iff, show zpowers (Fin76b.zbarC K z) = (zpowers (zz z)).map θ'.toMonoidHom by
          rw [MonoidHom.map_zpowers]; rfl,
          ← Subgroup.map_inf _ _ θ'.toMonoidHom θ'.injective, disjoint_iff.1 hdisj',
          Subgroup.map_bot]
      · rw [show zpowers (Fin76b.zbarC K z) = (zpowers (zz z)).map θ'.toMonoidHom by
          rw [MonoidHom.map_zpowers]; rfl, ← Subgroup.map_sup, hsup', Subgroup.map_top]
        exact MonoidHom.range_eq_top.2 θ'.surjective
    · exact (MulEquiv.subgroupCongr hs.layer_eq).trans
        ((mulEquivProdSup hle (disjoint_iff.2 hdisj)).symm.trans (MulEquiv.prodCongr φ₁ φ₂))

end CFSG.EvenSporadicStandard.SolomonRed
