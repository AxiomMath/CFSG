module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Swap
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Out
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Shape
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonCatZ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonGen

public section

namespace CFSG.EvenSporadicStandard.SolomonRed

open Subgroup CFSG CFSG.LocalCores CFSG.Open

theorem solomonGen_of_cat {A : Type} [Group A] [IsSimpleGroup A]
    (hnab : ∃ a b : A, a * b ≠ b * a) (hsq : OutSq A) (hcat : CatNoAlmostSimpleZ2 A) :
    SolomonGen A := by
  intro K _ _ hK z hz hZ ⟨e⟩
  have hB := setting_of_equiv hnab hz hZ e
  have hne : z ≠ 1 := hB.z_ne
  rcases dichotomy hB with ⟨S, hS⟩ | ⟨S₁, S₂, hs⟩
  ·
    exfalso
    have := hS.simple
    have := hS.normal
    have hcatS : CFSG.Blueprint.Catalog ↥S :=
      CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK S (MonoidHom.id ↥S)
        Function.surjective_id
    exact hcat K S hS.normal hS.simple hcatS hS.cent z hz ⟨e⟩
  ·
    have hinj := embA_injective e
    have hBle : (embA e).range ≤ layer K := by
      rw [← hs.inf_eq]
      exact inf_le_left
    have hC : ∀ d ∈ centralizer ({z} : Set K), d ∈ normalizer (S₁ : Set K) → d ∈ layer K := by
      intro d hd hdN
      rcases mem_range_or_mul hnab hne e hd with h1 | h1
      · exact hBle h1
      · exfalso
        have h2 : d * z ∈ normalizer (S₁ : Set K) := layer_le_normalizer hs.comp (hBle h1)
        have h3 : z ∈ normalizer (S₁ : Set K) := by
          have := mul_mem (inv_mem hdN) h2
          simpa using this
        exact hs.z_not_mem_normalizer h3
    let φ : ↥S₁ ≃* A := hs.iso.some.trans (MonoidHom.ofInjective hinj).symm
    have hsq' : OutSq ↥S₁ := OutSq.of_mulEquiv φ.symm hsq
    have habel : OutAbel ↥S₁ := hsq'.abel
    have hall : ∀ y ∈ normalizer (S₁ : Set K), y ∈ layer K :=
      hs.normalizer_le_layer hB hC (fun y₁ hy₁ y₂ hy₂ => outCond_one habel hy₁ hy₂)
        (fun y hy => outCond_two hsq' hy)
    have hidx : (layer K).index = 2 := hs.index_layer hB hall
    have hEc : (layer K).Characteristic := layer_characteristic
    have hEn : (layer K).Normal := inferInstance
    let ψ : ↥S₂ ≃* A :=
      ((MulEquiv.subgroupCongr hs.conj_eq).trans
        (Subgroup.equivMapOfInjective S₁ (MulAut.conj z).toMonoidHom
          (MulAut.conj z).injective).symm).trans φ
    refine ⟨S₁, S₂, ⟨φ⟩, ⟨ψ⟩, hs.commute, disjoint_iff.2 (hs.disjoint hB), ?_, ?_, ?_,
      hs.conj_eq.symm⟩
    · rw [← hs.layer_eq]; exact hEn
    · rw [← hs.layer_eq]; exact hidx
    · rw [← hs.layer_eq]; exact hs.z_not_mem

end CFSG.EvenSporadicStandard.SolomonRed
