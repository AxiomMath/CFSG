module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Tools
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Inner
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitRankFour

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Q81

open CFSG Subgroup CFSG.ABGLocalTools

section Map

variable {G G' : Type} [Group G] [Group G'] (φ : G ≃* G')

theorem map_centralizer_equiv (s : Set G) :
    (centralizer s).map φ.toMonoidHom = centralizer (φ.toMonoidHom '' s) := by
  ext y
  obtain ⟨x, rfl⟩ := φ.surjective y
  constructor
  · rintro ⟨x', hx', hx'e⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← hx'e]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hx' a ha]
  · intro hy
    refine ⟨x, mem_centralizer_iff.mpr fun a ha => φ.injective ?_, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hy (φ a) ⟨a, ha, rfl⟩

theorem centralizer_map_equiv (H : Subgroup G) :
    centralizer ((H.map φ.toMonoidHom : Subgroup G') : Set G') =
      (centralizer (H : Set G)).map φ.toMonoidHom := by
  rw [coe_map, map_centralizer_equiv]

theorem map_centralizer_singleton_equiv (x : G) :
    (centralizer ({x} : Set G)).map φ.toMonoidHom = centralizer {φ.toMonoidHom x} := by
  rw [map_centralizer_equiv, Set.image_singleton]

theorem map_normalizer_equiv (H : Subgroup G) :
    (normalizer (H : Set G)).map φ.toMonoidHom =
      normalizer ((H.map φ.toMonoidHom : Subgroup G') : Set G') := by
  ext y
  obtain ⟨x, rfl⟩ := φ.surjective y
  have key : ∀ g : G, g ∈ normalizer (H : Set G) ↔
      φ g ∈ normalizer ((H.map φ.toMonoidHom : Subgroup G') : Set G') := by
    intro g
    simp only [mem_normalizer_iff]
    constructor
    · intro hg b
      obtain ⟨a, rfl⟩ := φ.surjective b
      have e : φ g * φ a * (φ g)⁻¹ = φ (g * a * g⁻¹) := by rw [map_mul, map_mul, map_inv]
      rw [e, mem_map_equiv, mem_map_equiv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      exact hg a
    · intro hg a
      have h1 := hg (φ a)
      have e : φ g * φ a * (φ g)⁻¹ = φ (g * a * g⁻¹) := by rw [map_mul, map_mul, map_inv]
      rw [e, mem_map_equiv, mem_map_equiv, MulEquiv.symm_apply_apply,
        MulEquiv.symm_apply_apply] at h1
      exact h1
  constructor
  · rintro ⟨x', hx', hx'e⟩
    rw [← hx'e]
    exact (key x').mp hx'
  · intro hx
    exact ⟨x, (key x).mpr hx, rfl⟩

theorem map_center_equiv : (center G).map φ.toMonoidHom = center G' := by
  ext y
  obtain ⟨x, rfl⟩ := φ.surjective y
  constructor
  · rintro ⟨x', hx', hx'e⟩
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := φ.surjective g
    rw [← hx'e]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx' g']
  · intro hy
    refine ⟨x, mem_center_iff.mpr fun g => φ.injective ?_, rfl⟩
    rw [map_mul, map_mul]
    exact mem_center_iff.mp hy (φ g)

theorem map_layer_equiv : (layer G).map φ.toMonoidHom = layer G' := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← map_le_iff_le_comap]
    exact le_sSup (LocalCores.isComponent_map_mulEquiv φ hK)
  · refine sSup_le fun K hK => ?_
    have hle : K.map φ.symm.toMonoidHom ≤ layer G :=
      le_sSup (LocalCores.isComponent_map_mulEquiv φ.symm hK)
    calc K = (K.map φ.symm.toMonoidHom).map φ.toMonoidHom := by
          rw [map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G' by
            ext; simp, map_id]
      _ ≤ (layer G).map φ.toMonoidHom := map_mono hle

variable [Finite G] [Finite G']

theorem map_layerIn_equiv (H : Subgroup G) :
    (GSThmB.layerIn H).map φ.toMonoidHom = GSThmB.layerIn (H.map φ.toMonoidHom) := by
  refine GSThmB.OddQuot.map_layerIn φ.toMonoidHom ?_ H
  rw [(MonoidHom.ker_eq_bot_iff _).mpr φ.injective, card_bot]
  norm_num

theorem IsInnDiag.map {Q I : Subgroup G} (hI : IsInnDiag Q I) :
    IsInnDiag (Q.map φ.toMonoidHom) (I.map φ.toMonoidHom) where
  le := map_mono hI.le
  centralizer_le := by
    rw [centralizer_map_equiv]
    exact map_mono hI.centralizer_le
  le_normalizer := by
    rw [← map_normalizer_equiv]
    exact map_mono hI.le_normalizer
  mul_mem := by
    intro x' hx' y' hy' hxI hyI
    rw [← map_normalizer_equiv] at hx' hy'
    obtain ⟨x, hx, rfl⟩ := hx'
    obtain ⟨y, hy, rfl⟩ := hy'
    have hxI' : x ∉ I := fun h => hxI (mem_map_of_mem _ h)
    have hyI' : y ∉ I := fun h => hyI (mem_map_of_mem _ h)
    rw [← map_mul]
    exact mem_map_of_mem _ (hI.mul_mem x hx y hy hxI' hyI')
  inner_b := by
    rintro _ ⟨x, hxI, rfl⟩ hx2 hxC hlie
    have hx2' : x * x = 1 := φ.injective (by simpa using hx2)
    have hxC' : x ∉ centralizer (Q : Set G) := by
      intro h
      apply hxC
      rw [centralizer_map_equiv]
      exact mem_map_of_mem _ h
    have hQx : (Q ⊓ centralizer {x}).map φ.toMonoidHom =
        Q.map φ.toMonoidHom ⊓ centralizer {φ.toMonoidHom x} := by
      rw [map_inf_eq _ _ _ φ.injective, map_centralizer_singleton_equiv]
    have hlie' : Blueprint.LieModel ↥(GSThmB.layerIn (Q ⊓ centralizer {x})) .PSL 2 3 2 := by
      rw [← hQx, ← map_layerIn_equiv] at hlie
      exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        ((GSThmB.layerIn (Q ⊓ centralizer {x})).equivMapOfInjective _ φ.injective).symm hlie
    obtain ⟨B, hB, hZB, A, hAB, hA, hA8⟩ := hI.inner_b x hxI hx2' hxC' hlie'
    refine ⟨B.map φ.toMonoidHom, hQx ▸ map_mono hB, ?_, A.map φ.toMonoidHom, map_mono hAB,
      RankFour.isElemTwo_map _ hA, by rw [card_map_of_injective φ.injective, hA8]⟩
    have e : ↥B ≃* ↥(B.map φ.toMonoidHom) := B.equivMapOfInjective _ φ.injective
    refine eq_bot_of_card_eq _ ?_
    rw [← Nat.card_congr (centerCongr e).toEquiv, hZB, card_bot]

end Map

variable {X : Type} [Group X]

@[expose] def mbarConj (c : X) {β β' : X} (hc : c * β * c⁻¹ = β') : MBar β ≃* MBar β' :=
  UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
    (((centralizer ({β} : Set X)).equivMapOfInjective _ (MulAut.conj c).injective).trans
      (MulEquiv.subgroupCongr (show (centralizer ({β} : Set X)).map
        (MulAut.conj c).toMonoidHom = centralizer ({β'} : Set X) by
          rw [L415.map_conj_centralizer, hc])))

theorem mbarConj_mk (c : X) {β β' : X} (hc : c * β * c⁻¹ = β') {x : X}
    (hx : x ∈ centralizer ({β} : Set X)) (hx' : c * x * c⁻¹ ∈ centralizer ({β'} : Set X)) :
    mbarConj c hc (QuotientGroup.mk ⟨x, hx⟩) = QuotientGroup.mk ⟨c * x * c⁻¹, hx'⟩ := by
  rw [mbarConj, UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr_mk]
  rfl

end CFSG.ComponentClassification.HarrisLit.Q81
