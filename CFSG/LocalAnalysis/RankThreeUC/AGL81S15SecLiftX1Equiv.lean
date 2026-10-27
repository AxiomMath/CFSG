module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
import CFSG.Quasithin.Background.C118Main
import CFSG.Quasithin.H13.NQCatA314ShortMap
import CFSG.Quasithin.Background.SimsD1TransBlock
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.LocalAnalysis.RankThreeUC.GN15JOutMapEquiv
import CFSG.Assembly.OrderReductions.NormalizerAuxiliary
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CharTwoTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.OrderReductions.NormalizerAuxiliary (centralizer_image_eq)

variable {G H : Type} [Group G] [Group H]

theorem gnV_map_mulEquiv (e : G ≃* H) (S : Subgroup G) :
    (gnV S).map e.toMonoidHom = gnV (S.map e.toMonoidHom) := by
  rw [gnV, gnV, Subgroup.map_normalClosure _ e.toMonoidHom e.surjective,
    CFSG.Quasithin.omegaOneCenterOf_map_of_injective (f := e.toMonoidHom) e.injective,
    Subgroup.coe_map]

theorem gnC_map_mulEquiv (e : G ≃* H) (S : Subgroup G) :
    (gnC S).map e.toMonoidHom = gnC (S.map e.toMonoidHom) := by
  rw [gnC, gnC, ← centralizer_image_eq, ← gnV_map_mulEquiv, Subgroup.coe_map,
    MulEquiv.coe_toMonoidHom]

private def starEquiv (e : G ≃* H) (S : Subgroup G) :
    G ⧸ gnC S ≃* H ⧸ gnC (S.map e.toMonoidHom) :=
  QuotientGroup.congr (gnC S) (gnC (S.map e.toMonoidHom)) e (gnC_map_mulEquiv e S)

private theorem starEquiv_toStar (e : G ≃* H) (S : Subgroup G) (x : G) :
    starEquiv e S (toStar S x) = toStar (S.map e.toMonoidHom) (e x) :=
  QuotientGroup.congr_mk _ _ e (gnC_map_mulEquiv e S) x

private theorem map_gnImg_mulEquiv (e : G ≃* H) (S Y : Subgroup G) :
    (gnImg S Y).map (starEquiv e S).toMonoidHom =
      gnImg (S.map e.toMonoidHom) (Y.map e.toMonoidHom) := by
  rw [gnImg, gnImg, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem gnYComponent_map_starEquiv (e : G ≃* H) {S S₁ S₂ : Subgroup G}
    {K : Subgroup (G ⧸ gnC S)} (hK : GNYComponent S S₁ S₂ K) :
    GNYComponent (S.map e.toMonoidHom) (S₁.map e.toMonoidHom) (S₂.map e.toMonoidHom)
      (K.map (starEquiv e S).toMonoidHom) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := CFSG.isComponentOf_map_mulEquiv (starEquiv e S) hK.1
    rwa [Subgroup.map_top_of_surjective (starEquiv e S).toMonoidHom
      (starEquiv e S).surjective] at h
  · rw [Subgroup.coe_map, MulEquiv.coe_toMonoidHom, centralizer_image_eq, ← map_gnImg_mulEquiv,
      Subgroup.map_le_map_iff_of_injective (f := (starEquiv e S).toMonoidHom)
        (starEquiv e S).injective]
    exact hK.2.1
  · rw [← Subgroup.map_equiv_normalizer_eq, ← map_gnImg_mulEquiv,
      Subgroup.map_le_map_iff_of_injective (f := (starEquiv e S).toMonoidHom)
        (starEquiv e S).injective]
    exact hK.2.2

private theorem map_ystar_le (e : G ≃* H) (S S₁ S₂ : Subgroup G) :
    (Ystar S S₁ S₂).map (starEquiv e S).toMonoidHom ≤
      Ystar (S.map e.toMonoidHom) (S₁.map e.toMonoidHom) (S₂.map e.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap, Ystar]
  refine iSup₂_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap, Ystar]
  exact le_iSup₂_of_le (K.map (starEquiv e S).toMonoidHom) (gnYComponent_map_starEquiv e hK) le_rfl

theorem gnSetting_map_mulEquiv [Finite G] [Finite H] (e : G ≃* H) {S : Subgroup G}
    (h : GNSetting G S) : GNSetting H (S.map e.toMonoidHom) where
  kGroup := CFSG.IsKGroup.of_mulEquiv h.kGroup e.symm
  sylow := by
    obtain ⟨-, h2, hi⟩ := h.sylow
    refine ⟨le_top, h2.map e.toMonoidHom, ?_⟩
    have h1 : ((S.map e.toMonoidHom).subgroupOf ⊤).index = (S.subgroupOf ⊤).index := by
      change (S.map e.toMonoidHom).relIndex ⊤ = S.relIndex ⊤
      rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right,
        Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
    rwa [h1]
  charTwo := by
    have h1 := CFSG.QuasithinUnique.Ch1.charTwo_map_mulEquiv e h.charTwo
    rwa [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h1
  noXBlock := fun Y hY hB => by
    have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
    refine h.noXBlock (Y.map e.symm.toMonoidHom) ?_ ⟨?_, ?_⟩
    · have h1 := hY.map e.symm.toMonoidHom
      rwa [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] at h1
    · exact CFSG.QuasithinUnique.Setup.Wreath.IsShort2.map_of_injective _ hinj hB.1
    · rcases hB.2 with ⟨n, hn, h'⟩ | ⟨n, hn, h'⟩
      · exact Or.inl ⟨n, hn, CFSG.Quasithin.H13.NQCat.A314D.IsLin2Type.map_of_injective' _ hinj h'⟩
      · exact Or.inr ⟨n, hn, (CFSG.Quasithin.SimsD1.TransBlock.isAltType_map_iff _ hinj Y
          (2 * n + 1)).mpr h'⟩

theorem gnFactor_map_mulEquiv [Finite G] [Finite H] (e : G ≃* H) {S S₁ S₂ : Subgroup G}
    (h : GNFactor S S₁ S₂) :
    GNFactor (S.map e.toMonoidHom) (S₁.map e.toMonoidHom) (S₂.map e.toMonoidHom) := by
  intro x
  obtain ⟨a, ha, y, hy, b, hb, hx⟩ := h (e.symm x)
  refine ⟨e a, ?_, e y, ?_, e b, ?_, ?_⟩
  · rw [Subgroup.coe_map, MulEquiv.coe_toMonoidHom, centralizer_image_eq]
    exact Subgroup.mem_map_of_mem e.toMonoidHom ha
  · have h1 : starEquiv e S (toStar S y) ∈ (Ystar S S₁ S₂).map (starEquiv e S).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (show toStar S y ∈ Ystar S S₁ S₂ from hy)
    have h2 := map_ystar_le e S S₁ S₂ h1
    rw [starEquiv_toStar] at h2
    exact h2
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hb
  · rw [← map_mul, ← map_mul, ← hx, MulEquiv.apply_symm_apply]

theorem jOutCentralAt_map_mulEquiv [Finite G] [Finite H] (e : G ≃* H) {S : Subgroup G}
    (h : GN15.JOutCentralAt S) : GN15.JOutCentralAt (S.map e.toMonoidHom) := by
  have h1 := GN15.jOutBody_map_mulEquiv (starEquiv e S) h
  rw [map_gnImg_mulEquiv,
    ← CFSG.Quasithin.thompsonJ_map_of_injective' (f := e.toMonoidHom) e.injective S] at h1
  exact h1

theorem gnFactor_subgroupOf_subgroupOf {X : Type} [Group X] [Finite X] {T T₁ T₂ M : Subgroup X}
    (hg : GNGood T T₁ T₂) (hTM : T ≤ M) (X₂ : Subgroup ↥M) (hTX₂ : T.subgroupOf M ≤ X₂)
    (hX₂ : GNSetting ↥X₂ ((T.subgroupOf M).subgroupOf X₂))
    (hJ₂ : GN15.JOutCentralAt ((T.subgroupOf M).subgroupOf X₂)) :
    GNFactor ((T.subgroupOf M).subgroupOf X₂) ((T₁.subgroupOf M).subgroupOf X₂)
      ((T₂.subgroupOf M).subgroupOf X₂) := by
  set X₃ : Subgroup X := X₂.map M.subtype with hX₃
  let e : ↥X₂ ≃* ↥X₃ := X₂.equivMapOfInjective M.subtype M.subtype_injective
  have hmap : ∀ A : Subgroup X,
      (A.subgroupOf X₃).map e.symm.toMonoidHom = (A.subgroupOf M).subgroupOf X₂ := by
    intro A
    ext x
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
    exact Iff.rfl
  have hmap' : ∀ A : Subgroup X,
      ((A.subgroupOf M).subgroupOf X₂).map e.toMonoidHom = A.subgroupOf X₃ := by
    intro A
    ext x
    rw [Subgroup.mem_map_equiv, ← hmap A, Subgroup.mem_map_equiv, MulEquiv.symm_symm,
      MulEquiv.apply_symm_apply]
  have hTX₃ : T ≤ X₃ := fun t ht =>
    ⟨⟨t, hTM ht⟩, hTX₂ (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hX₃ : GNSetting ↥X₃ (T.subgroupOf X₃) := by
    have h1 := gnSetting_map_mulEquiv e hX₂
    rwa [hmap'] at h1
  have hJ₃ : GN15.JOutCentralAt (T.subgroupOf X₃) := by
    have h1 := jOutCentralAt_map_mulEquiv e hJ₂
    rwa [hmap'] at h1
  have h := gnFactor_map_mulEquiv e.symm (hg.factorSub X₃ hTX₃ hX₃ hJ₃)
  rwa [hmap, hmap, hmap] at h

end CFSG.LocalAnalysis.RankThreeUC.S15
