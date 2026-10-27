module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.DatumOf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.NcData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.VerticalIn
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaS

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

private theorem center_le_fusionZStar (L : Type*) [Group L] :
    Subgroup.center L ≤ Open.fusionZStar L := by
  rw [CFSG.ComponentClassification.Sol78.fusionZStar_eq_comap]
  intro x hx
  rw [Subgroup.mem_comap]
  exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective (pPrimeCore 2 L))
    (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)

theorem false_of_pump_vertical (hI : Phase1Inputs) (hA7 : TwoA7RankOne) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : Assembly.KProper Catalog G) (hcat : ¬ Catalog G) {y z : G} {K T N : Subgroup G}
    {q₀ : ℕ} (h : NcData G y z K T N q₀) {M : Subgroup G}
    (hM : Omega.IsComponentIn M (centralizer ({z} : Set G)))
    (hMy : M.map (MulAut.conj y).toMonoidHom = M) (hTM : T ≤ M) : False := by
  have hH : SectionRank.IsKGroupCat ↥(centralizer ({z} : Set G)) :=
    CFSG.ComponentClassification.GSThmB.isKGroupCat_of_ne_top' hKP
      (CFSG.ComponentClassification.Helpers.centralizer_ne_top_of_involution G hnonab z h.oz)
  have hyH : y ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (Subgroup.mem_centralizer_iff.mp (h.hK.1 h.hzK) y (by simp)).symm
  have hyM : y ∈ normalizer (M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMy
  have hM' : IsPComponent 2 (M.subgroupOf (centralizer ({z} : Set G))) :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hM.2
  have hT' : HarrisLit.IsTwoComponentIn T
      (centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G)) := by
    have hT := isTwoComponentIn_centralizer_pair h.hK h.hzK h.hzc h.hT
    rwa [centralizer_pair_eq_inf, inf_comm] at hT
  have hzT : z ∈ T := h.hNT h.hzN
  have hzM : z ∈ M := hTM hzT
  have hzcenter : (⟨z, hzM⟩ : ↥M) ∈ center ↥M := by
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hM.1 m.2) z (by simp)).symm
  have hzcentral : z ∈ (center ↥M).map M.subtype :=
    Subgroup.mem_map.2 ⟨⟨z, hzM⟩, hzcenter, rfl⟩
  have hzZ : z ∈ (Open.fusionZStar ↥M).map M.subtype :=
    Subgroup.map_mono (center_le_fusionZStar ↥M) hzcentral
  have hTypM : TypU ↥M :=
    typU_of_vertical_in hI hH hM.1 hM' h.oy hyH hyM hTM hT' h.hTypU h.oz hzT hzZ
  have hdatum : GS82PumpInputs.IsDatum q₀ z M N z :=
    isDatum_of_central (v := z) (c := z) h.oz hM (h.hNT.trans hTM) h.hqodd h.hq5 h.hSL
      h.oz h.hzN hzcentral
  exact false_of_datum_typU hI hA7 G hnonab hKP hcat q₀ h.hqodd h.hq5 z M N z hdatum hTypM

end CFSG.OddStandard.SmallF3.HypA2
