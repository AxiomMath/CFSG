module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Ctx
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8LayerEq
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Chain
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6ShapesDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private theorem m6e8_le_centralizer_pair {K : Subgroup G} {x y : G}
    (hx : K ≤ centralizer ({x} : Set G)) (hy : K ≤ centralizer ({y} : Set G)) :
    K ≤ centralizer ({x, y} : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rcases hw with rfl | hw
  · exact Subgroup.mem_centralizer_iff.mp (hx hz) _ (Set.mem_singleton _)
  · rw [Set.mem_singleton_iff.mp hw]
    exact Subgroup.mem_centralizer_iff.mp (hy hz) _ (Set.mem_singleton _)

private theorem m6e8_centralizer_pair_le_right (x y : G) :
    centralizer ({x, y} : Set G) ≤ centralizer ({y} : Set G) :=
  Subgroup.centralizer_le
    (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem x (Set.mem_singleton y)))

theorem m6e8_dichotomy (h61 : Asc82Lemma61) (h63 : Asc82Lemma63) (hsh : Asc82Shapes)
    {t : G} {L : Subgroup G} {y : G} {X Y T : Subgroup G} {r : G}
    (d : M6E8Datum t L y X Y T r) {I : Subgroup G}
    (hI : IsComponentIn I (centralizer ({r} : Set G))) (hJI : layerCent Y r ≤ I) (hIF : InF I) :
    I = layerCent Y r ∨ (IsOmega6Minus I ∧ y ∉ centralizer (I : Set G)) := by
  have hSI : Sec3SettingLB G r I := sec3SettingLB_of_component d.setting d.orderOf_r hI hIF
  have hIq : IsQuasisimple ↥I := hI.isQuasisimple
  have hJq : IsQuasisimple ↥(layerCent Y r) := d.quasi
  have hyr : y ∈ centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr d.comm_yr
  rcases hsh G r I hSI with h5I | h6pI | h6mI
  · left
    exact (eq_of_le_of_ctrQ_eq hIq hJI (by
      rw [ctrQ_of_psp4 hJq d.omega5, ctrQ_of_psp4 hIq h5I])).symm
  · exfalso
    have hJe : layerCent I y = layerCent Y r := m6e8_layerCent_eq d hI hJI h6pI
    have h5 : IsOmega5 (layerCent I y) := by rw [hJe]; exact d.omega5
    obtain ⟨I', hI'c, hI'le, hI'sh⟩ := h61 G r I hSI h6pI y d.hy hyr h5
    have hI'q : IsQuasisimple ↥I' := hI'c.isQuasisimple
    have hI'F : InFStar I' := by
      unfold InFStar IsFStarGroup IsFGroup SmallF3OmegaQuotient
      rcases hI'sh with h5' | h6p'
      · exact Or.inl ⟨hI'q, Or.inl (Or.inl h5')⟩
      · exact Or.inl ⟨hI'q, Or.inl (Or.inr (Or.inl h6p'))⟩
    have hI'Y : I' = Y := h63 G t L d.setting d.hyp62 y d.hy I' Y hI'c hI'F d.hYc d.hYF
    have hYsh : IsOmega5 Y ∨ IsOmega6Plus Y := hI'Y ▸ hI'sh
    have hYq : IsQuasisimple ↥Y := d.hYc.isQuasisimple
    have hYu : ctrQ Y = 3265920 := ctrQ_of_u43 hYq d.hY6
    rcases hYsh with h5Y | h6pY
    · rw [ctrQ_of_psp4 hYq h5Y] at hYu
      omega
    · rw [ctrQ_of_l43 hYq h6pY] at hYu
      omega
  · right
    refine ⟨h6mI, ?_⟩
    intro hyI
    have hy_le : I ≤ centralizer ({y} : Set G) := by
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hyI a ha)
    have hle : I ≤ centralizer ({y, r} : Set G) := m6e8_le_centralizer_pair hy_le hI.1
    have hI' : IsComponentIn I (centralizer ({y, r} : Set G)) :=
      hI.mono hle (m6e8_centralizer_pair_le_right y r)
    have hJI' : layerCent Y r = I := d.comp.eq_of_le hI' hJI
    have hJu : ctrQ (layerCent Y r) = 25920 := ctrQ_of_psp4 hJq d.omega5
    have hIu : ctrQ I = 3265920 := ctrQ_of_u43 hIq h6mI
    rw [hJI'] at hJu
    omega

end CFSG.OddStandard.SmallF3.Omega
