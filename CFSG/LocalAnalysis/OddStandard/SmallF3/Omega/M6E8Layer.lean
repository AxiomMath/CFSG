module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Facts
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Trans
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Helpers
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem m6e8_exists_datum (h63 : Asc82Lemma63) (hF1 : Asc82E8LayerFact)
    {t : G} {L : Subgroup G} {y : G} {X Y T : Subgroup G} (c : M6E8Ctx t L y X Y T) :
    ∃ r : G, M6E8Datum t L y X Y T r := by
  classical
  have hXq : IsQuasisimple ↥X := by
    obtain ⟨x, -, hXc⟩ := c.hXC
    exact hXc.isQuasisimple
  have hYq : IsQuasisimple ↥Y := c.hYc.isQuasisimple
  obtain ⟨⟨r0, hr0R, hr05⟩, hall⟩ :=
    hF1 G X Y (T ⊓ centralizer ({y} : Set G)) hXq hYq c.hX29 c.hY6 c.hXY
      c.isPGroup_R (c.R_le_normalizer h63) c.relIndex_four
  have hr0y : r0 ∉ Subgroup.zpowers y := by
    intro hmem
    have hr0cent : r0 ∈ centralizer (Y : Set G) :=
      Subgroup.zpowers_le.mpr c.y_mem_centralizer_Y hmem
    have hY5 : IsOmega5 Y := by
      rw [← sec5_layerCent_of_mem_centralizer hYq hr0cent]
      exact hr05
    have h1 := ctrQ_of_psp4 hYq hY5
    have h2 := ctrQ_of_u43 hYq c.hY6
    omega
  obtain ⟨r, hrcase, hrR, hry, hrC⟩ :=
    m6e8_exists_centralizing c.isPGroup_T c.hyT c.hab c.h8 c.hne hr0R hr0y
  have hlayer : layerCent Y r = layerCent Y r0 := by
    rcases hrcase with h | h
    · rw [h]
    · rw [h]
      unfold layerCent
      rw [inf_centralizer_eq_of_mul_centralizer c.y_mem_centralizer_Y]
  have hJ5 : IsOmega5 (layerCent Y r) := by
    rw [hlayer]
    exact hr05
  obtain ⟨hJq, hXJ, hcent⟩ := hall r hrR hJ5
  refine ⟨r, ⟨c, hrR, hry, hrC, hJ5, hJq, hXJ, ?_, ?_⟩⟩
  · intro z hz
    have h := hcent hz
    rw [c.R_inf_cent_eq] at h
    exact h
  · have h1 : IsComponentIn (layerCent Y r) (Y ⊓ centralizer ({r} : Set G)) :=
      isComponentIn_layerCent (Or.inl hJ5)
    have hnorm : ∀ c' ∈ centralizer ({y} : Set G), CFSG.conjugate Y c' = Y := by
      intro c' hc'
      exact (h63 G t L c.setting c.hyp62 y c.hy Y (CFSG.conjugate Y c') c.hYc c.hYF
        (c.hYc.conjugate hc') (c.hYF.conjugate c')).symm
    have h2 := IsComponentIn.of_normal_inf_centralizer
      (L := Y) (N := centralizer ({y} : Set G)) (w := r) (J := layerCent Y r)
      c.hYc.1 hnorm h1
    rw [centralizer_pair_eq_inf]
    exact h2

end CFSG.OddStandard.SmallF3.Omega
