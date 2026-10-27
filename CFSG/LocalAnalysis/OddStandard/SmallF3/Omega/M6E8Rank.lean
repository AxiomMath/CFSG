module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Ctx
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8CStar
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Core
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Datum
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Outside
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6ShapesDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem m6e8_rank_of_u43 (h33 : Asc82Lemma33) (h63 : Asc82Lemma63) (hsh : Asc82Shapes)
    (hout : Asc82Outside) (hCh : Asc82AutCentChain3)
    {t : G} {L : Subgroup G} {y : G} {X Y T : Subgroup G} {r : G}
    (d : M6E8Datum t L y X Y T r) {I : Subgroup G}
    (hI : IsComponentIn I (centralizer ({r} : Set G))) (hJI : layerCent Y r ≤ I) (hIF : InF I)
    (hI6 : IsOmega6Minus I) (hyI : y ∉ centralizer (I : Set G)) :
    CFSG.GH74.sectionalTwoRank T ≤ 3 := by
  have hIC : InC I := ⟨r, d.orderOf_r, hI⟩
  have hIF' : InFStar I := Or.inl hIF
  have hIC' : InCStar I := m6e8_inCStar_of_u43 hsh d.setting hIC hIF' hI6
  have hRN : ∀ c ∈ T ⊓ centralizer ({r} : Set G), c ∈ normalizer (I : Set G) :=
    fun c hc => sec64_mem_normalizer h63 d.setting d.hyp62 d.orderOf_r hI hIF' hc.2
  have hyH : r ∈ centralizer (I : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (hI.1 ha)
  have hRH : ∀ c ∈ T ⊓ centralizer ({r} : Set G),
      ∀ h ∈ centralizer (I : Set G), c * h * c⁻¹ ∈ centralizer (I : Set G) := by
    intro c hc h hh
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hb : c⁻¹ * a * c ∈ I :=
      (Subgroup.mem_normalizer_iff''.mp (hRN c hc) a).mp ha
    have hcomm : (c⁻¹ * a * c) * h = h * (c⁻¹ * a * c) :=
      Subgroup.mem_centralizer_iff.mp hh (c⁻¹ * a * c) hb
    calc a * (c * h * c⁻¹)
        = c * ((c⁻¹ * a * c) * h) * c⁻¹ := by group
        _ = c * (h * (c⁻¹ * a * c)) * c⁻¹ := by rw [hcomm]
        _ = (c * h * c⁻¹) * a := by group
  have hU : IsCyclic ↥(T ⊓ centralizer ({r} : Set G) ⊓ centralizer (I : Set G)) :=
    sec64_isCyclic_U h33 d.setting hI hIC' hIF' d.isPGroup_T d.mem_R.1
  have hcfg : Sec64Cfg T (centralizer (I : Set G)) y r :=
    ⟨d.isPGroup_T, d.hy, d.orderOf_r, d.comm_yr, d.hyT, d.mem_R.1, hyI, hyH, hRH, hU⟩
  have hXq : IsQuasisimple ↥X := by
    obtain ⟨x₀, -, hXc'⟩ := d.hXC
    exact hXc'.isQuasisimple
  let R' : Subgroup G := T ⊓ centralizer ({r} : Set G)
  have hR'p : IsPGroup 2 ↥R' := d.isPGroup_T.to_le inf_le_left
  have hR'le : R' ≤ normalizer (I : Set G) ⊓ centralizer (X : Set G) :=
    fun c hc => ⟨hRN c hc, d.hT.1 hc.1⟩
  have hCh' := hCh G X (layerCent Y r) I hXq d.quasi hI.isQuasisimple d.hX29 d.omega5 hI6
    d.xj hJI R' hR'p hR'le
  have htri : Sec64Tri T (centralizer (I : Set G)) r := by
    unfold Sec64Tri
    rcases hCh' with h | h
    · exact Or.inl h
    · refine Or.inr (Or.inl ⟨?_, h⟩)
      intro _ h8 _ _
      have := d.card_gt
      omega
  have hout' : Sec64Out T (centralizer (I : Set G)) r := sec64_core hout hcfg htri
  unfold Sec64Out at hout'
  rcases hout' with h | h
  · exfalso
    have h3 : 3 ≤ CFSG.Open.pRank 2 T :=
      CFSG.SectionRank.le_pRank (p := 2) (by norm_num) inf_le_left d.hab (k := 3)
        (by rw [d.h8]; norm_num)
    omega
  · exact h.2

end CFSG.OddStandard.SmallF3.Omega
