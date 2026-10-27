module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem m6e8_exists_I (h63 : Asc82Lemma63) {t : G} {L : Subgroup G} {y : G}
    {X Y T : Subgroup G} {r : G} (d : M6E8Datum t L y X Y T r) :
    ∃ I : Subgroup G, IsComponentIn I (centralizer ({r} : Set G)) ∧ layerCent Y r ≤ I ∧ InF I := by
  have hJF : InF (layerCent Y r) := ⟨d.quasi, Or.inl (Or.inl d.omega5)⟩
  obtain ⟨K, hK, hJK⟩ :=
    d.setting.lBalance y r d.hy d.orderOf_r d.comm_yr (layerCent Y r) d.comp
  have hKF : InFStar K :=
    d.setting.a2 y r d.hy d.orderOf_r d.comm_yr (layerCent Y r) K d.comp hK hJK
      (inFStar_of_inF hJF)
  have hyC : y ∈ centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr d.comm_yr
  have hKy : K = CFSG.conjugate K y :=
    h63 G t L d.setting d.hyp62 r d.orderOf_r K (CFSG.conjugate K y) hK hKF
      (hK.conjugate hyC) (hKF.conjugate y)
  have hJK' : layerCent Y r ≤ K := by
    rw [← hKy, sup_idem] at hJK
    exact hJK
  exact ⟨K, hK, hJK', inF_of_le_of_inFStar hJK' hJF hKF⟩

end CFSG.OddStandard.SmallF3.Omega
