module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15NoXBlockBorel
public import CFSG.Quasithin.Background.A4V

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem t_le_borelPre (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)} :
    T ≤ borelPre T Ls := by
  intro t ht
  rw [borelPre, Subgroup.mem_comap]
  exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem (toStar T) ht)

theorem gnC_le_centralizer_T1 (hX : GNSetting X T) (hg : IsGNPair T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} :
    (gnC (T.subgroupOf (borelPre T Ls))).map (Subgroup.subtype (borelPre T Ls)) ≤
      Subgroup.centralizer (T₁ : Set X) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have hT1T : T₁ ≤ T := hg.le_center.trans (CFSG.Quasithin.A4.omegaOneCenterOf_le T)
  have htT : t ∈ T := hT1T ht
  have htX1 : t ∈ borelPre T Ls := t_le_borelPre hX htT
  have htZ : t ∈ centerOf T := CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf T (hg.le_center ht)
  have htSq : t ^ 2 = 1 := CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf (hg.le_center ht)
  have htSub : (⟨t, htX1⟩ : ↥(borelPre T Ls)) ∈ T.subgroupOf (borelPre T Ls) := by
    rwa [Subgroup.mem_subgroupOf]
  have htCent : (⟨t, htX1⟩ : ↥(borelPre T Ls)) ∈ Subgroup.centralizer
      ((T.subgroupOf (borelPre T Ls) : Subgroup ↥(borelPre T Ls)) :
        Set ↥(borelPre T Ls)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzT : (z : X) ∈ T := Subgroup.mem_subgroupOf.mp hz
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp htZ.2 (z : X) hzT)
  have htω : (⟨t, htX1⟩ : ↥(borelPre T Ls)) ∈
      omegaOneCenterOf (T.subgroupOf (borelPre T Ls)) := by
    unfold omegaOneCenterOf omegaOneOf
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [centerOf]
      exact Subgroup.mem_inf.mpr ⟨htSub, htCent⟩
    · exact Subtype.ext htSq
  have htV : (⟨t, htX1⟩ : ↥(borelPre T Ls)) ∈
      gnV (T.subgroupOf (borelPre T Ls)) :=
    Subgroup.subset_normalClosure htω
  have hcomm : (⟨t, htX1⟩ : ↥(borelPre T Ls)) * y = y * ⟨t, htX1⟩ :=
    Subgroup.mem_centralizer_iff.mp hy _ htV
  simpa using congrArg Subtype.val hcomm

end CFSG.LocalAnalysis.RankThreeUC.S15
