module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81COutRankOne
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeOutPClosedOf

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81COutRankOne

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree
open Subgroup

theorem isPClosedMod_component_of_pRank3_le_one_of_simple
    (hSimple : SimpleOutCommInnerRankOne)
    {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hK : CFSG.Open.IsKGroup X) {C : Subgroup X} (hC : CFSG.IsComponent C)
    (h3 : CFSG.Open.pRank 3 C ≤ 1) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
      ((C ⊔ Subgroup.centralizer (C : Set X)).subgroupOf
        (Subgroup.normalizer (C : Set X))) := by
  let N := Subgroup.normalizer (C : Set X)
  let L := C.subgroupOf N
  have hCN : C ≤ N := Subgroup.le_normalizer
  have hcomp : CFSG.IsComponent L := CFSG.LocalCores.component_overgroup hC hCN
  have hLn : L.Normal := Subgroup.normal_in_normalizer
  haveI := hLn
  have hKC : CFSG.Open.IsKGroup ↥C := hK.subgroup C
  have h3C : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) ≤ 1 := by
    rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h3
  have hqC : CFSG.Open.IsQuasisimple ↥C :=
    ⟨Group.isPerfect_def.mp hC.1.1, hC.1.2.1⟩
  have hOutC : ∀ S : Sylow p (Outer ↥C), (S : Subgroup (Outer ↥C)).Normal :=
    sylow_normal_out_of_pRank3_le_one_of_simple hSimple hqC hKC hp h3C
  have hOutL : ∀ S : Sylow p (Outer ↥L), (S : Subgroup (Outer ↥L)).Normal :=
    sylow_normal_outer_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCN) hOutC
  obtain ⟨R⟩ : Nonempty (Sylow p ↥N) := inferInstance
  have hnorm : ((R : Subgroup ↥N) ⊔ (L ⊔ Subgroup.centralizer (L : Set ↥N))).Normal :=
    normal_sup_sup_centralizer_of_outer L R hOutL
  have hres : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
      (L ⊔ Subgroup.centralizer (L : Set ↥N)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo.isPClosedMod_of_normal_sup_sylow R hnorm
  have heq : (L ⊔ Subgroup.centralizer (L : Set ↥N)) =
      (C ⊔ Subgroup.centralizer (C : Set X)).subgroupOf N := by
    dsimp only [L]
    rw [CFSG.centralizer_subgroupOf_eq C N hCN]
    rw [Subgroup.subgroupOf_sup hCN (Subgroup.centralizer_le_normalizer (C : Set X))]
  rwa [heq] at hres

section Certified

theorem isPClosedMod_component_of_pRank3_le_one
    {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hK : CFSG.Open.IsKGroup X) {C : Subgroup X} (hC : CFSG.IsComponent C)
    (h3 : CFSG.Open.pRank 3 C ≤ 1) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
      ((C ⊔ Subgroup.centralizer (C : Set X)).subgroupOf
        (Subgroup.normalizer (C : Set X))) :=
  isPClosedMod_component_of_pRank3_le_one_of_simple simpleOutCommInnerRankOne_holds
    hp hK hC h3

end Certified

end CFSG.LocalAnalysis.RankThreeUC.AGL81COutRankOne
