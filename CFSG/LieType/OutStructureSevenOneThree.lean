module

public import CFSG.LieType.OutStructureReductions
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenOneThreeRankTwoHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeOutPClosedOf

public section

namespace CFSG.LieType.OutStructure

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms

theorem sevenOneThree_pClosed_of_pRank_le_one
    {X : Type} [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {L : Subgroup X} (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hrk : CFSG.Open.pRank p L ≤ 1) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
      (L ⊔ Subgroup.centralizer (L : Set X)) := by
  haveI := hLn
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect ↥L := hL.1.1
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  have hq : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩
  have hnab : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.quotient_center_nonabelian hq
  have hcat : CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.isCatalogGroup_quotient_center hK L hq
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) ≤ 1 :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.pRank_quotient_center_le_one hp hp2 L hrk
  have hOut : ∀ S : Sylow p (Outer (↥L ⧸ Subgroup.center ↥L)),
      (S : Subgroup (Outer (↥L ⧸ Subgroup.center ↥L))).Normal :=
    sylow_normal_outer_of_pRank_le_one _ hL.1.2.1 hnab hcat p hp hp2 hrank
  have hOutL : ∀ S : Sylow p (Outer ↥L), (S : Subgroup (Outer ↥L)).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo.sylow_normal_of_injective
      (centerQuotient_outer_injective ↥L) hOut
  obtain ⟨R⟩ : Nonempty (Sylow p X) := inferInstance
  exact CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo.isPClosedMod_of_normal_sup_sylow R
    (CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.normal_sup_sup_centralizer_of_outer L R hOutL)

theorem sevenOneThree_threeRank_three_of_pRank_le_two
    {X : Type} [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3)
    (hL2 : CFSG.Open.pRank 3 L ≤ 2) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod 3
      (L ⊔ Subgroup.centralizer (L : Set X)) := by
  rcases lt_or_eq_of_le hL2 with hlt | heq
  · exact sevenOneThree_pClosed_of_pRank_le_one hK Nat.prime_three (by norm_num) hL hLn
      (by omega)
  · exact CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo.sevenOneThreeRankTwo_holds
      X hK L hL hLn heq hX3

theorem sevenOneThree_rankLeTwo_three
    {X : Type} [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hX2 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod 3
      (L ⊔ Subgroup.centralizer (L : Set X)) :=
  sevenOneThree_threeRank_three_of_pRank_le_two hK hL hLn (by omega)
    ((CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) (le_top : L ≤ ⊤)).trans hX2)

theorem sevenOneThree_threeRank_three_of_sevenOneSeven
    (h7 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneSeven)
    {X : Type} [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod 3
      (L ⊔ Subgroup.centralizer (L : Set X)) := by
  have hmono : CFSG.Open.pRank 3 L ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) le_top
  rcases lt_or_ge (CFSG.Open.pRank 3 L) 3 with hlt | hge
  · exact sevenOneThree_threeRank_three_of_pRank_le_two hK hL hLn hX3 (by omega)
  · have hL3 : CFSG.Open.pRank 3 L = 3 := le_antisymm (hmono.trans hX3) hge
    have hX3eq : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 :=
      le_antisymm hX3 (hge.trans hmono)
    rcases h7 X hK L hL hLn hL3 hX3eq with hU | hPSL
    ·
      haveI := hLn
      have hUn : (L ⊔ Subgroup.centralizer (L : Set X)).Normal := inferInstance
      exact ⟨_, hUn, le_rfl, ⟨0, by rw [Subgroup.relIndex_self, pow_zero]⟩, hU⟩
    ·
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      haveI : Group.IsPerfect ↥L := hL.1.1
      haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
      have hOutQ : ∀ S : Sylow 3 (Outer (↥L ⧸ Subgroup.center ↥L)),
          (S : Subgroup (Outer (↥L ⧸ Subgroup.center ↥L))).Normal := by
        obtain ⟨e⟩ := hPSL
        exact CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.sylow_normal_outer_of_mulEquiv e
          fun S => CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.sylow_normal_of_comm
            (fun a b => CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm
              (GaloisField 3 3) a b) S
      have hOutL : ∀ S : Sylow 3 (Outer ↥L), (S : Subgroup (Outer ↥L)).Normal :=
        CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo.sylow_normal_of_injective
          (centerQuotient_outer_injective ↥L) hOutQ
      obtain ⟨R⟩ : Nonempty (Sylow 3 X) := inferInstance
      exact CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo.isPClosedMod_of_normal_sup_sylow R
        (CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.normal_sup_sup_centralizer_of_outer L R hOutL)

end CFSG.LieType.OutStructure
