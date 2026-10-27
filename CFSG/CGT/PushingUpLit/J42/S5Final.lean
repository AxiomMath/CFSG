module

public import CFSG.CGT.PushingUpLit.J42.S5Ext
public import CFSG.CGT.PushingUpLit.J42.S5Mod
public import CFSG.CGT.PushingUpLit.J42.S5Nf
public import CFSG.CGT.PushingUpLit.J42.S5Halves

set_option linter.unusedSectionVars false

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.GH74 CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin CFSG.Quasithin.G6 Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : SolCfg G M X 2)

namespace SolCfg

theorem gen4_M (hR : RSmall S) (hrbot : rOf M X = ⊥) : SectionalTwoRankLE ↥M 4 := by
  have hQW : pCoreOf 2 M = S.D.W := S.pCoreOf_eq_W_of_rOf_bot hrbot
  let Q' : Subgroup ↥M := (pCoreOf 2 M).subgroupOf M
  let β' : ↥Q' ≃* ↥(coreMod 5) :=
    ((Subgroup.subgroupOfEquivOfLe (pCoreOf_le_self M)).trans
      (MulEquiv.subgroupCongr hQW)).trans S.D.β
  refine gen4_of_alt_module Q' S.θ β' (fun m q hq => ?_) (fun m q => ?_) (fun m hm => ?_)
  · exact pCoreOf_normalized M m.2 hq
  · have hqW : ((q : ↥M) : G) ∈ S.D.W := hQW ▸ Subgroup.mem_subgroupOf.1 q.2
    have hW' : (m : G) * ((q : ↥M) : G) * (m : G)⁻¹ ∈ S.D.W := S.W_normalized m.2 hqW
    exact S.θ_spec m ⟨((q : ↥M) : G), hqW⟩ hW'
  · exact S.mem_Q_of_theta_eq_one hR m.2 hm

theorem gen4_of_le_M (hR : RSmall S) (hrbot : rOf M X = ⊥) (hA : ∃ m : ↥M, sign (S.θ m) = -1)
    (hKM : CGOf S.x0 ≤ M) : SectionalTwoRankLE G 4 := by
  obtain ⟨T, hT⟩ := (S.isPGroup_S0 hR).exists_le_sylow
  exact gen4_of_sylow_le T ((S.le_centralizer_x0 hR hrbot hA T hT).trans hKM)
    (S.gen4_M hR hrbot)

theorem gen4_of_not_le_M (hB : S.CaseB) : SectionalTwoRankLE G 4 := by
  obtain ⟨D⟩ := hB.nonempty_extraData
  obtain ⟨T, hT⟩ := (S.isPGroup_S0 hB.rsmall).exists_le_sylow
  exact gen4_of_sylow_le T (S.le_centralizer_x0 hB.rsmall hB.rbot hB.odd T hT)
    (gen4_of_extraData D)

end SolCfg

theorem jankoU42Gen4S5ROne_holds : JankoU42Gen4S5ROne := by
  intro G _ _ M X S _ hT hR _ hA hrbot
  by_cases hKM : CGOf S.x0 ≤ M
  · exact S.gen4_of_le_M hR hrbot hA hKM
  · exact S.gen4_of_not_le_M ⟨hT, hR, hrbot, hA, hKM⟩

end CFSG.CGT.PushingUpLit.SolK
