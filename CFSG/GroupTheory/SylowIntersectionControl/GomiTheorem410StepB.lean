module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLemma44
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410Type
public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBModule
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBCase
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBAThree
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBResidual
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBNaturalAlt
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBBlock
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBType
import CFSG.GroupTheory.ConjugatePairSubnormality
import CFSG.Quasithin.Background.GoldschmidtE23Blocks

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup

open scoped IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω}
  {hyp : Subgroup Ω → Prop} {G : Subgroup Ω}

private theorem pCore_two_eq_bot_of_card_eq_three_basm {T : Type*} [Group T]
    (h3 : Nat.card T = 3) : CFSG.pCore 2 T = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold CFSG.pCore
  rw [sSup_eq_bot]
  intro K hK
  obtain ⟨-, hK2⟩ := hK
  have hdvd : Nat.card K ∣ 3 := by
    rw [← h3]
    exact Subgroup.card_subgroup_dvd_card K
  rcases hK2.card_eq_or_dvd with h1 | h2
  · exact Subgroup.card_eq_one.mp h1
  · exact absurd (h2.trans hdvd) (by norm_num)

theorem Gomi410Cex.exists_twoComponent (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    (h43 : GomiHyp43 G) (h31 : GomiFact31) (h33 : GomiFact33) (h37 : GomiFact37Two)
    (h44 : GomiLemma44) {S X : Subgroup Ω} (hS : IsSylowTwoOf S G)
    (hX : IsGomiSingularSubgroup G S X) :
    ∃ B : Subgroup Ω, IsGomiTwoComponent G B ∧ ⁅pCoreOf 2 G, B⁆ ≤ gomiV G ∧
      IsGomi410Type G B := by
  obtain ⟨L, H, W, hset⟩ := h.exists_isGomi410bSetting hfZ hchar hmono hS hX
  have := hset.isMulCommutative
  obtain ⟨hW2, hY, hP, -, -⟩ := hset.moduleSetting hS
  rcases exists_binaryNaturalSL_or_isComponent h31 h33 hW2 hY hP with
    ⟨N, hNY, hNsub, hN, hnat⟩ | ⟨M, hMY, hMc, hM2, hMJ, hMP⟩
  · obtain ⟨e3, hreal⟩ := isAlt_three_and_realizes_altDn_three hN hnat
    have hcardT : Nat.card ↥(twoResidual N) = 3 := by
      obtain ⟨e⟩ := e3
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hQ2 : CFSG.pCore 2 ↥(twoResidual N) = ⊥ :=
      pCore_two_eq_bot_of_card_eq_three_basm hcardT
    have hTsub : ((twoResidual N).subgroupOf (autOn H W)).IsSubnormal :=
      isSubnormal_subgroupOf_trans (twoResidual_le N) hNY
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidual_le N)).mpr
          (le_normalizer_twoResidual N)).isSubnormal hNsub
    obtain ⟨B, hBL, hBsub, hBres, hBM⟩ :=
      hset.exists_autOn_eq hS ((twoResidual_le N).trans hNY) hTsub (twoResidual_twoResidual N)
    have hMq : CFSG.IsQuasisimple ↥(twoResidual N) ∨
        ((Nat.card ↥(twoResidual N)).Prime ∧ Odd (Nat.card ↥(twoResidual N))) := by
      refine Or.inr ⟨?_, ?_⟩ <;> rw [hcardT] <;> norm_num
    have hBcomp := hset.isGomi410bComponent hBL hBsub hBres hBM hQ2 hMq
    rw [← hBM] at e3 hreal
    have hnatB : IsNaturalAltModule ↥B 1 :=
      isNaturalAltModule_of_realizes (n := 1) hBcomp.le_normalizer hBcomp.inf_centralizer_eq
        hBcomp.commutator_eq e3 hreal
    exact (h.not_block (hasGomiBlock_of_isGomiTwoComponent hBcomp.twoComponent
      hBcomp.commutator_pCoreOf_le (Or.inr ⟨1, le_rfl, hnatB⟩))).elim
  · have hMq : CFSG.IsQuasisimple ↥M :=
      CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMY).symm hMc.1
    have hMres : twoResidual M = M :=
      le_antisymm (twoResidual_le M)
        (CFSG.Quasithin.GE23.le_twoResidual_of_perfect le_rfl hMq.1)
    obtain ⟨B, hBL, hBsub, hBres, hBM⟩ := hset.exists_autOn_eq hS hMY hMc.2 hMres
    have hBcomp := hset.isGomi410bComponent hBL hBsub hBres hBM hM2 (Or.inl hMq)
    rcases hset.isGomi410Type_or_hasGomiBlock hS h43 h37 h44 hMY hMc hM2 hMJ hMP hBcomp with
      htype | hblock
    · exact ⟨B, hBcomp.twoComponent, hBcomp.commutator_pCoreOf_le, htype⟩
    · exact (h.not_block hblock).elim

end CFSG.GroupTheory
