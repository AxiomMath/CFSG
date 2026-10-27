module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Reduce
public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.Assembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal
public import CFSG.LocalAnalysis.GL83PartI.I713.Final
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.ExcRankProofs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Yardstones.Md8ed6d263d89

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G}
  {M : Subgroup G}

theorem confinement_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G) (hloc : D1Local p P M)
    (hType : PTypeHyp p P M)
    (hpm : ∃ x : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement p M x) :
    ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M := by
  obtain ⟨x, hx⟩ := hpm
  obtain ⟨m, -, hpt⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_isPPoint hG.fc hloc hx
  have hab := (shape_p hp5 hK hG hloc hType hpt).abelian
  intro H hH h2
  exact confinement_of_abelian_p hp5 hK hG hloc hType hab hH h2

theorem pNonemptyConfinement_of_inputs (hK : P5KFacts) : YSPNonemptyConfinement := by
  intro G _ _ _ hnonab hKp hchar he hpre hD1 hD2 hFC p P M hp5 hloc hpm hType
  haveI : Fact p.Prime := ⟨hloc.beta.1⟩
  have hS : D1Global G := ⟨inferInstance, hnonab, hKp, hchar, he, hpre⟩
  have hG : P5Global G := ⟨hS, hD1, hD2, hFC⟩
  have hType' : PTypeHyp p P M := hType
  exact ⟨confinement_p hp5 hK hG hloc hType' hpm,
    fun x R K i hd => isLinTwoType_of_pPointData hp5 hK hG hloc hType' hd⟩

section Certificates



theorem pNonemptyConfinement_of_kfacts
    (h10 : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h11 : CFSG.LocalAnalysis.RankFourTheoremC.GL83NongenerationList)
    (h14 : CFSG.LocalAnalysis.RankThreeTheoremC.KFactWeakClosure) : YSPNonemptyConfinement :=
  pNonemptyConfinement_of_inputs
    ⟨h10, h11, CFSG.LocalAnalysis.RankFourTheoremC.gl83SignalizerAut_holds,
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.kFactInnerAction_holds,
      h14, GL83.I713.i_7_13_1_holds,
      CFSG.LocalAnalysis.RankFourTheoremC.PPointP.pPointExclusionFive_of_partI h10 h11
        CFSG.LocalAnalysis.RankFourTheoremC.gl83SignalizerAut_holds⟩

end Certificates

end CFSG.LocalAnalysis.RankFourTheoremC.P5
