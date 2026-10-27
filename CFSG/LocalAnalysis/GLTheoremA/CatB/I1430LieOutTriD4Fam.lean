module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutTriD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.ComponentClassification.CatLeaf
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (card_projImage_glPi_three)
open CFSG.HardMathSupport.Dickson.Sec6 (FamTriD4 blueprintLieModel_trialityD4)
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (catalogIs_of_mulEquiv
  not_mem_range_conj_of_not_mem_innAutDerived)

variable {T Pc : TauCeti.CFSGIndex → Prop} {tm tf tN : ℕ}


section Family

theorem lieSOut_triD4W (hD : LieSOutTypeW T tm tf tN) : TypeOuterAt T Pc FamTriD4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | trialityD4 q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_trialityD4 q hv e
    have hexc : ChevalleyExceptionalModel S .trialityD4 q.p q.exponent := by
      rcases hm with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
      · exact absurd hcl (by decide)
      · exact hexc
      · exact absurd hree (by decide)
      · exact absurd h (by decide)
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e'⟩⟩ := exists_graphFixed_of_chevalleyExceptional hexc
    rw [hq2] at hK hσ
    haveI := finite_graphFixedRootGroup_D4 σ
    have hβ3 : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    have hβ : MulAut.congr e' α ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      rintro ⟨c, hc'⟩
      refine not_mem_range_conj_of_not_mem_innAutDerived hα
        ⟨e'.symm c, (MulAut.congr e').injective ?_⟩
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
      exact hc'
    exact hp.apply (typeLayer_congr e'
      (typeLayer_three_D4_outer_twoW hD q.exponent_pos hK σ hσ _ hβ3 hβ))
  | _ => exact hF.elim

end Family

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
