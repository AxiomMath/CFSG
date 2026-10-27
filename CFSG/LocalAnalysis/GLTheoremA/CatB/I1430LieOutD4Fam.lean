module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.ComponentClassification.CatLeaf CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.RankThree.PartOne.Sec66T
open CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux
  CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
open CFSG.HardMathSupport.Lang.E6Descent (twistedEntrywiseAut)
open CFSG.HardMathSupport.Dickson.Sec6 (FamD4 blueprintLieModel_D)
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (not_mem_range_conj_of_not_mem_innAutDerived)
open scoped commutatorElement

variable {T Pc : TauCeti.CFSGIndex → Prop} {tm tf tN : ℕ}


section Family

theorem lieSOut_d4W (hD : LieSOutTypeW T tm tf tN) : TypeOuterAt T Pc FamD4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | D r q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hr4 : r = 4 := hF
    subst hr4
    have hm := blueprintLieModel_D 4 q hv e
    have hC : StatedClassicalModel S .POmegaPlus 4 q.p q.exponent :=
      (lieModel_classical_iff (by decide)).mp hm
    obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
    rw [hq2] at hK
    obtain ⟨e'⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
    let E : S ≃* adjointGroup Tag.D4 K := e0.trans e'
    haveI := finite_adjointD4 K
    have hα3 : MulAut.congr E α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    have hαi : MulAut.congr E α ∉
        CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.D4 K) := by
      rintro ⟨c, hc'⟩
      refine not_mem_range_conj_of_not_mem_innAutDerived hα
        ⟨E.symm c, (MulAut.congr E).injective ?_⟩
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
      exact hc'
    exact hp.apply
      (typeLayer_congr E (typeLayer_adjointD4_outerW hD q.exponent_pos K hK _ hα3 hαi))
  | _ => exact hF.elim

end Family

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
