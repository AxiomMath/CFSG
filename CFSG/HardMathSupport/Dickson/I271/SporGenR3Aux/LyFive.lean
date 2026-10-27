module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.LyFive
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMShape
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.RankThree.PartOne CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem pConstrainedShape_of_fiveCoreAt' {S : Type*} [Group S] {w : S} (h : FiveCoreAt' w) :
    PConstrainedShape 5 (Subgroup.centralizer ({w} : Set S)) := by
  obtain ⟨Q, hQC, hQn, hQp, hQc⟩ := h
  refine ⟨Q, hQC, hQn, hQp, fun g hg => hQc g hg.1 fun q hq => ?_⟩
  exact (Subgroup.mem_centralizer_iff.1 hg.2 q hq).symm

section Ly


theorem pConstrainedShape_Ly_five (S : Type) [Group S]
    (hS : Nonempty (S ≃* NativeSporadic.Carrier .Ly)) {g : S} (hg : orderOf g = 5) :
    PConstrainedShape 5 (Subgroup.centralizer ({g} : Set S)) := by
  obtain ⟨eT⟩ := hS
  let eJ : S ≃* CFSG.Sporadic.Ly.J := eT.trans CFSG.Sporadic.Ly.lyEquivJ
  have hJ : FiveCoreAt (eJ g) :=
    LyFive.fiveCore_J (eJ g) (by rw [MulEquiv.orderOf_eq]; exact hg)
  have h' : FiveCoreAt' g := by
    have := @fiveCoreAt'_map CFSG.Sporadic.Ly.J inferInstance S _ eJ.symm (eJ g)
      (fiveCoreAt'_of_fiveCoreAt hJ)
    rwa [MulEquiv.symm_apply_apply] at this
  exact pConstrainedShape_of_fiveCoreAt' h'

end Ly

section LyLocal


theorem isLocallyOneBalancedAbs_Ly_five (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (S : Type) [Group S] [Finite S] (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic .Ly).Group)) :
    IsLocallyOneBalancedAbs 5 S := by
  haveI := hS
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hOutS : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ≤ 2 :=
    hOut S hS hnab .Ly he
  obtain ⟨h1, h2⟩ := sporadicOnePairHolds_Ly_five
  have he' : Nonempty (S ≃* NativeSporadic.Carrier .Ly) := ⟨he.some.trans (hBr .Ly).some.symm⟩
  exact isLocallyOneBalancedAbs_of_parts (by norm_num) (by norm_num) hcen hOutS (h1 S he')
    (h2 S he')

end LyLocal

end CFSG.HardMathSupport.Dickson.I271
