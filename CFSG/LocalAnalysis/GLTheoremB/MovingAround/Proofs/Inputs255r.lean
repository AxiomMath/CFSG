module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB5
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM5
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM7

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs255r

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs k2Spor)
open CFSG.HardMathSupport.Dickson.BMRows (PCompCensus census_B_five_of_noComp census_M_five_of_noComp
  census_M_seven)
open CFSG.HardMathSupport.Dickson.I271 (TabBFiveBNoComp CentFiveBNoComp)
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem sporNoChevTwoDown_of_census {p : ℕ} (hp : p.Prime) {name : TauCeti.SporadicName} {Q : Type}
    [Group Q] (b : Q ≃* (TauCeti.CFSGIndex.sporadic name).Group) {P : TauCeti.CFSGIndex → Prop}
    (hC : PCompCensus p Q P) (hT : ∀ (T : Type) [Group T], catalogIs T P → ¬ IsChevSimple 2 T) :
    Inputs256.SporNoChevTwoDown p name := by
  rintro S _ _ ⟨e⟩ s hs I hI hc
  obtain ⟨hI', ⟨eI⟩⟩ := Inputs1415.comp_transport hp (e.trans b.symm) hI
  exact hT _ (hC _ (by rw [MulEquiv.orderOf_eq, hs]) _ hI')
    (CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv eI hc)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs255r

end
