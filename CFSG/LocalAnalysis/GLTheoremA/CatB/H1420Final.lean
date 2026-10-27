module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420RedMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LieBranch
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SporBranch
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420AltBranch

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

theorem i1420FactA_holds
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hD3 : ∀ q : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 q)
    (hD5 : ∀ q : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 5 q)
    (hAD : CFSG.LocalAnalysis.GLTheoremA.KDAltDown) {p z : ℕ} {s : TauCeti.SporadicName}
    (ht : I1420Target p z s) : I1420FactA p z s :=
  i1420FactA_of_branches i1420Red_holds (i1420Lie_holds hOrd hb hD3 hD5)
    (i1420Alt_holds hOrd hAD) (i1420Spor_holds hOrd hOut) ht

theorem i1420M3A_holds
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hD3 : ∀ q : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 q)
    (hD5 : ∀ q : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 5 q)
    (hAD : CFSG.LocalAnalysis.GLTheoremA.KDAltDown) : I1420M3A :=
  i1420FactA_holds hOrd hb hOut hD3 hD5 hAD (Or.inl ⟨rfl, rfl, rfl⟩)

theorem i1420M5A_holds
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hD3 : ∀ q : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 q)
    (hD5 : ∀ q : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 5 q)
    (hAD : CFSG.LocalAnalysis.GLTheoremA.KDAltDown) : I1420M5A :=
  i1420FactA_holds hOrd hb hOut hD3 hD5 hAD (Or.inr ⟨rfl, rfl, rfl⟩)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
