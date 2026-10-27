module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthAssembly

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

theorem lieCompOn_symplecticOrthogonal
    (hb : LieOrderBridge) (hQ : YS08.LieQ.LieQConstrainedInner 3)
    (hD4 : D4OuterExport) : LieCompOn .symplecticOrthogonal := by
  apply lieCompOn_of_exports
  intro S _ _ hs hna idx hF he β hβ
  obtain ⟨d, hv⟩ := idx
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | B r q =>
    by_cases hsp : q.p = 2 ∨ r = 2
    · exact lieCompCase_symplectic hb hQ hs hna ⟨_, hv⟩ (Or.inl ⟨r, q, rfl, hsp⟩) he β hβ
    · push_neg at hsp
      exact lieCompCase_orthogonal hb hQ hD4 hs hna ⟨_, hv⟩
        (Or.inl ⟨r, q, rfl, hsp.1, by simp only at hr; omega⟩) he β hβ
  | C r q => exact lieCompCase_symplectic hb hQ hs hna ⟨_, hv⟩ (Or.inr ⟨r, q, rfl⟩) he β hβ
  | D r q =>
    exact lieCompCase_orthogonal hb hQ hD4 hs hna ⟨_, hv⟩ (Or.inr (Or.inl ⟨r, q, rfl⟩)) he β hβ
  | twistedD r q =>
    exact lieCompCase_orthogonal hb hQ hD4 hs hna ⟨_, hv⟩ (Or.inr (Or.inr ⟨r, q, rfl⟩)) he β hβ
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
