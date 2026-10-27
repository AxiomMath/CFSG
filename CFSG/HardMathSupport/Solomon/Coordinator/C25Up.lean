module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def IsCatalogLieIso (Q : Type*) [Group Q] (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, P d.1 ∧ Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsL364Index : TauCeti.LieTypeIndex → Prop
  | .A r q => r = 2 ∧ q.p = 2 ∧ q.exponent = 6
  | _ => False

@[expose] def Is3D44Index : TauCeti.LieTypeIndex → Prop
  | .trialityD4 q => q.p = 2 ∧ q.exponent = 2
  | _ => False

@[expose] def IsD44Index : TauCeti.LieTypeIndex → Prop
  | .D r q => r = 4 ∧ q.p = 2 ∧ q.exponent = 2
  | _ => False

end CFSG.HardMathSupport.Solomon.Coordinator
