module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269SFin
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TD42

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def I269Residual3 : Prop :=
  ∀ (S : Type) [Group S], catalogIs S (fun i => S9.isD4two i ∨ S9.isU3eight i) → E9Solv S

section Certs


theorem i269At_of_residual3 (h : I269Residual3) (G : Type) [Group G] [Finite G] : I269At G :=
  i269At_of_residual2 h e9Solv_td4two G

end Certs

end CFSG.LocalAnalysis.GLTheoremA
