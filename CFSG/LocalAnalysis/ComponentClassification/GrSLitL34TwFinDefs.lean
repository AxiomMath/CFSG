module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwRADefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four

@[expose] noncomputable def cosRA (r : Equiv.Perm (Fin 42)) : Fin 4 := by
  classical
  exact if r ∈ L34Facts.T0 then 0 else if g₅⁻¹ * r ∈ L34Facts.T0 then 1 else
    if g₆⁻¹ * r ∈ L34Facts.T0 then 2 else 3

@[expose] noncomputable def cc (x : WrE) : Fin 4 × Fin 4 × Bool := (cosRA x.a, cosRA x.b, x.e)

@[expose] def U1 : Set (Fin 4 × Fin 4 × Bool) :=
  {(0, 0, false), (3, 3, false), (0, 3, true), (3, 0, true)}

@[expose] def U2 : Set (Fin 4 × Fin 4 × Bool) :=
  {(0, 0, false), (3, 3, false), (1, 2, true), (2, 1, true)}

@[expose] def X1 : Subgroup WrE :=
  Subgroup.closure ((N0w : Set WrE) ∪ {⟨1, g₅ * g₆, true⟩})

@[expose] def X2 : Subgroup WrE :=
  Subgroup.closure ((N0w : Set WrE) ∪ {⟨g₅, g₆, true⟩})

end CFSG.ComponentClassification.GrSLit.L34Tw
