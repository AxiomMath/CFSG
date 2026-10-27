module

public import CFSG.Foundations.Basic

public section

namespace CFSG

theorem pCore_le_solvableRadical (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Finite G] :
    pCore p G ≤ solvableRadical G :=
  haveI := (pCore_isPGroup (p := p) (G := G)).isNilpotent
  le_sSup ⟨pCore_normal, inferInstance⟩

end CFSG
