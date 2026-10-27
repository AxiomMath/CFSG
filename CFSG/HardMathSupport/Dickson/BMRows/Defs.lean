module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def PCompCensus (p : ℕ) (Q : Type) [Group Q] (P : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ x : Q, orderOf x = p → ∀ J : Subgroup Q,
    GLAPComponent p (Subgroup.centralizer ({x} : Set Q)) J → catalogIs (PSimple p J) P

end CFSG.HardMathSupport.Dickson.BMRows
