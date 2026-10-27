module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.PlaneKill

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open

@[expose] def PlaneNoSig (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ Ê : Subgroup (MulAut S), IsElemAbelian p Ê → Nat.card Ê = p ^ 2 → NoSig p Ê

end CFSG.HardMathSupport.Dickson.I271
