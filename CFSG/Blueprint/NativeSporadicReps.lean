module

public import CFSG.Blueprint.MonsterModels

public section

namespace CFSG.Blueprint.NativeSporadic

@[expose] def nativeCarrier : TauCeti.SporadicName → Type :=
  selectCarrier .gmat

noncomputable instance nativeCarrierGroup (s : TauCeti.SporadicName) : Group (nativeCarrier s) :=
  selectCarrierGroup .gmat s

@[expose] def NativeSporadicRep (G : Type) [Group G] : Prop :=
  ∃ s : TauCeti.SporadicName, Nonempty (G ≃* nativeCarrier s)

end CFSG.Blueprint.NativeSporadic
