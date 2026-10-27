module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J1
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22E8
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McL
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint.NativeSporadic

@[expose] def SporadicSettled (s : TauCeti.SporadicName) : Prop :=
  s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J1 ∨ s = .J2 ∨ s = .J3 ∨ s = .McL

theorem noNonsolvableClassical_carrier {s : TauCeti.SporadicName} (hs : SporadicSettled s) :
    NoNonsolvableClassical (Carrier s) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact noNonsolvableClassical_M12
  · exact noNonsolvableClassical_M22
  · exact noNonsolvableClassical_M23
  · exact noNonsolvableClassical_J1
  · exact noNonsolvableClassical_J2
  · exact noNonsolvableClassical_J3
  · exact noNonsolvableClassical_McL

theorem noNonsolvableClassical_of_isSporadic {G : Type} [Group G] {s : TauCeti.SporadicName}
    (hs : SporadicSettled s) (h : IsSporadic G s) : NoNonsolvableClassical G :=
  h.elim fun e => NoNonsolvableClassical.of_mulEquiv e (noNonsolvableClassical_carrier hs)

theorem noNonsolvableClassical_of_gh74_models {G : Type} [Group G]
    (hLy : NoNonsolvableClassical (Carrier .Ly))
    (h : IsSporadic G .M12 ∨ IsSporadic G .M22 ∨ IsSporadic G .M23 ∨ IsSporadic G .J1 ∨
      IsSporadic G .J2 ∨ IsSporadic G .J3 ∨ IsSporadic G .McL ∨ IsSporadic G .Ly) :
    NoNonsolvableClassical G := by
  rcases h with h | h | h | h | h | h | h | h
  · exact noNonsolvableClassical_of_isSporadic (Or.inl rfl) h
  · exact noNonsolvableClassical_of_isSporadic (Or.inr (Or.inl rfl)) h
  · exact noNonsolvableClassical_of_isSporadic (Or.inr (Or.inr (Or.inl rfl))) h
  · exact noNonsolvableClassical_of_isSporadic (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h
  · exact noNonsolvableClassical_of_isSporadic
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h
  · exact noNonsolvableClassical_of_isSporadic
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) h
  · exact noNonsolvableClassical_of_isSporadic
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) h
  · exact h.elim fun e => NoNonsolvableClassical.of_mulEquiv e hLy

end CFSG.ClassicalInvolution
