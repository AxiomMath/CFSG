module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4ExOrd
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4ExSp

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open CFSG CFSG.Blueprint

theorem k94Excl_mono {P Q : (K : Type) → [Group K] → Prop}
    (h : ∀ (K : Type) [Group K], P K → Q K) (hQ : K94Excl Q) : K94Excl P :=
  fun K _ _ hs hnab hgen htwo hPK z I₁ I₂ F₁ F₂ _ _ _ _ cfg =>
    hQ K hs hnab hgen htwo (h K hPK) z I₁ I₂ F₁ F₂ cfg

theorem k94_spor
    :
    K94Excl fun K _ =>
      NativeSporadic.IsSporadic K .M12 ∨ NativeSporadic.IsSporadic K .M22 ∨
        NativeSporadic.IsSporadic K .M23 ∨ NativeSporadic.IsSporadic K .J1 ∨
        NativeSporadic.IsSporadic K .J2 ∨ NativeSporadic.IsSporadic K .J3 ∨
        NativeSporadic.IsSporadic K .McL ∨ NativeSporadic.IsSporadic K .Ly :=
  k94Excl_mono
    (fun K _ h => by
      rcases h with h | h | h | h | h | h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h)))
    (k94Excl_or k94_spor_ord (k94Excl_or k94_j2 k94_mcl_ly))

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
