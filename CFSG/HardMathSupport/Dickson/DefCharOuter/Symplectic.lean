module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.SymplecticAux.Outer
import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator

theorem perfectInLayer_C_outer (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.C r q).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.C r q, hv⟩)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = q.p)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β := by
  have hr : 3 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
  exact SymplecticAux.perfectInLayer_of_lieModel_psp (by omega)
    (CFSG.Models.lieModel_C r q hv e) hp hp2 hβ hout

theorem perfectInLayer_B_two_outer (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = q.p)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β := by
  rcases CFSG.Models.lieModel_B 2 q hv e with h | h
  · exact SymplecticAux.perfectInLayer_of_lieModel_psp le_rfl h hp hp2 hβ hout
  ·
    exact absurd h.1.2.2.1 (by norm_num)

end CFSG.HardMathSupport.Dickson.DefCharOuter
