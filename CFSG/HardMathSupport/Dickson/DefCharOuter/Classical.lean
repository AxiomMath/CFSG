module

public import CFSG.Yardstones.Md42047359a2a.Definitions
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Linear
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Unitary
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Symplectic
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Orthogonal
public import CFSG.HardMathSupport.Dickson.DefCharOuter.D4Three

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator



theorem lieDefCharOuter_classical (h1 : D4ThreeGraphOuter) (idx : TauCeti.ValidLieTypeIndex)
    (hfam : CFSG.Yardstones.Md42047359a2a.lieFamily idx.1 =
        CFSG.Yardstones.Md42047359a2a.LieFamily.linearUnitary ∨
      CFSG.Yardstones.Md42047359a2a.lieFamily idx.1 =
        CFSG.Yardstones.Md42047359a2a.LieFamily.symplecticOrthogonal)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = idx.1.characteristic)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β ∨ CFSG.Open.GLAPPrimeCoreOf p (fixSubgroup β) = ⊥ := by
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  cases d with
  | A r q =>
    exact .inl (perfectInLayer_A_outer r q hv hnc e hp hp2
      (hpc.trans (TauCeti.LieTypeIndex.characteristic_A r q)) hβ hout)
  | twistedA r q =>
    exact .inl (perfectInLayer_twistedA_outer r q hv hnc e hp hp2
      (hpc.trans (TauCeti.LieTypeIndex.characteristic_twistedA r q)) hβ hout)
  | B r q =>
    have hpq := hpc.trans (TauCeti.LieTypeIndex.characteristic_B r q)
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact .inl (perfectInLayer_B_two_outer q hv hnc e hp hp2 hpq hβ hout)
    · exact .inl (perfectInLayer_B_outer r q hv hnc e hp hp2 hpq hr3 hβ hout)
  | C r q =>
    exact .inl (perfectInLayer_C_outer r q hv hnc e hp hp2
      (hpc.trans (TauCeti.LieTypeIndex.characteristic_C r q)) hβ hout)
  | D r q =>
    have hpq := hpc.trans (TauCeti.LieTypeIndex.characteristic_D r q)
    by_cases h43 : r = 4 ∧ p = 3
    · obtain ⟨rfl, h3⟩ := h43
      exact lieDefCharOuter_D4_three h1 q hv hnc e hp hp2 hpq h3 hβ hout
    · exact .inl (perfectInLayer_D_outer r q hv hnc e hp hp2 hpq
        (fun h4 h3 => h43 ⟨h4, h3⟩) hβ hout)
  | twistedD r q =>
    exact .inl (perfectInLayer_twistedD_outer r q hv hnc e hp hp2
      (hpc.trans (TauCeti.LieTypeIndex.characteristic_twistedD r q)) hβ hout)
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hfam

end CFSG.HardMathSupport.Dickson.DefCharOuter
