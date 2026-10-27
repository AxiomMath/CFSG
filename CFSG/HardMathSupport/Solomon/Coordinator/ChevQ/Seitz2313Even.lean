module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Two
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LieType.Seitz


@[expose] def Seitz2313Even : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → Seitz2313Cover.EvenScope d.1 →
    ∀ E : Subgroup (MulAut S), IsElemAbelian p E → E ≠ ⊥ →
      (∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U) →
        (⨆ (F : Subgroup (MulAut S)) (_ : F ≤ E ∧ F.relIndex E = p),
          CFSG.GH74.GLS.oPrimeResidualOf 2 (fixedPoints F)) = ⊤

theorem seitz2313Even_of_twoEven (h : Seitz2313TwoEven) : Seitz2313Even := by
  intro p hp hp2 S _ _ d he hs E hE hE0 hU
  obtain ⟨Q₁, Q₂, h1, h2, hi1, hi2, hgen⟩ := h p hp hp2 S d he hs E hE hU
  rw [eq_top_iff, ← hgen]
  exact sup_le
    (Seitz2313Aux.hyperplane_generation_of_invariant hp Nat.prime_two hp2 hE hE0 h1 hi1)
    (Seitz2313Aux.hyperplane_generation_of_invariant hp Nat.prime_two hp2 hE hE0 h2 hi2)

theorem seitz2313Even_holds : Seitz2313Even := seitz2313Even_of_twoEven seitz2313TwoEven_holds

theorem seitzHyperGamma_eq_top_of_seitz2313Even (h : Seitz2313Even) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) (hs : Seitz2313Cover.EvenScope d.1)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E) (hE0 : E ≠ ⊥)
    (hU : ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U) :
    seitzHyperGamma p E = ⊤ := by
  have h1 := h p hp hp2 S d he hs E hE hE0 hU
  rw [eq_top_iff, ← h1]
  refine iSup₂_le fun F hF => ?_
  exact le_trans (Subgroup.map_subtype_le _) (le_iSup₂_of_le F hF le_rfl)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
