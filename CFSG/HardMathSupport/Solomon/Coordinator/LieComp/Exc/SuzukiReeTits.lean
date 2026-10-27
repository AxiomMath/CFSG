module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Ree
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Suzuki
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Tits

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Yardstones.Md42047359a2a

set_option linter.unusedSectionVars false

@[expose] def ReeG2Char3Export : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, lieFamily idx.1 = .suzukiReeTits →
      lieIndexChar idx.1 = 3 → Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → LieCompExport 3 β ∨ NoThreeComponents β


theorem isEmpty_cat_alt6_reeG2 (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) :
    IsEmpty ((TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group ≃* alternatingGroup (Fin 6)) := by
  have hm1 : 1 ≤ m := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  exact isEmpty_alt6_of_lieModel (t := .twistedG2) (p := 3) (f := 2 * m + 1)
    (Or.inr (Or.inr (Or.inl ⟨rfl, by decide,
      CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨MulEquiv.refl _⟩⟩⟩)))
    (by simp [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]; omega)

theorem lieCompOn_suzukiReeTits (hchar3 : ReeG2Char3Export) : LieCompOn .suzukiReeTits := by
  refine lieCompOn_of_exports fun S _ _ hs hna idx hF he β hβ => ?_
  classical
  by_cases hβ1 : β = 1
  · subst hβ1
    obtain ⟨e⟩ := he
    haveI := hs
    refine Or.inl (lieCompExport_one hna idx ⟨e⟩ ⟨fun f => ?_⟩)
    obtain ⟨d, hv⟩ := idx
    cases d with
    | reeG2 m => exact (isEmpty_cat_alt6_reeG2 m hv).false (e.symm.trans f)
    | _ =>
      exact (isEmpty_cat_alt6 ⟨_, hv⟩ (Or.inr ⟨hF, fun m h => by simp at h⟩)).false
        (e.symm.trans f)
  obtain ⟨d, hv⟩ := idx
  cases d with
  | suzuki m =>
    exact Or.inr (noThreeComponents_suzuki m hv he β)
  | tits =>
    haveI := hs
    exact Or.inr (noThreeComponents_tits hv hna he hβ hβ1)
  | reeF4 m =>
    exact Or.inl (lieCompExport_reeF4 m hv he hβ hβ1)
  | reeG2 m =>
    exact hchar3 S hs hna ⟨.reeG2 m, hv⟩ hF rfl he β hβ hβ1
  | _ => simp [lieFamily] at hF

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
