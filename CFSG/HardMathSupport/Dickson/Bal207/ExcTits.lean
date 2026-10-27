module

public import CFSG.HardMathSupport.Dickson.Bal207.ExcVac
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTTits

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

theorem excTits_index {d : TauCeti.ValidLieTypeIndex} (hd : IsExcTits d.1) :
    ∃ hv : TauCeti.LieTypeIndex.tits.Valid, d = ⟨.tits, hv⟩ := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | tits => exact ⟨hv, rfl⟩
  | _ => exact absurd hd (by simp [IsExcTits])

section TitsFam

set_option linter.unusedSectionVars false


theorem excTits_clauses {G : ∀ (S : Type) [Group S], MulAut S → Prop} {X : Type} [Group X]
    [Finite X] {p : ℕ} {K B A : Subgroup X} (ctx : Bal207PlusCtx G p K B A)
    (hq : IsLieQuot ↥K IsExcTits) : Bal207PlusFamClauses p K B A := by
  obtain ⟨d, hd, ⟨f⟩⟩ := hq
  obtain ⟨hv, rfl⟩ := excTits_index hd
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := ctx.comp.2.2.2
  have hnc := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
    ctx.comp.2.2
  refine bal207PlusFamClauses_of_fix_solvable ctx fun β hβ hβ1 => ?_
  exact isSolvable_fixSubgroup_tits hv hnc ⟨f⟩ ctx.prime ctx.odd hβ hβ1

theorem bal207PlusFamTitsThree (G : ∀ (S : Type) [Group S], MulAut S → Prop) :
    Bal207PlusFamTitsThree G := by
  intro X _ _ _ p K B A ctx hq _
  obtain ⟨d, ⟨-, hd⟩, e⟩ := hq
  exact excTits_clauses ctx ⟨d, hd, e⟩

theorem bal207PlusFamTitsFive (G : ∀ (S : Type) [Group S], MulAut S → Prop) :
    Bal207PlusFamTitsFive G := by
  intro X _ _ _ p K B A ctx hq _
  obtain ⟨d, ⟨-, hd⟩, e⟩ := hq
  exact excTits_clauses ctx ⟨d, hd, e⟩

end TitsFam

end CFSG.HardMathSupport.Dickson.Bal207

end
