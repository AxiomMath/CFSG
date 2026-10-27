module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndCfg

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.Blueprint CFSG.CGT.PushingUpLit.CGT6
open CFSG.Open (StatedClassicalModel)

@[expose] def End411' : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → ∀ f : ℕ, 2 ≤ f → YSL Y f → OuterT G T Y →
      (StatedClassicalModel (LayerQ G Y) .PSL 3 2 f ∨
        StatedClassicalModel (LayerQ G Y) .PSU 3 2 f) → False

@[expose] def End412' : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → YSL Y 3 → OuterT G T Y →
      ChevalleyExceptionalModel (LayerQ G Y) .G2 3 1 → False

@[expose] def End413' : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → ∀ f : ℕ, 2 ≤ f → YSL Y f → OuterT G T Y →
      StatedClassicalModel (LayerQ G Y) .PSL 2 2 (2 * f) → False

@[expose] def CaseOutcome' {V : Type} [CommGroup V] [Finite V] (G T Y : Subgroup (MulAut V)) :
    Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ YSL Y f ∧ OuterT G T Y ∧ (StatedClassicalModel (LayerQ G Y) .PSL 3 2 f ∨
    StatedClassicalModel (LayerQ G Y) .PSU 3 2 f)) ∨
  (∃ f : ℕ, 2 ≤ f ∧ YSL Y f ∧ OuterT G T Y ∧
    StatedClassicalModel (LayerQ G Y) .PSL 2 2 (2 * f)) ∨
  (YSL Y 3 ∧ OuterT G T Y ∧ ChevalleyExceptionalModel (LayerQ G Y) .G2 3 1) ∨
  (YSL Y 2 ∧ SmallList (LayerQ G Y)) ∨
  YSL5 Y ∨
  (∃ m : ℕ, 7 ≤ m ∧ Odd m ∧ YAlt Y m)

@[expose] def EndGMS' : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → CaseOutcome' G T Y

theorem endFour_of_cases' (hGMS : EndGMS') (h411 : End411') (h412 : End412') (h413 : End413')
    (h415 : End415)
    (hM12 : End4Small fun Q _ => NativeSporadic.IsSporadic Q .M12)
    (hJ1 : End4Small fun Q _ => NativeSporadic.IsSporadic Q .J1)
    (hJ2 : End4Small fun Q _ => NativeSporadic.IsSporadic Q .J2)
    (hA9 : End4Small fun Q _ => Nonempty (Q ≃* alternatingGroup (Fin 9)))
    (hA7 : End4Small fun Q _ => Nonempty (Q ≃* alternatingGroup (Fin 7)))
    (hL225 : End4Small fun Q _ => StatedClassicalModel Q .PSL 2 5 2)
    (hL35 : End4Small fun Q _ => StatedClassicalModel Q .PSL 3 5 1)
    (hU35 : End4Small fun Q _ => StatedClassicalModel Q .PSU 3 5 1) (hAlt : End4Alt) :
    EndFour := by
  intro V _ _ hV G T Y h
  rcases hGMS V hV G T Y h with ⟨f, hf, hY, hT, hQ⟩ | ⟨f, hf, hY, hT, hQ⟩ | ⟨hY, hT, hQ⟩ |
    ⟨hY, hQ⟩ | hY | ⟨m, hm, hodd, hY⟩
  · exact h411 V hV G T Y h f hf hY hT hQ
  · exact h413 V hV G T Y h f hf hY hT hQ
  · exact h412 V hV G T Y h hY hT hQ
  · rcases hQ with hQ | hQ | hQ | hQ | hQ | hQ | hQ | hQ
    · exact hM12 V hV G T Y h hY hQ
    · exact hJ1 V hV G T Y h hY hQ
    · exact hJ2 V hV G T Y h hY hQ
    · exact hA9 V hV G T Y h hY hQ
    · exact hA7 V hV G T Y h hY hQ
    · exact hL225 V hV G T Y h hY hQ
    · exact hL35 V hV G T Y h hY hQ
    · exact hU35 V hV G T Y h hY hQ
  · exact h415 V hV G T Y h hY
  · exact hAlt V hV G T Y h m hm hodd hY

end CFSG.CGT.PushingUpLit.CGT6K1
