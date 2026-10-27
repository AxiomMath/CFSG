module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Glob
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.PredS

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup

theorem Sol78PredS.nil (H : Type) [Group H] [Finite H] : Sol78PredS [] H :=
  fun _ _ _ _ _ _ ⟨_, hs, _⟩ => absurd hs List.not_mem_nil

theorem Sol78PredS.union {S T : List TauCeti.SporadicName} {H : Type} [Group H] [Finite H]
    (hS : Sol78PredS S H) (hT : Sol78PredS T H) : Sol78PredS (S ++ T) H :=
  fun N hN hidx hkp L hL ⟨s, hs, hcov⟩ => by
    rcases List.mem_append.1 hs with h | h
    · exact hS N hN hidx hkp L hL ⟨s, h, hcov⟩
    · exact hT N hN hidx hkp L hL ⟨s, h, hcov⟩

@[expose] def Sol78Hyp35StepAmb (A Up S : List TauCeti.SporadicName)
    (Q : TauCeti.SporadicName → PairClass) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS A) H → Sol78PredS Up H →
    Hyp35At S Q H

@[expose] def Hyp31OfBelowAt (IsK : GroupClass) (S A Up : List TauCeti.SporadicName) : Prop :=
  Sol78Lit → Hyp31Row IsK (IsLS S) → ∀ (H : Type) [Group H] [Finite H],
    BelowSec (Sol78PredS A) H → Sol78PredS Up H → ∀ N : Subgroup H, FStarSimple N →
      N.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ∀ L : Subgroup H, SolStd L →
        (∃ s ∈ S, OddCover s L) → Hyp31Glob H N IsK (IsLS S) ∧ Hyp31FourA H N IsK

theorem Hyp31OfBelowAt.mono_ambient {IsK : GroupClass} {S A A' Up : List TauCeti.SporadicName}
    (hA : ∀ s ∈ A, s ∈ A') (h : Hyp31OfBelowAt IsK S A Up) : Hyp31OfBelowAt IsK S A' Up :=
  fun lit hrow H _ _ ih hup N hN hidx hkp L hL hcov =>
    h lit hrow H (BelowSec.mono_types hA ih) hup N hN hidx hkp L hL hcov

theorem sol78Hyp35StepAmb_of_stage3 {A Up S : List TauCeti.SporadicName}
    {Q : TauCeti.SporadicName → PairClass} (row : Stage3Row S Q) (lit : Sol78Lit)
    (h31 : Hyp31OfBelowAt row.IsK S A Up)
    (h33 : ∀ (H : Type) [Group H] [Finite H], Lemma33Two row.IsK (IsLS S) H) :
    Sol78Hyp35StepAmb A Up S Q := fun H _ _ ih hup =>
  hyp35At_of_stage3 row lit ih.uHered
    (fun N hN hidx hkp L hL hcov => h31 lit row.hyp31Row H ih hup N hN hidx hkp L hL hcov) (h33 H)

theorem sol78Hyp35StepAmb_withGlobals {A Up S : List TauCeti.SporadicName}
    {Q : TauCeti.SporadicName → PairClass} (row : Stage3Row S Q) (lit : Sol78Lit)
    (h31 : Hyp31OfBelowAt row.IsK S A Up)
    (h33 : ∀ (H : Type) [Group H] [Finite H], Lemma33Two row.IsK (IsLS S) H)
    (htwo : TwoSylowStd S) (htmem : TMemOfNotMax S Q) :
    Sol78Hyp35StepAmb A Up S (fun s => (Q s).withGlobals) := fun H _ _ ih hup =>
  hyp35At_withGlobals row lit ih.uHered
    (fun N hN hidx hkp L hL hcov => h31 lit row.hyp31Row H ih hup N hN hidx hkp L hL hcov) (h33 H)
    htwo htmem

theorem sol78PredS_row_at {A Up : List TauCeti.SporadicName} (r : RowSpec)
    (h35 : Sol78Hyp35StepAmb A Up r.types r.pairs) (hclose : Sol78ClosingHered r.types r.pairs)
    (H : Type) [Group H] [Finite H] (ih : BelowSec (Sol78PredS A) H)
    (hup : Sol78PredS Up H) : Sol78PredS r.types H := by
  intro N hN hidx hkp L hL hcov
  obtain ⟨s', L', K, t, u, hs', hcov', hglob, hQ⟩ := h35 H ih hup N hN hidx hkp L hL hcov
  exact (hclose H ih.uHered N L' K t u s' hs' hN hidx hkp hcov' hglob hQ).elim

structure DepRow where
  row : RowSpec
  up : List TauCeti.SporadicName

@[expose] def DepOrdered : List TauCeti.SporadicName → List DepRow → Prop
  | _, [] => True
  | Done, r :: rs => (∀ s ∈ r.up, s ∈ Done) ∧ DepOrdered (Done ++ r.row.types) rs

theorem sol78PredS_depRows {A : List TauCeti.SporadicName} {H : Type} [Group H] [Finite H]
    (ih : BelowSec (Sol78PredS A) H) :
    ∀ (rows : List DepRow) (Done : List TauCeti.SporadicName), Sol78PredS Done H →
      DepOrdered Done rows →
      (∀ r ∈ rows, Sol78Hyp35StepAmb A r.up r.row.types r.row.pairs ∧
        Sol78ClosingHered r.row.types r.row.pairs) →
      ∀ T : List TauCeti.SporadicName,
        (∀ s ∈ T, s ∈ Done ∨ ∃ r ∈ rows, s ∈ r.row.types) → Sol78PredS T H
  | [], Done, hDone, _, _, T, hT =>
    Sol78PredS.mono (fun s hs => by
      rcases hT s hs with h | ⟨r, hr, _⟩
      · exact h
      · exact absurd hr List.not_mem_nil) hDone
  | r :: rs, Done, hDone, hord, hrows, T, hT => by
    obtain ⟨hup, hord'⟩ := hord
    have hr := hrows r List.mem_cons_self
    have hrowH : Sol78PredS r.row.types H :=
      sol78PredS_row_at r.row hr.1 hr.2 H ih (Sol78PredS.mono hup hDone)
    exact sol78PredS_depRows ih rs (Done ++ r.row.types) (hDone.union hrowH) hord'
      (fun r' hr' => hrows r' (List.mem_cons_of_mem _ hr')) T (fun s hs => by
        rcases hT s hs with h | ⟨r', hr', hs'⟩
        · exact Or.inl (List.mem_append_left _ h)
        · rcases List.mem_cons.1 hr' with rfl | hr''
          · exact Or.inl (List.mem_append_right _ hs')
          · exact Or.inr ⟨r', hr'', hs'⟩)

theorem step_sol78Amb {A : List TauCeti.SporadicName} {rows : List DepRow}
    (hord : DepOrdered [] rows) (hcov : ∀ s ∈ A, ∃ r ∈ rows, s ∈ r.row.types)
    (hrows : ∀ r ∈ rows, Sol78Hyp35StepAmb A r.up r.row.types r.row.pairs ∧
      Sol78ClosingHered r.row.types r.row.pairs) : StepSec (Sol78PredS A) :=
  fun H _ _ ih =>
    sol78PredS_depRows ih rows [] (Sol78PredS.nil H) hord hrows A
      (fun s hs => Or.inr (hcov s hs))

theorem sol78PredS_of_depRows {A : List TauCeti.SporadicName} {rows : List DepRow}
    (hord : DepOrdered [] rows) (hcov : ∀ s ∈ A, ∃ r ∈ rows, s ∈ r.row.types)
    (hrows : ∀ r ∈ rows, Sol78Hyp35StepAmb A r.up r.row.types r.row.pairs ∧
      Sol78ClosingHered r.row.types r.row.pairs) (H : Type) [Group H] [Finite H]
    (hH : Balance.UHered H) : Sol78PredS A H :=
  holds_of_stepSec (step_sol78Amb hord hcov hrows) H hH

end CFSG.EvenSporadicStandard.Induction
