module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Glob

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H] {N : Subgroup H}

theorem fi_caseA (row : Stage3Row [.Fi22] (fun _ => fiLoc 18393661440))
    (h31 : FiHyp31 row.IsK [.Fi22] fiTypes [.Fi23, .Fi24Prime]) (hTwo : TwoSylowStd [.Fi22])
    (hT : TMemOfNotMax [.Fi22] (fun _ => fiLoc 18393661440))
    (h33 : Lemma33Two row.IsK (IsLS [.Fi22]) H) (lit : Sol78Lit)
    (ih : BelowSec (Sol78PredS fiTypes) H) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hN22 : ¬ IsSporadic ↥N .Fi22)
    (hN23 : ¬ IsSporadic ↥N .Fi23) (hN24 : ¬ IsSporadic ↥N .Fi24Prime)
    (hnb : NoBiggerFi H .Fi22) (hup : FiNoUp [.Fi23, .Fi24Prime] H) {L₀ : Subgroup H}
    (hL₀ : SolStd L₀) (hcov : OddCover .Fi22 L₀) :
    ∃ L' : Subgroup H, OddCover .Fi22 L' ∧ FiOut H N L' .Fi22 := by
  obtain ⟨s', L', K, t, u, hs', hcov', hglob, hloc, -, hmem⟩ :=
    hyp35At_withGlobals row lit ih.uHered
      (fun N' hN' hidx' hkp' L'' hL'' hc'' => by
        have hNN : N' = N := hN'.generalizedFitting_eq.symm.trans hN.generalizedFitting_eq
        subst hNN
        exact h31 lit row.hyp31Row H ih N' hN' hidx' hkp' hup hN22 hN23 hN24 L'' hL'' hc'')
      h33 hTwo hT N hN hidx hkp L₀ hL₀
      ⟨.Fi22, List.mem_singleton_self _, hcov⟩
  have hs : s' = .Fi22 := List.mem_singleton.1 hs'
  subst hs
  exact ⟨L', hcov', Or.inl ⟨K, t, u, hglob, fiInBase_iff.2 ⟨hloc, hnb⟩, hmem⟩⟩

theorem fi_caseB (row : Stage3Row [.Fi23] (fun _ => fiLoc (2 * 64561751654400)))
    (h31 : FiHyp31 row.IsK [.Fi23] fiTypes [.Fi24Prime]) (h33 : Lemma33Two row.IsK (IsLS [.Fi23]) H)
    (lit : Sol78Lit)
    (ih : BelowSec (Sol78PredS fiTypes) H) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hN22 : ¬ IsSporadic ↥N .Fi22)
    (hN23 : ¬ IsSporadic ↥N .Fi23) (hN24 : ¬ IsSporadic ↥N .Fi24Prime)
    (hnb : NoBiggerFi H .Fi23) (hup : FiNoUp [.Fi24Prime] H) {L₀ : Subgroup H}
    (hL₀ : SolStd L₀) (hcov : OddCover .Fi23 L₀) :
    ∃ L' : Subgroup H, OddCover .Fi23 L' ∧ FiOut H N L' .Fi23 := by
  obtain ⟨s', L', K, t, u, hs', hcov', hglob, hloc, -⟩ :=
    stage3Pair row lit ih.uHered
      (fun N' hN' hidx' hkp' L'' hL'' hc'' => by
        have hNN : N' = N := hN'.generalizedFitting_eq.symm.trans hN.generalizedFitting_eq
        subst hNN
        exact h31 lit row.hyp31Row H ih N' hN' hidx' hkp' hup hN22 hN23 hN24 L'' hL'' hc'')
      h33 N hN hidx hkp L₀ hL₀
      ⟨.Fi23, List.mem_singleton_self _, hcov⟩
  have hs : s' = .Fi23 := List.mem_singleton.1 hs'
  subst hs
  exact ⟨L', hcov', Or.inl ⟨K, t, u, hglob, fiInBase_iff.2 ⟨hloc, hnb⟩⟩⟩

theorem fi_caseC1 (ho : FiOrders)
    (row : Stage3Row [.Fi24Prime] (fun _ => fiLoc (2 * 64561751654400)))
    (h31 : FiHyp31 row.IsK [.Fi24Prime] fiTypes [.Fi23])
    (h33 : Lemma33Two row.IsK (IsLS [.Fi24Prime]) H) (lit : Sol78Lit)
    (ih : BelowSec (Sol78PredS fiTypes) H) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hN22 : ¬ IsSporadic ↥N .Fi22)
    (hN23 : ¬ IsSporadic ↥N .Fi23) (hN24 : ¬ IsSporadic ↥N .Fi24Prime)
    (hup : FiNoUp [.Fi23] H) {L₀ : Subgroup H} (hL₀ : SolStd L₀) (hcov : OddCover .Fi24Prime L₀) :
    ∃ L' : Subgroup H, OddCover .Fi24Prime L' ∧ FiOut H N L' .Fi24Prime := by
  obtain ⟨s', L', K, t, u, hs', hcov', hglob, hloc, -⟩ :=
    stage3Pair row lit ih.uHered
      (fun N' hN' hidx' hkp' L'' hL'' hc'' => by
        have hNN : N' = N := hN'.generalizedFitting_eq.symm.trans hN.generalizedFitting_eq
        subst hNN
        exact h31 lit row.hyp31Row H ih N' hN' hidx' hkp' hup hN22 hN23 hN24 L'' hL'' hc'')
      h33 N hN hidx hkp L₀ hL₀
      ⟨.Fi24Prime, List.mem_singleton_self _, hcov⟩
  have hs : s' = .Fi24Prime := List.mem_singleton.1 hs'
  subst hs
  exact ⟨L', hcov', Or.inl ⟨K, t, u, hglob,
    Or.inl (fiInBase_iff.2 ⟨hloc, noBiggerFi_fi24Prime_of_orders ho H⟩)⟩⟩

end CFSG.EvenSporadicStandard.Induction.Fi
