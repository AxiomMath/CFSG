module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

@[expose] def PairClass.withGlobals (Q : PairClass) : PairClass :=
  fun H _ L K u => Q H L K u ∧ (∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2) ∧
    ∀ [Finite H] (N : Subgroup H) (t : H), SolomonHypQ H N L K t u → t ∈ N

@[expose] def TMemOfNotMax (S : List TauCeti.SporadicName)
    (Q : TauCeti.SporadicName → PairClass) : Prop :=
  ∀ s ∈ S, ∀ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H), OddCover s L →
    SolomonHypQ H N L K t u → Q s H L K u → ¬ (K ≤ N ∧ Maximal (K.subgroupOf N)) → t ∈ N

variable {H : Type} [Group H] [Finite H]

theorem hyp35At_withGlobals {S : List TauCeti.SporadicName}
    {Q : TauCeti.SporadicName → PairClass} (row : Stage3Row S Q) (lit : Sol78Lit)
    (hH : Balance.UHered H)
    (hyp31 : ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ∀ L : Subgroup H, SolStd L →
        (∃ s ∈ S, OddCover s L) → Hyp31Glob H N row.IsK (IsLS S) ∧ Hyp31FourA H N row.IsK)
    (h33 : Lemma33Two row.IsK (IsLS S) H) (htwo : TwoSylowStd S) (htmem : TMemOfNotMax S Q) :
    Hyp35At S (fun s => (Q s).withGlobals) H := by
  intro N hN hidx hkp L hSol hcov
  obtain ⟨s', L', K, t, u, hs', hcov', hglob, hQ, hnotmax⟩ :=
    stage3Pair row lit hH hyp31 h33 N hN hidx hkp L hSol hcov
  refine ⟨s', L', K, t, u, hs', hcov', hglob, hQ,
    htwo s' hs' H N L' hN hidx hkp hcov' hglob.standardL hglob.cyclicSylow, ?_⟩
  intro _ N' t' hhyp
  have hNN : N' = N := hhyp.fstar.generalizedFitting_eq.symm.trans hN.generalizedFitting_eq
  subst hNN
  exact htmem s' hs' H N' L' K t' u hcov' hhyp hQ hnotmax

end CFSG.EvenSporadicStandard.Induction
