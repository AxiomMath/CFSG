module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Even
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Step
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

structure UpFacts (Up : List TauCeti.SporadicName) : Prop where
  fi23 : ∀ s ∈ Up, Fi23Excl s
  not_exc : ∀ s ∈ Up, SporadicNotExc s
  odd : ∀ s ∈ Up, ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    IsSporadic (X ⧸ center X) s → Odd (Nat.card (center X))
  rank : ∀ s ∈ Up, ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    IsSporadic (X ⧸ center X) s → 3 ≤ CFSG.pRank 2 X

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} {Up : List TauCeti.SporadicName}

theorem noUp_of_hUp (junction : JunctionStmtAt H) (thm22 : Sol78Thm22At H)
    (ihUp : BelowSec (Sol78PredS Up) H) (hUpH : Sol78PredS Up H) (uf : UpFacts Up)
    (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) : NoUp Up H := by
  intro Q hQ s'' hs'' hsp
  have hQq : CFSG.IsQuasisimple ↥Q := hQ.isQuasisimple
  have hmax : Maximal Q :=
    maximal_of_central_type junction ihUp noUp_nil hN hidx hkp hQ hs''
      hsp (uf.fi23 s'' hs'') (evenCoverExcl_of_odd (uf.odd s'' hs'')) (uf.not_exc s'' hs'')
  have hstd : StdBare Q :=
    stdBare_of_maximal thm22 hkp hN hidx hmax (uf.rank s'' hs'' _ hQq hsp)
  have hsol : SolStd Q := solStd_of_inL_of_stdBare hQ hstd
  have hcov : OddCover s'' Q := ⟨hQq, uf.odd s'' hs'' _ hQq hsp, hsp⟩
  obtain ⟨hF23, -⟩ := hUpH N hN hidx hkp Q hsol ⟨s'', hs'', hcov⟩
  exact uf.fi23 s'' hs'' ↥Q hF23 hsp

end CFSG.EvenSporadicStandard.Induction.Hyp
