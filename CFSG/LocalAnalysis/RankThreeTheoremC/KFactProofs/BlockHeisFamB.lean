module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamBCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisCenter
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.AGLEmbedding
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem heisB_model {X : Type} [Group X] (d : TauCeti.ValidLieTypeIndex) (hd : IdxB d.1)
    (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ r f : ℕ, StatedClassicalModel X .PSp r 2 f := by
  obtain ⟨d, hv⟩ := d
  cases d
  case B r q =>
    have hq2 : q.p = 2 := hd
    have hr : 2 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
    refine ⟨r, q.exponent, ?_⟩
    by_cases h2 : r = 2
    · subst h2
      have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rwa [hq2] at hm
    · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2
        (by omega) e
      rwa [hq2] at hm
  all_goals exact hd.elim

theorem heisCoreOn_idxB_of_oddCenterRest (hZ : OddCenterRest) : HeisCoreOn IdxB := by
  intro L _ _ hperf hodd hrk hsimple d hd e p hp hp5
  left
  haveI := hperf
  haveI := hsimple
  have hq : CFSG.Open.IsQuasisimple L := ⟨hperf.commutator_eq_top, hsimple⟩
  have hZp : ¬ p ∣ Nat.card (Subgroup.center L) :=
    heis_not_dvd_center_rest hZ hq hodd (Or.inl ⟨d, hd, ⟨e⟩⟩) hp hp5
  obtain ⟨r, f, hcl⟩ := heisB_model d hd e
  exact heisB_noHeisAut_of_model hp hp5 (heis_conj_injective L)
    (fun A hA hAp => heis_rank_quotient hrk hp (by omega) hZp A hA hAp) hcl

theorem heisCoreOn_idxB
    (hGA : CFSG.Open.GriessAllModelsStatement) : HeisCoreOn IdxB :=
  heisCoreOn_idxB_of_oddCenterRest (oddCenterRest_of_griess hGA)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
