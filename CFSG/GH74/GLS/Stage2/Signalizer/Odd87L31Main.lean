module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31CaseIT1
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31FWrap
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31CaseII
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31D
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87NCDProved

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Main

theorem leaf_lemma31Narrow_of
    (h29 : Lemma29First) (h29n : Lemma29NonSolv) (hInv : InvSec)
    (hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → L4TwoFieldStmt G z k S)
    (hSch : P34.GHSchreier) : Lemma31Narrow := by
  intro G _ _ z k S hctx H J R _ hJ hR hR1
  have hNCD : NonCentralDihedral := nonCentralDihedral_of_ctx hfld hSch
  have hT1 : NonCentralT1 := nonCentralT1_of_ctx hfld hSch
  have ha := l31_a_of_cases h29 hNCD hT1 hctx (fun hk => l31_a_central hctx hk) hJ hR hR1
  unfold Lemma31NarrowConcl
  exact ⟨ha, fun hd => l31_b_of_isDihedral h29n hctx hJ hR hd,
    fun hJK hne => l31_d hJ hR ha hJK hne, l31f_of_pcomp hInv hctx hJ hR hR1⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
