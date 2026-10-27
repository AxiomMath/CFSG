module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRk
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkL3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkU3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkG2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkD4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkRee
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOutL4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOutLU4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOutS2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L5
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55U5
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTExcl

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem false_of_killed (hInv : InvSec) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hF : FL3 (↥J ⧸ center ↥J) ∨ FU3 (↥J ⧸ center ↥J) ∨ FG2 (↥J ⧸ center ↥J) ∨
      FD4 (↥J ⧸ center ↥J) ∨ FRee (↥J ⧸ center ↥J) ∨ FL5 (↥J ⧸ center ↥J) ∨
      FU5 (↥J ⧸ center ↥J) ∨ FMcLy (↥J ⧸ center ↥J)) : False := by
  have hk := hd.u.kind
  have hI := invSecGroup_of_component hInv h.ctx H hJ
  rcases hF with hF | hF | hF | hF | hF | hF | hF | hF
  · exact false_of_rankCellK hInv (rankCell_fl3 k hk) h hd J hJ hF
  · exact false_of_rankCellK hInv (rankCell_fu3 k hk) h hd J hJ hF
  · exact false_of_rankCellK hInv (rankCell_fg2 k hk) h hd J hJ hF
  · exact false_of_rankCellK hInv (rankCell_fd4 k hk) h hd J hJ hF
  · exact false_of_rankCellK hInv (rankCell_free k hk) h hd J hJ hF
  · exact excl55_fl5 k _ hF hI
  · exact excl55_fu5 k _ hF hI
  · exact excl_mcly hk hF hI

theorem outTwoNilp_of_component (hInv : InvSec) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) (J : Subgroup (HBar H)) (hJ : IsComponent J) :
    OutTwoNilp (↥J ⧸ center ↥J) := by
  have hs : IsSimpleGroup (↥J ⧸ center ↥J) := hJ.1.2.1
  have hgh : GHList (↥J ⧸ center ↥J) := ghList_of_quotient_component h.ctx.std.kgh (H_ne_top h)
    (QuotientGroup.mk' (pPrimeCore 2 ↥H)) (QuotientGroup.mk'_surjective _) hJ.1
  have hk := false_of_killed hInv h hd hJ
  rcases ghList_cases hgh with hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF |
    hF | hF
  · exact outCell_alt _ hs hF
  · exact outCell_spor _ hs hF
  · exact (hk (by simp only [hF, or_true])).elim
  · exact outCell_two _ hs hF
  · exact outCell_fl2 _ hs hF
  · exact (hk (by simp only [hF, true_or])).elim
  · exact (hk (by simp only [hF, true_or, or_true])).elim
  · exact outCell_fsp4 _ hs hF
  · exact (hk (by simp only [hF, true_or, or_true])).elim
  · exact (hk (by simp only [hF, true_or, or_true])).elim
  · exact outCell_fl4 _ hs hF
  · exact outCell_fu4 _ hs hF
  · exact (hk (by simp only [hF, true_or, or_true])).elim
  · exact (hk (by simp only [hF, true_or, or_true])).elim
  · exact (hk (by simp only [hF, true_or, or_true])).elim

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
