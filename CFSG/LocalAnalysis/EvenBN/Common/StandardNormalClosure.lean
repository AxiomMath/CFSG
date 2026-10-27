module

public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.GroupTheory.PCore.Defs
import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup CFSG.Open
open scoped commutatorElement

variable {H : Type*} [Group H]

instance standardComponentOddCore_normal (H : Type*) [Group H] :
    (standardComponentOddCore H).Normal :=
  sSup_normal _ fun _ hN => hN.1

theorem standardComponentOddCore_eq_oddCore (H : Type*) [Group H] :
    standardComponentOddCore H = CFSG.oddCore H := by
  unfold standardComponentOddCore CFSG.oddCore
  rfl

theorem odd_card_standardComponentOddCore (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (standardComponentOddCore H)) := by
  rw [standardComponentOddCore_eq_oddCore]
  exact CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd

end CFSG.LocalAnalysis.EvenBN.Common
