module

public import CFSG.ClassicalInvolution.Q3.TL3T84
public import CFSG.ClassicalInvolution.Q3.TL3T51B

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}
  {K J : Subgroup G}

theorem CSetting.false_of_aeIdent_of_five_le
    (hS : CSetting 3 IH Ω K J) {n : ℕ} (hn : 5 ≤ n)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) : False :=
  hS.false_of_aeIdent_of_model117 hn (model117At_of_five_le hn) I

theorem cLeafAE_holds (IH : ℕ → Prop) : CLeafAE 3 IH := by
  intro G _ _ Ω K J hS n hn hI
  obtain ⟨I⟩ := hI
  exact hS.false_of_aeIdent_of_five_le hn I

end CFSG.ClassicalInvolution.Q3.TC.Thin
