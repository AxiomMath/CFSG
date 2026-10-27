module

public import CFSG.GH74.Generic.S1.Exo.NbIvk
public import CFSG.GH74.Generic.S1.Exo.Q3H
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Proved

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.GLS

@[expose] def NbhdNoCommon : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (q : ℕ) (w y : H) (J₂ J₄ : Subgroup H),
    NbhdHyp H q w y J₂ J₄ → NoCommonComponent J₂ J₄

theorem nbhdNoPrime_of_noCommon
    (h : NbhdNoCommon) : NbhdNoPrime :=
  fun H _ _ q w y J₂ J₄ hN _ hr hr2 hrq =>
    hN.no_prime (h H q w y J₂ J₄ hN) (IVK.Proofs2.ivk_9_5At_gh_all_proved q hN.five) hr hr2 hrq

theorem s1FrameExists_of_noCommon_q3H
    (hExact : S1LiftExactProp) (h : NbhdNoCommon) (hq3 : Q3H) : S1FrameExists :=
  s1FrameExists_of_nbhd_q3H hExact (nbhdNoPrime_of_noCommon h) hq3

end CFSG.GH74.Generic.S1.Exo
