module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf5L173
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf4Six
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWQuot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWQuotCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Six

variable [PrintedQuotOdd] [PrintedQuotCent]

@[expose] def E18_6O2Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
      ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 ↥Q →
        Q ≤ Subgroup.center G ∧ ∀ J ∈ Ω, J ⊓ Q = ⊥

@[expose] def Lemma17_3Q8 : Prop :=
  TwinThmE.Lemma17_3Q8

theorem lemma17_3Q8 : Lemma17_3Q8 := by
  intro G _ _ Ω hΩ _ hq8 h2 hA _ hO hsolv hgen K hK htrans
  exact lemma17_3_twoGroup hΩ hq8 hA hO hsolv hgen h2 hK htrans

end Six

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
