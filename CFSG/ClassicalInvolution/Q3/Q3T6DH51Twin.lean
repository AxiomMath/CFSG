module

public import CFSG.ClassicalInvolution.Q3.Q3T6DH51Layer
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51D4B

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77

section Twin


theorem d4InnerAlphaThree_proved : D4InnerAlphaThree :=
  fun H _ _ L ψ hψ hker A h2 hinn hcl =>
    alphaOf_eq_bot_of_inner_one_classical H L ψ hψ hker A h2 hinn hcl

theorem hyp51At_of_twin_layer3_proved {G : Type} [Group G] [Finite G] [FrameSimple G]
    {Ω : Set (Subgroup G)} {c b d : G} {K K' B : Subgroup G} (hΩ : InClass3 Ω)
    (hBelow : CIT3Below (Nat.card G)) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hbK : IsClassicalMember3 K b) (hbK' : IsClassicalMember3 K' b)
    (hbU : IsUniqueInvolution K b) (hbU' : IsUniqueInvolution K' b)
    (hMK : K ∈ tqMembers3 Ω c) (hMK' : K' ∈ tqMembers3 Ω c)
    (hB : CFSG.Open.IsElemAbelian 2 B) (hbB : b ∈ B) (hdB : d ∈ B) (hcB : c ∈ B)
    (hBgen : B = Subgroup.closure ({b, d, c} : Set G)) (hc1 : c ≠ 1) (hbc : b ≠ c)
    (hd1 : d ≠ 1) (hdb : d ≠ b) (hdsup : d ∈ exactCore3 c K ⊔ exactCore3 c K') :
    Asc77.Hyp51At B c :=
  hyp51At_of_twin_layer3 d4InnerAlphaThree_proved hΩ hBelow hnab hbK hbK' hbU hbU' hMK hMK' hB
    hbB hdB hcB hBgen hc1 hbc hd1 hdb hdsup

end Twin

end CFSG.ClassicalInvolution.Q3.Q3T6D
