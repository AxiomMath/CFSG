module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigDefs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrA1Model

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W

section Cert



variable {r n : ℕ}

theorem tightLinkZ2L2BigR_of_props (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n) (hA : Z2BigAdapted r n)
    (hC : Z2BigC264One r n) (h7a : Z2BigProp7a r n) (h6a : Z2BigProp6a4 r n) :
    TightLinkZ2L2BigR r n := by
  intro Y _ _ R S t hL hc hT hbad hZ2 hsimp hidx hmodel
  obtain ⟨J, hJ, u, hu, -⟩ := id hbad
  obtain ⟨R₀, T₀, hR₀, hR₀u, hT₀, hT₀N, P, hR₀P, hT₀P⟩ := hA Y R S t hL J hJ u hu
  have h4' : Thm4RBelow r n := h4 hL.below hL.tbelow
  have hall : NoA1All R t J u := fun R₁ T₁ h1 h2 h3 h4'' ⟨w, hw2, hwt, hwu, hwE, hR₁w, hT₁w⟩ =>
    RonanRes.false_of_caseA1_of_linkZ2L2 hr hNo h4' hL hc hbad hZ2 hsimp hmodel hJ hu h1 h2 h3 h4''
      hw2 hwt hwu hwE hR₁w hT₁w
  have hs : Z2SetR r n R S t J u R₀ T₀ P :=
    ⟨hL, hc, hT, hZ2, hsimp, hidx, hmodel, hJ, hu, hR₀, hR₀u, hT₀, hT₀N,
      hall R₀ T₀ hR₀ hR₀u hT₀ hT₀N, hR₀P, hT₀P⟩
  have hC' := hC hr hNo h4' Y R S t J u R₀ T₀ P hs
  by_cases hinv : InvOutsideA (P : Subgroup Y) t u
  · exact h7a hr Y R S t J u R₀ T₀ P hs hC' hinv
  · exact h6a hr Y R S t J u R₀ T₀ P hs hC' hall hinv

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
