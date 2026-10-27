module

public import CFSG.CGT.PushingUpLit.LIT.A4.Leaves
public import CFSG.CGT.PushingUpLit.LIT.A4.T211Transfer

public section

namespace CFSG.CGT.PushingUpLit.A4

theorem haradaTransfer211 : HaradaTransfer211 := by
  intro G _ _ hG M M₁ S A h₁ h2 hSM hS2 hSodd hAS hAn hAc hA4 hN hSyl
  exact T211.harada_transfer_211 hG h₁ h2 hSM hS2 hSodd hAS hAn hAc hA4 hN hSyl

end CFSG.CGT.PushingUpLit.A4
