module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Emb
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYHsSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Model

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native
  CFSG.EvenSporadicStandard.HSStd.FiveY

theorem not_seven_dvd_centralizer_of_hs
    (hM : HS100Model) {Γ : Type}
    [Group Γ] [Finite Γ] (N : Subgroup Γ) [N.Normal] (hC : centralizer (N : Set Γ) = ⊥)
    (hN : IsSporadic ↥N .HS) {y : Γ} (hy : orderOf y = 3) :
    ¬ 7 ∣ Nat.card ↥(centralizer ({y} : Set Γ)) := by
  obtain ⟨ε⟩ := hM.equiv N hN
  obtain ⟨e, -⟩ := hM.aut
  let ρ : Γ →* ↥hs100R := e.symm.toMonoidHom.comp (conjEmb N ε)
  have hρ : Function.Injective ρ := e.symm.injective.comp (conjEmb_injective N ε hC)
  have hy' : orderOf (ρ y) = 3 := by rw [orderOf_injective ρ hρ, hy]
  intro h7
  have h := h7.trans (card_centralizer_dvd ρ hρ y)
  rw [card_centralizer_hs100R_three hy'] at h
  omega

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
