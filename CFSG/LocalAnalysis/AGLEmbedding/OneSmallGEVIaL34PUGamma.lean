module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UPrimeExcL34

public section

namespace CFSG.AGLEmbedding

theorem card_glbCore_dvd_of_isLinThreeFour {K : Type} [Group K] [Finite K]
    (hK : IsLinThreeFour K) (T : Sylow 3 K) :
    Nat.card (CFSG.Open.GLBCore 3 1 (T : Subgroup K)) ∣ 72 := by
  have hD := KFactProofs.UPrimeExcL34.localData_of_isLinThreeFour hK T
  rw [← hD.card_normalizer]
  exact Subgroup.card_dvd_of_le hD.glbCore_le

end CFSG.AGLEmbedding
