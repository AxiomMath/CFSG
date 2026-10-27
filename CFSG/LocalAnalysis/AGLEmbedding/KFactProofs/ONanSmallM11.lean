module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFam
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallIdent
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallThreeOrders
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Bridge.M11
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCore

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Blueprint

theorem nonempty_equiv_m11 {K : Type} [Group K]
    (hK : IsSporadicGroup .M11 K) : Nonempty (K ≃* NativeSporadic.M11) := by
  obtain ⟨e⟩ := hK
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  exact ⟨e.trans β.symm⟩

theorem card_of_isM11 {K : Type}
    [Group K] (hK : IsSporadicGroup .M11 K) : Nat.card K = 7920 := by
  obtain ⟨e⟩ := nonempty_equiv_m11 hK
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M11

theorem sylowSq_of_isLinThreeFour {K : Type} [Group K] [Finite K] (hK : IsLinThreeFour K) :
    SylowSq 3 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro T
  have h := card_of_isLinThreeFour hK
  exact card_sylow_eq_pow_of_card_eq (k := 2) (m := 2240) (by rw [h]; norm_num) (by norm_num) T

theorem sylowSq_of_isM11 {K : Type}
    [Group K] [Finite K] (hK : IsSporadicGroup .M11 K) : SylowSq 3 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro T
  have h := card_of_isM11 hK
  exact card_sylow_eq_pow_of_card_eq (k := 2) (m := 880) (by rw [h]; norm_num) (by norm_num) T

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
