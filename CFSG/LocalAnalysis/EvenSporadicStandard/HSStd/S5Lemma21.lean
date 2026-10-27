module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveSym8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.CentralCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.HS

public section

namespace CFSG.EvenSporadicStandard.HSStd.Lemma21

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Induction
  CFSG.EvenSporadicStandard.HSStd

variable {H : Type} [Group H] [Finite H]

theorem seven_dvd_card_of_isSporadic_hs {Y : Type} [Group Y]
    (h : IsSporadic Y .HS) : 7 ∣ Nat.card Y := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* NativeSporadic.HS := e₀
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.HS.card_HS]
  norm_num

theorem card_le_two_of_no_involution {C M P : Subgroup H} [M.Normal] (hidx : M.index ≤ 2)
    (hP : IsPGroup 2 P) (hPC : P ≤ C) (hno : ∀ u ∈ C, u ∈ M → orderOf u = 2 → False) :
    Nat.card P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : P ⊓ M = ⊥ := by
    by_contra hne
    have hQp : IsPGroup 2 ↥(P ⊓ M) := hP.to_le inf_le_left
    rcases hQp.card_eq_or_dvd with h1 | h2
    · exact hne (Subgroup.eq_bot_of_card_eq _ h1)
    · obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
      have hu' : orderOf (u : H) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
      exact hno (u : H) (hPC (Subgroup.mem_inf.1 u.2).1) (Subgroup.mem_inf.1 u.2).2 hu'
  have hinj : Function.Injective ((QuotientGroup.mk' M).comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxM : (x : H) ∈ M := (QuotientGroup.eq_one_iff _).1 hx
    have : (x : H) ∈ P ⊓ M := Subgroup.mem_inf.2 ⟨x.2, hxM⟩
    rw [hQ, Subgroup.mem_bot] at this
    exact Subtype.ext this
  calc Nat.card P ≤ Nat.card (H ⧸ M) := Nat.card_le_card_of_injective _ hinj
    _ ≤ 2 := hidx

end CFSG.EvenSporadicStandard.HSStd.Lemma21

