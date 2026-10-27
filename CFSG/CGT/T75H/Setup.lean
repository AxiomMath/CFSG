module

public import CFSG.CGT.Timmesfeld75.Sec6Ctx

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem card_normIn_eq_two [Finite G] {T T₁ : Subgroup G} (hP : MaxPair T T₁) (hS : Sec3 T T₁)
    (h4 : Nat.card T = 4) : Nat.card (normIn T T₁) = 2 := by
  have hlt : normIn T T₁ < T := hS.cfg.normIn_lt hP.conj
  have hdvd : Nat.card (normIn T T₁) ∣ 4 := h4 ▸ Subgroup.card_dvd_of_le (normIn_le T T₁)
  have hne1 : Nat.card (normIn T T₁) ≠ 1 := fun h => hP.nontriv (Subgroup.card_eq_one.1 h)
  have hne4 : Nat.card (normIn T T₁) ≠ 4 := fun h =>
    hlt.ne (Subgroup.eq_of_le_of_card_ge (normIn_le T T₁) (by rw [h4, h]))
  have hle : Nat.card (normIn T T₁) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  interval_cases h : Nat.card (normIn T T₁)
  all_goals first | rfl | omega

theorem sec6Ctx_of_card_four (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hIso : Section3IsoInput) {T T₁ : Subgroup G} (hy : StepHyp T T₁) (h4 : Nat.card T = 4) :
    Sec6Ctx T T₁ 2 1 := by
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hP := hy.pair
  have hS : Sec3Global T := Sec3Global.of_inputs h214 hInv hP.wc
  have hI : Sec3IsoGlobal T := Sec3IsoGlobal.of_input hIso hy.nonab hS
  have hL := card_normIn_eq_two hP (hP.sec3 hS) h4
  refine ⟨hy, hS, hI, ?_, ?_, Or.inl h4⟩
  · rw [h4, hL]
    norm_num
  · rw [h4]
    norm_num

end CFSG.CGT.T75H
