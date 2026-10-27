module

public import CFSG.CGT.T75B.OuterCore
public import CFSG.CGT.T75D.CardL

public section

namespace CFSG.CGT.T75B

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki

theorem sec4I4OuterAction_of (hAsc : AschbacherNoPolarInput)
    (h215 : Lemma215Stmt) (h26 : Lemma26Input) (hId : Sec4I4RootGroupInput)
    (hA : Sec4I4TrivialAction)
    (hW : ∀ (f : ℕ) (P : Type) [Group P] [Finite P], 2 ≤ f → (P ≃* PSU3Model f) →
      Lemma21Input P) : Sec4I4OuterAction := by
  intro G _ _ _ hnab hind T T₁ T₂ a h hq h16 x hxD hxT hxN hout
  have hxD' := hxD
  obtain ⟨g, t, ht, -, hxg⟩ := hxD'
  have hxx : x * x = 1 := by
    rw [hxg]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [elemAbelian_mul_self h.pair.wc.1 ht]; group
  obtain ⟨w, hwY, hwT, hxw⟩ := h.exists_normalizing_conj hAsc hq hW hxT hxN hxx hout
  have h' := h.conj_normalizer hwT
  have hN' := sec4N_conj_of_mem h hwY hwT
  have hq' : 2 * Nat.card (normIn T (conjSubgroup w T₁)) < Nat.card T := by
    have hTw : conjSubgroup w T = T := mem_normalizer_iff_conjSubgroup_eq.1 hwT
    have e := normIn_conj w T T₁
    rw [hTw] at e
    rw [e, card_conjSubgroup]
    exact hq
  obtain ⟨f, hf2, -, hsq⟩ := CFSG.CGT.T75D.exists_sq_le_card_normIn hAsc h' hq'
  have hL16 : 16 ≤ Nat.card (normIn T (conjSubgroup w T₁)) := by
    have h4 : 4 ≤ 2 ^ f := calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    nlinarith
  have hxN' : x ∈ Subgroup.normalizer
      (sec4N T (conjSubgroup w T₁) (conjSubgroup w T₂) : Set G) := by
    rw [hN']
    exact hxN
  have hout' : ∀ t ∈ T, ¬ Sec4ActsTriv T (conjSubgroup w T₁) (conjSubgroup w T₂) (x * t) :=
    fun t ht => by
      rw [sec4ActsTriv_conj_iff h hwY hwT]
      exact hout t ht
  exact h'.false_of_outer_fixed hAsc h215 h26 hId hA hW hnab hind hq' h16 hL16 hxD hxT hxw hxN'
    hout'

end CFSG.CGT.T75B
