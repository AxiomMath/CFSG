module

public import CFSG.CGT.Timmesfeld75.WeaklyClosed

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem perm_six_no_order_ten : ∀ σ : Equiv.Perm (Fin 6), σ ^ 10 = 1 → σ ^ 2 = 1 ∨ σ ^ 5 = 1 := by
  decide +kernel

theorem A6_no_order_ten {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 6)) (g : K) :
    orderOf g ≠ 10 := by
  intro h
  have h1 : orderOf ((e g : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = 10 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, h]
  have h2 := pow_orderOf_eq_one ((e g : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
  rw [h1] at h2
  rcases perm_six_no_order_ten _ h2 with h3 | h3
  · have := orderOf_dvd_of_pow_eq_one h3
    rw [h1] at this
    omega
  · have := orderOf_dvd_of_pow_eq_one h3
    rw [h1] at this
    omega

theorem card_le_eight_of_elemAbelian {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 6))
    {V : Subgroup K} (hV : IsElemAbelian 2 V) : Nat.card V ≤ 8 := by
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (isPGroup_two_of_isElemAbelian hV)
  have hdvd : Nat.card V ∣ 360 := by
    have h1 := Subgroup.card_subgroup_dvd_card V
    rwa [Nat.card_congr e.toEquiv, card_alternatingGroup_six] at h1
  rw [hn] at hdvd ⊢
  by_contra h
  have h4 : 4 ≤ n := by
    by_contra h4
    push Not at h4
    interval_cases n <;> omega
  have : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 h4
  have h16 : 16 ∣ 360 := (by norm_num : 16 = 2 ^ 4) ▸ this.trans hdvd
  omega

end CFSG.CGT.Timmesfeld75
