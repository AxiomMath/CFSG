module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Assembly
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Arith
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.ThirdLineE8

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

theorem not_dvd_and_ne_one_of_orderOf {p q e : ℕ} [Fact p.Prime] (he : e ≠ 0) (he1 : e ≠ 1)
    (hord : orderOf ((q : ℕ) : ZMod p) = e) :
    ¬ p ∣ q ∧ ((q : ℕ) : ZMod p) ≠ 1 ∧ ((q : ℕ) : ZMod p) ^ e = 1 := by
  refine ⟨fun h => ?_, fun h => ?_, hord ▸ pow_orderOf_eq_one _⟩
  · have h0 : ((q : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    rw [h0, orderOf_eq_zero_iff'.2] at hord
    · exact he hord.symm
    · intro n hn h'
      rw [zero_pow hn.ne'] at h'
      exact zero_ne_one h'
  · rw [h, orderOf_one] at hord
    exact he1 hord.symm

theorem exists_charP_card (K : Type) [Field K] [Finite K] :
    ∃ ℓ f : ℕ, ℓ.Prime ∧ CharP K ℓ ∧ 1 ≤ f ∧ Nat.card K = ℓ ^ f := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, hchar⟩ := CharP.exists K
  have hℓ : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K ℓ
  exact ⟨ℓ, n, hℓ, hchar, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩


theorem closure_centralizers_eq_top_F4 (K : Type) [Field K] [Finite K]
    (hframe : ∃ ψA ψB : SL(3, K) →* ModGL Tag.F4 K,
      Function.Injective ψA ∧ Function.Injective ψB ∧ (∀ A B, Commute (ψA A) (ψB B)) ∧
      ψA.range ⊔ ψB.range = rootSpan Tag.F4 K (cosetRoots Tag.F4 1 3))
    (hC : FrameClosing .F4 K (cosetRoots .F4 1 3))
    (hN : FrameNormalizerSolvable .F4 K (cosetRoots .F4 1 3)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 3)
    (hcyc : ∀ g : SL(3, K), orderOf g = p →
      IsCyclic (Subgroup.centralizer ({g} : Set SL(3, K))))
    (E : Subgroup (adjointGroup .F4 K)) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : adjointGroup .F4 K | ∃ x ∈ E, x ≠ 1 ∧ Commute k x} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, f, hℓ, hchar, hf, hK⟩ := exists_charP_card K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨ψA, ψB, hA, hB, hcomm, hrange⟩ := hframe
  obtain ⟨-, hq1, hq3⟩ := not_dvd_and_ne_one_of_orderOf (by norm_num) (by norm_num) hord
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
    have hmul : (((Nat.card K : ℕ) : ZMod p) - 1) *
        (((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1) = 0 := by
      linear_combination hq3
    rcases mul_eq_zero.1 hmul with h | h
    · exact absurd (sub_eq_zero.1 h) hq1
    · exact h
  have hcard : (Nat.card (adjointGroup .F4 K)).factorization p =
      2 * (Nat.card SL(3, K)).factorization p := by
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
      padicValNat_ordF4_of_orderOf_eq_three hp hp5 hq2 hord,
      padicValNat_card_SL_of_orderOf_eq K hp (by norm_num)
        (by rw [← Nat.card_eq_fintype_card]; exact hord), Nat.card_eq_fintype_card]
  refine closure_centralizers_eq_top_of_frame hA hB hcomm hrange hC hN (by omega) hcyc hcard
    ?_ E hEp hEc
  intro F hFc hFp a b haF hbF ha1 hb1
  exact exists_offLine_nonsolvable_F4 K hf hK hp (by omega) hΦ F hFc hFp haF hbF ha1 hb1


theorem closure_centralizers_eq_top_E8 (K : Type) [Field K] [Finite K]
    (hframe : ∃ ψA ψB : SL(5, K) →* ModGL Tag.E8 K,
      Function.Injective ψA ∧ Function.Injective ψB ∧ (∀ A B, Commute (ψA A) (ψB B)) ∧
      ψA.range ⊔ ψB.range = rootSpan Tag.E8 K (cosetRoots Tag.E8 4 5))
    (hC : FrameClosing .E8 K (cosetRoots .E8 4 5))
    (hN : FrameNormalizerSolvable .E8 K (cosetRoots .E8 4 5)) {p : ℕ} (hp : p.Prime)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 5)
    (hcyc : ∀ g : SL(5, K), orderOf g = p →
      IsCyclic (Subgroup.centralizer ({g} : Set SL(5, K))))
    (E : Subgroup (adjointGroup .E8 K)) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : adjointGroup .E8 K | ∃ x ∈ E, x ≠ 1 ∧ Commute k x} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, f, hℓ, hchar, hf, hK⟩ := exists_charP_card K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨ψA, ψB, hA, hB, hcomm, hrange⟩ := hframe
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp11 : 11 ≤ p := by
    obtain ⟨hpq, -, -⟩ := not_dvd_and_ne_one_of_orderOf (by norm_num) (by norm_num) hord
    have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := fun h =>
      hpq ((ZMod.natCast_eq_zero_iff _ _).1 h)
    have hdvd : 5 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hq0
    obtain ⟨k, hk⟩ := hdvd
    have h2 := hp.two_le
    rcases k with _ | _ | k
    · omega
    · have : p = 6 := by omega
      subst this
      exact absurd hp (by norm_num)
    · omega
  have hcard : (Nat.card (adjointGroup .E8 K)).factorization p =
      2 * (Nat.card SL(5, K)).factorization p := by
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8,
      padicValNat_ordE8_of_orderOf_eq_five hp (by omega) hq2 hord,
      padicValNat_card_SL_of_orderOf_eq K hp (by norm_num)
        (by rw [← Nat.card_eq_fintype_card]; exact hord), Nat.card_eq_fintype_card]
  refine closure_centralizers_eq_top_of_frame hA hB hcomm hrange hC hN (by omega) hcyc hcard
    ?_ E hEp hEc
  intro F hFc hFp a b haF hbF ha1 hb1
  exact exists_offLine_nonsolvable_E8 K hf hK hp (by omega) hord F hFc hFp haF hbF ha1 hb1

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
