module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Spor
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

theorem exists_prime_order_of_quotient {S : Type} [Group S] {H : Subgroup S} [Finite H]
    (N : Subgroup H) [N.Normal] {q : ℕ} [Fact q.Prime] (hq : q ∣ Nat.card (H ⧸ N)) :
    ∃ y : S, y ∈ H ∧ orderOf y = q := by
  obtain ⟨yb, hyb⟩ := exists_prime_orderOf_dvd_card' (G := H ⧸ N) q hq
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective yb
  have hn : orderOf y0 ≠ 0 := (orderOf_pos y0).ne'
  have hqn : q ∣ orderOf y0 := by
    rw [← hyb]
    exact orderOf_dvd_of_pow_eq_one (by
      rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one])
  obtain ⟨m, hm⟩ := hqn
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact hn hm
  have hord : orderOf (y0 ^ m) = q := by
    rw [orderOf_pow' _ hm0, hm, Nat.gcd_mul_left_left]
    exact Nat.mul_div_cancel q (Nat.pos_of_ne_zero hm0)
  exact ⟨((y0 ^ m : H) : S), (y0 ^ m).2, by rw [Subgroup.orderOf_coe, hord]⟩

theorem exists_order_mul_of_fi22Cfg {G : Type} [Group G] {x : G} (hx5 : x ^ 5 = 1)
    (hx1 : x ≠ 1) (q : ℕ) [Fact q.Prime] (hq5 : q ≠ 5) (hqF : q ∣ Nat.card Fi22G)
    (hQ0 : Nat.card Fi22G ≠ 0) (hcfg : Fi22Cfg G (MulAut.conj x)) : ∃ g : G, orderOf g = 5 * q := by
  obtain ⟨H, hH, N, hN, hc, ⟨φ⟩⟩ := hcfg
  have hNfin : Finite N := Nat.finite_of_card_ne_zero (by
    intro h0
    rw [h0] at hc
    norm_num at hc)
  have hQfin : Finite Fi22G := Nat.finite_of_card_ne_zero hQ0
  have hHQ : Finite (H ⧸ N) := Finite.of_equiv _ φ.toEquiv.symm
  have hHfin : Finite H := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
    exact mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  have hHx : H ≤ Subgroup.centralizer ({x} : Set G) := by
    have := le_of_isSubnormal' hH
    rwa [fixedSub_conj] at this
  have hq : q ∣ Nat.card (H ⧸ N) := by
    rw [Nat.card_congr φ.toEquiv]
    exact hqF
  obtain ⟨y, hyH, hyq⟩ := exists_prime_order_of_quotient N hq
  have hcomm : Commute x y :=
    (Subgroup.mem_centralizer_iff.1 (hHx hyH) x rfl).symm.symm
  have hord5 : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  have hcop : Nat.Coprime (orderOf x) (orderOf y) := by
    rw [hord5, hyq]
    exact (Nat.coprime_primes (by norm_num) Fact.out).2 hq5.symm
  exact ⟨x * y, by rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hord5, hyq]⟩

@[expose] def NoOrderSixtyFiveAt (s : TauCeti.SporadicName) : Prop :=
  ∀ g : (TauCeti.CFSGIndex.sporadic s).Group, orderOf g ≠ 65

@[expose] def NoOrderSixtyFive : Prop :=
  ∀ s : TauCeti.SporadicName, (s = .Co1 ∨ s = .B ∨ s = .M) → NoOrderSixtyFiveAt s

theorem fi22FiveCentBig_of_noOrderSixtyFive
    (h : NoOrderSixtyFive) : Fi22FiveCentBig := by
  intro s hs x hx5 hx1 hcfg
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨-, hcard⟩ := fi22_facts
  obtain ⟨g, hg⟩ := exists_order_mul_of_fi22Cfg hx5 hx1 13 (by norm_num) (by
    rw [hcard]
    decide +kernel) (by rw [hcard]; norm_num) hcfg
  exact h s hs g hg

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
