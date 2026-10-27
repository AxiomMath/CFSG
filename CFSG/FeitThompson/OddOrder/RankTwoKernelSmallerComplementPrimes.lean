module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.OddOrder.FreeActionKernelCongruence
import Mathlib.GroupTheory.Complement

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {L : Type*} [Group L] {H U : Subgroup L} {d n p q : ℕ}

theorem mul_comm_of_mem_of_isMulCommutative {K : Subgroup L} [IsMulCommutative K] {x y : L}
    (hx : x ∈ K) (hy : y ∈ K) : x * y = y * x :=
  congrArg Subtype.val (IsMulCommutative.is_comm (M := K).comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem mem_elementaryAbelianRanks_subgroup_iff (hp : p.Prime) :
    d ∈ elementaryAbelianRanks p H ↔
      ∃ A : Subgroup L, A ≤ H ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ (∀ x ∈ A, x ^ p = 1) ∧
        Nat.card A = p ^ d := by
  rw [mem_elementaryAbelianRanks_iff_exists_subgroup hp]
  constructor
  · rintro ⟨P, hcomm, hexp, hcard⟩
    refine ⟨P.map H.subtype, Subgroup.map_subtype_le P, ?_, ?_, ?_⟩
    · rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
      exact congrArg (fun z : H => (z : L))
        (congrArg Subtype.val (IsMulCommutative.is_comm (M := P).comm ⟨x', hx'⟩ ⟨y', hy'⟩))
    · rintro x ⟨y, hy, rfl⟩
      exact congrArg (fun z : H => (z : L)) (hexp y hy)
    · rw [Subgroup.card_map_of_injective H.subtype_injective, hcard]
  · rintro ⟨A, hAH, hcomm, hexp, hcard⟩
    exact ⟨A.subgroupOf H, IsMulCommutative.of_comm fun x y =>
      Subtype.ext (Subtype.ext (hcomm x.1.1 x.2 y.1.1 y.2)), fun x hx => Subtype.ext (hexp x.1 hx),
      by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hcard]⟩

def powTorsion (H : Subgroup L) [IsMulCommutative H] (n : ℕ) : Subgroup L where
  carrier := {x | x ∈ H ∧ x ^ n = 1}
  one_mem' := ⟨H.one_mem, one_pow n⟩
  mul_mem' {a b} ha hb := by
    refine ⟨H.mul_mem ha.1 hb.1, ?_⟩
    have hc : Commute a b := mul_comm_of_mem_of_isMulCommutative ha.1 hb.1
    rw [hc.mul_pow, ha.2, hb.2, one_mul]
  inv_mem' {a} ha := ⟨H.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

@[simp]
theorem mem_powTorsion [IsMulCommutative H] {x : L} :
    x ∈ powTorsion H n ↔ x ∈ H ∧ x ^ n = 1 := Iff.rfl

theorem powTorsion_le [IsMulCommutative H] (n : ℕ) : powTorsion H n ≤ H := fun _ hx => hx.1

theorem pow_eq_one_of_mem_powTorsion [IsMulCommutative H] {x : L} (hx : x ∈ powTorsion H n) :
    x ^ n = 1 := hx.2

theorem le_powTorsion [IsMulCommutative H] {A : Subgroup L} (hAH : A ≤ H)
    (hA : ∀ x ∈ A, x ^ n = 1) : A ≤ powTorsion H n := fun x hx => ⟨hAH hx, hA x hx⟩

instance powTorsion_isMulCommutative [IsMulCommutative H] (n : ℕ) :
    IsMulCommutative (powTorsion H n) :=
  IsMulCommutative.of_comm fun a b =>
    Subtype.ext (mul_comm_of_mem_of_isMulCommutative a.2.1 b.2.1)

instance powTorsion_normal [IsMulCommutative H] [hH : H.Normal] (n : ℕ) :
    (powTorsion H n).Normal where
  conj_mem x hx g := ⟨hH.conj_mem x hx.1 g, by rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩

theorem isPGroup_powTorsion [IsMulCommutative H] : IsPGroup p (powTorsion H p) :=
  fun g => ⟨1, Subtype.ext (by simpa using g.2.2)⟩

@[instance_reducible]
def conjMulDistribMulAction (V A : Subgroup L) [A.Normal] : MulDistribMulAction V A :=
  MulDistribMulAction.compHom (M := ConjAct L) _
    (ConjAct.toConjAct.toMonoidHom.comp V.subtype)

attribute [local instance] conjMulDistribMulAction

theorem conjMulDistribMulAction_smul_coe (V A : Subgroup L) [A.Normal] (v : V) (a : A) :
    ((v • a : A) : L) = (v : L) * (a : L) * (v : L)⁻¹ := by
  change ((ConjAct.toConjAct (v : L) • a : A) : L) = _
  rw [ConjAct.Subgroup.val_conj_smul, ConjAct.smul_def]
  simp

theorem natCard_dvd_natCard_sub_one_of_conj_free [Finite L] (V A : Subgroup L) [A.Normal]
    (h : ∀ a ∈ A, a ≠ 1 → ∀ v ∈ V, v * a * v⁻¹ = a → v = 1) :
    Nat.card V ∣ Nat.card A - 1 := by
  refine card_dvd_card_sub_one_of_smul_eq_self V A fun a ha v hv => ?_
  refine Subtype.ext (h a a.2 (fun hh => ha (Subtype.ext hh)) v v.2 ?_)
  rw [← conjMulDistribMulAction_smul_coe V A v a, hv]

theorem natCard_powTorsion_eq_sq [Finite L] [IsMulCommutative H] (hp : p.Prime)
    (h2 : 2 ∈ elementaryAbelianRanks p H) (h3 : 3 ∉ elementaryAbelianRanks p H) :
    Nat.card (powTorsion H p) = p ^ 2 := by
  have := Fact.mk hp
  set A := powTorsion H p with hA
  obtain ⟨k, hk⟩ := (isPGroup_powTorsion (H := H) (p := p)).exists_card_eq
  obtain ⟨A₀, hA₀H, -, hA₀exp, hA₀card⟩ := (mem_elementaryAbelianRanks_subgroup_iff hp).1 h2
  have hdvd : p ^ 2 ∣ p ^ k := by
    rw [← hk, ← hA₀card]
    exact Subgroup.card_dvd_of_le (le_powTorsion hA₀H hA₀exp)
  have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
  have hk3 : k < 3 := by
    by_contra hk3
    obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := 3)
      (by rw [hk]; exact pow_dvd_pow p (by omega))
    refine h3 ((mem_elementaryAbelianRanks_subgroup_iff hp).2
      ⟨K.map A.subtype, (Subgroup.map_subtype_le K).trans (powTorsion_le p), ?_, ?_, ?_⟩)
    · rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
      exact mul_comm_of_mem_of_isMulCommutative (powTorsion_le p x'.2) (powTorsion_le p y'.2)
    · rintro x ⟨y, hy, rfl⟩
      exact pow_eq_one_of_mem_powTorsion y.2
    · rw [Subgroup.card_map_of_injective A.subtype_injective, hKcard]
  rw [hk, show k = 2 by omega]

theorem prime_lt_of_dvd_natCard_of_isComplement [Finite L] [H.Normal] {U0 : Subgroup U}
    (hodd : Odd (Nat.card L))
    (hprod : (H : Set L) * (U : Set L) = Set.univ) (hint : H ⊓ U = ⊥)
    (hp : p.Prime) (hHp : 2 ∈ elementaryAbelianRanks p H)
    (hexpU0 : Monoid.exponent U0 = Monoid.exponent U)
    (hfree : ∀ u ∈ U0, (u : L) ≠ 1 → H ⊓ Subgroup.centralizer {(u : L)} = ⊥)
    (halt : (IsMulCommutative H ∧ ∀ r : ℕ, r.Prime → 3 ∉ elementaryAbelianRanks r H) ∨
      Monoid.exponent U ∣ p - 1)
    (hq : q.Prime) (hqU : q ∣ Nat.card U) : q < p := by
  have := Fact.mk hp
  have hcompl : H.IsComplement' U :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hint) hprod
  have hcard : Nat.card H * Nat.card U = Nat.card L := hcompl.card_mul_card
  have hqodd : Odd q := hodd.of_dvd_nat (hqU.trans ⟨Nat.card H, by rw [← hcard]; ring⟩)
  obtain ⟨A₀, -, -, -, hA₀card⟩ := (mem_elementaryAbelianRanks_subgroup_iff hp).1 hHp
  have hpL : p ∣ Nat.card L :=
    (dvd_pow_self p two_ne_zero).trans (by rw [← hA₀card]; exact A₀.card_subgroup_dvd_card)
  have hpodd : Odd p := hodd.of_dvd_nat hpL
  have hp3 : 3 ≤ p := by
    have h2 : p ≠ 2 := by rintro rfl; exact absurd hpodd (by decide)
    have := hp.two_le
    omega
  have hqexp : q ∣ Monoid.exponent U := by
    have := Fact.mk hq
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := U) q hqU
    exact hx ▸ Monoid.order_dvd_exponent x
  rcases halt with ⟨hcomm, h3⟩ | hexp
  ·
    have hAcard : Nat.card (powTorsion H p) = p ^ 2 :=
      natCard_powTorsion_eq_sq hp hHp (h3 p hp)
    have hdvd : Nat.card U0 ∣ p ^ 2 - 1 := by
      rw [← Subgroup.card_map_of_injective (K := U0) U.subtype_injective, ← hAcard]
      refine natCard_dvd_natCard_sub_one_of_conj_free _ (powTorsion H p)
        fun a ha ha1 v hv hconj => ?_
      obtain ⟨w, hw, rfl⟩ := hv
      by_contra hne
      have hmem : a ∈ H ⊓ Subgroup.centralizer {(w : L)} :=
        ⟨powTorsion_le p ha, Subgroup.mem_centralizer_singleton_iff.2
          (mul_inv_eq_iff_eq_mul.mp hconj).symm⟩
      rw [hfree w hw hne, Subgroup.mem_bot] at hmem
      exact ha1 hmem
    have hqp2 : q ∣ p ^ 2 - 1 :=
      hqexp.trans ((hexpU0 ▸ Group.exponent_dvd_nat_card).trans hdvd)
    rw [show p ^ 2 - 1 = (p - 1) * (p + 1) by
      rw [Nat.sub_mul, one_mul, pow_two, Nat.mul_succ]; omega] at hqp2
    rcases (Nat.Prime.dvd_mul hq).1 hqp2 with h | h
    ·
      have := Nat.le_of_dvd (by omega) h
      omega
    ·
      obtain ⟨m, hm⟩ := h
      obtain ⟨j0, hj0⟩ := hpodd
      have hm2 : 2 ∣ m := by
        have h2 : (2 : ℕ) ∣ q * m := by rw [← hm]; exact ⟨j0 + 1, by omega⟩
        rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h' | h'
        · obtain ⟨c, hc⟩ := h'
          obtain ⟨k0, hk0⟩ := hqodd
          omega
        · exact h'
      obtain ⟨j, rfl⟩ := hm2
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · exact absurd hm (by simp)
        · exact hj
      have hle : q * 2 ≤ q * (2 * j) := Nat.mul_le_mul_left q (by omega)
      omega
  ·
    have := Nat.le_of_dvd (by omega) (hqexp.trans hexp)
    omega

end

end CFSG.FeitThompson
