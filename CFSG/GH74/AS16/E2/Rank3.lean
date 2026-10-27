module

public import CFSG.GH74.E2.Cases
public import CFSG.GH74.AS16.Pairs

public section

namespace CFSG.GH74.AS16.E2

open Subgroup
open CFSG.GH74.E2 hiding Hyp

theorem three_le_evenRank {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P A : Subgroup G} (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P) (hA : ElemAb p A)
    (hcard : Nat.card A = p ^ 3) (hAP : A ≤ normalizer (P : Set G)) :
    3 ≤ Assembly.evenRank G := by
  have hAcomm : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hA.1 a a.2 b b.2)⟩⟩
  have hel : Assembly.IsElemAbelian p A := ⟨hAcomm, hA.2⟩
  have hbdd : ∀ q : ℕ, q.Prime → ∀ H : Subgroup G, Assembly.pRank q H ≤ Nat.card G := by
    intro q hq H
    obtain ⟨E, -, -, hE⟩ := assembly_pRank_attained hq H
    have h1 : q ^ Assembly.pRank q H ≤ Nat.card G := hE ▸ E.card_le_card_group
    exact ((Nat.lt_pow_self hq.one_lt).le).trans h1
  have h3 : 3 ≤ Assembly.pRank p (normalizer (P : Set G)) := by
    unfold Assembly.pRank
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨A, hAP, hel, hcard⟩
    rintro k ⟨E, -, -, hk⟩
    have h1 : p ^ k ≤ Nat.card G := hk ▸ E.card_le_card_group
    exact ((Nat.lt_pow_self hp.one_lt).le).trans h1
  have h4 : Assembly.pRank p (normalizer (P : Set G)) ≤ Assembly.evenRank G := by
    unfold Assembly.evenRank
    refine le_csSup ⟨Nat.card G, ?_⟩
      ⟨p, normalizer (P : Set G), hp, hp2, ⟨P, hP, hP2, rfl⟩, rfl⟩
    rintro k ⟨q, H, hq, -, -, rfl⟩
    exact hbdd q hq H
  omega

theorem false_of_elemAb27 {G : Type} [Group G] [Finite G] (he : Assembly.evenRank G ≤ 2)
    {r : G} (hr : orderOf r = 2) {A : Subgroup G} (hA : ElemAb 3 A) (hcard : Nat.card A = 27)
    (hAc : A ≤ centralizer ({r} : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hr
    omega
  have hP : zpowers r ≠ ⊥ := by
    intro h
    exact hr1 (by simpa using (zpowers_eq_bot.1 h))
  have hP2 : IsPGroup 2 (zpowers r) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hr]
    norm_num
  have hAP : A ≤ normalizer (zpowers r : Set G) := by
    rw [CFSG.GH74.AS16.normalizer_zpowers_eq_centralizer hr]
    exact hAc
  have h3 := three_le_evenRank (p := 3) (by norm_num) (by norm_num) hP hP2 hA
    (by rw [hcard]; norm_num) hAP
  omega

theorem exists_elemAb27 {G : Type*} [Group G] {E : Subgroup G}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hEcard : Nat.card E = 9) {c : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hcE : ∀ e ∈ E, c * e = e * c) (hcnE : c ∉ E) :
    ∃ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 3 = 1) ∧
      Nat.card A = 27 ∧
      ∀ r : G, (∀ e ∈ E, r * e = e * r) → r * c = c * r → A ≤ centralizer ({r} : Set G) := by
  have hprime : (3 : ℕ).Prime := by norm_num
  have hcard_c : Nat.card (zpowers c) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hc3 hc1
  have : Finite (zpowers c) := Nat.finite_of_card_ne_zero (by rw [hcard_c]; norm_num)
  have hdisj : ∀ x ∈ E, x ∈ zpowers c → x = 1 := by
    intro x hxE hxc
    by_contra hx1
    have hxc' : zpowers x = zpowers c := by
      have hle : zpowers x ≤ zpowers c := (zpowers_le).2 hxc
      have hcard_x : Nat.card (zpowers x) = 3 := by
        rw [Nat.card_zpowers]
        have : x ^ 3 = 1 := hE3 x hxE
        exact orderOf_eq_prime this hx1
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard_x, hcard_c])
    apply hcnE
    have : c ∈ zpowers x := by rw [hxc']; exact mem_zpowers c
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 this
    rw [← hk]
    exact E.zpow_mem hxE k
  have hcomm : ∀ (e : E) (w : zpowers c), Commute ((E.subtype) e) ((zpowers c).subtype w) := by
    intro e w
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 w.2
    show (e : G) * (w : G) = (w : G) * (e : G)
    rw [← hk]
    exact ((Commute.zpow_right (Commute.symm (hcE e e.2)) k)).eq
  let φ : E × zpowers c →* G := (E.subtype).noncommCoprod ((zpowers c).subtype) hcomm
  have hφ : ∀ p : E × zpowers c, φ p = (p.1 : G) * (p.2 : G) := fun p => rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨e, w⟩ hker
    rw [MonoidHom.mem_ker, hφ] at hker
    have h1 : (e : G) = ((w : G))⁻¹ := eq_inv_of_mul_eq_one_left hker
    have hw : ((w : G))⁻¹ ∈ zpowers c := (zpowers c).inv_mem w.2
    have he1 : (e : G) = 1 := hdisj e e.2 (h1 ▸ hw)
    have hw1 : (w : G) = 1 := by
      rw [he1, one_mul] at hker
      exact hker
    simp only [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext he1, Subtype.ext hw1⟩
  refine ⟨(⊤ : Subgroup (E × zpowers c)).map φ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, -, rfl⟩ _ ⟨q, -, rfl⟩
    rw [hφ, hφ]
    have h1 : (p.1 : G) * (q.1 : G) = (q.1 : G) * (p.1 : G) := hEc _ p.1.2 _ q.1.2
    have h2 : (p.2 : G) * (q.2 : G) = (q.2 : G) * (p.2 : G) := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 p.2.2
      obtain ⟨l, hl⟩ := mem_zpowers_iff.1 q.2.2
      rw [← hk, ← hl]
      exact ((Commute.refl c).zpow_zpow k l).eq
    have h3 : (p.2 : G) * (q.1 : G) = (q.1 : G) * (p.2 : G) := (hcomm q.1 p.2).eq.symm
    have h4 : (p.1 : G) * (q.2 : G) = (q.2 : G) * (p.1 : G) := (hcomm p.1 q.2).eq
    calc (p.1 : G) * p.2 * ((q.1 : G) * q.2) = p.1 * (p.2 * q.1) * q.2 := by group
      _ = p.1 * (q.1 * p.2) * q.2 := by rw [h3]
      _ = (p.1 * q.1) * (p.2 * q.2) := by group
      _ = (q.1 * p.1) * (q.2 * p.2) := by rw [h1, h2]
      _ = q.1 * (p.1 * q.2) * p.2 := by group
      _ = q.1 * (q.2 * p.1) * p.2 := by rw [h4]
      _ = q.1 * q.2 * (p.1 * p.2) := by group
  · rintro _ ⟨p, -, rfl⟩
    rw [hφ]
    have h1 : (p.1 : G) ^ 3 = 1 := hE3 _ p.1.2
    have h2 : (p.2 : G) ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 p.2.2
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
    have hcm : Commute (p.1 : G) (p.2 : G) := hcomm p.1 p.2
    rw [hcm.mul_pow, h1, h2, one_mul]
  · rw [Subgroup.card_map_of_injective hinj, Subgroup.card_top, Nat.card_prod, hEcard, hcard_c]
  · intro r hrE hrc a ha
    obtain ⟨p, -, rfl⟩ := ha
    rw [hφ, mem_centralizer_singleton_iff]
    have h1 : r * (p.1 : G) = (p.1 : G) * r := hrE _ p.1.2
    have h2 : r * (p.2 : G) = (p.2 : G) * r := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 p.2.2
      rw [← hk]
      exact (Commute.zpow_right hrc k).eq
    calc (p.1 : G) * p.2 * r = p.1 * (p.2 * r) := by group
      _ = p.1 * (r * p.2) := by rw [h2]
      _ = (p.1 * r) * p.2 := by group
      _ = (r * p.1) * p.2 := by rw [h1]
      _ = r * (p.1 * p.2) := by group

theorem false_of_elemAb9_order3 {G : Type} [Group G] [Finite G] (he : Assembly.evenRank G ≤ 2)
    {r : G} (hr : orderOf r = 2) {E : Subgroup G} (hE : ElemAb 3 E) (hEcard : Nat.card E = 9)
    {c : G} (hc : orderOf c = 3) (hcE : ∀ e ∈ E, c * e = e * c) (hcnE : c ∉ E)
    (hrE : ∀ e ∈ E, r * e = e * r) (hrc : r * c = c * r) : False := by
  have hc3 : c ^ 3 = 1 := hc ▸ pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  obtain ⟨A, hAc, hA3, hAcard, hAr⟩ := exists_elemAb27 hE.1 hE.2 hEcard hc3 hc1 hcE hcnE
  exact false_of_elemAb27 he hr ⟨hAc, hA3⟩ hAcard (hAr r hrE hrc)

end CFSG.GH74.AS16.E2
