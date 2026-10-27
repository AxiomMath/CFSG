module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG

@[expose] def pTorsionSub {K : Type} [Group K] (p : ℕ) (Z : Subgroup K)
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) : Subgroup K where
  carrier := {w | w ∈ Z ∧ w ^ p = 1}
  mul_mem' := by
    rintro a b ⟨haZ, hap⟩ ⟨hbZ, hbp⟩
    refine ⟨Z.mul_mem haZ hbZ, ?_⟩
    rw [(show Commute a b from hZ a haZ b hbZ).mul_pow, hap, hbp, one_mul]
  one_mem' := ⟨Z.one_mem, one_pow _⟩
  inv_mem' := by
    rintro a ⟨haZ, hap⟩
    exact ⟨Z.inv_mem haZ, by rw [inv_pow, hap, inv_one]⟩

theorem eq_one_of_inv_eq {K : Type} [Group K] {p : ℕ} (hp2 : p ≠ 2) (hpp : p.Prime) {w : K}
    (hwp : w ^ p = 1) (hw : w⁻¹ = w) : w = 1 := by
  obtain ⟨k, hk⟩ := hpp.odd_of_ne_two hp2
  have h2 : w ^ 2 = 1 := by
    calc w ^ 2 = w * w := sq w
      _ = w * w⁻¹ := by rw [hw]
      _ = 1 := mul_inv_cancel w
  have h3 : w ^ (2 * k + 1) = w := by
    rw [pow_succ, pow_mul, h2, one_pow, one_mul]
  rw [← hk, hwp] at h3
  exact h3.symm

theorem exists_inverted_elemAb {K : Type} [Group K] [Finite K] {u : K} (hu : u * u = 1) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2)
    (hodd : ∀ N : Subgroup K, N ≤ centralizer ({u} : Set K) →
      (∀ c ∈ centralizer ({u} : Set K), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → Odd (Nat.card ↥N) → N = ⊥)
    {X : Subgroup K} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hN : centralizer ({u} : Set K) ≤ normalizer (X : Set K)) :
    ∃ W : Subgroup K, W ≠ ⊥ ∧ (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) ∧ (∀ w ∈ W, w ^ p = 1) ∧
      (∀ c ∈ centralizer ({u} : Set K), ∀ w ∈ W, c * w * c⁻¹ ∈ W) ∧
      (∀ w ∈ W, u * w * u⁻¹ = w⁻¹) := by
  classical
  have hpp : p.Prime := Fact.out
  let Z : Subgroup K := (center ↥X).map X.subtype
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hb' : b ∈ center ↥X := hb
    have := Subgroup.mem_center_iff.mp hb' a
    exact congrArg Subtype.val this
  have hZinv : ∀ c ∈ centralizer ({u} : Set K), ∀ w ∈ Z, c * w * c⁻¹ ∈ Z := by
    rintro c hc _ ⟨x, hx, rfl⟩
    have hx' : x ∈ center ↥X := hx
    have hcN : c ∈ normalizer (X : Set K) := hN hc
    have hmem : c * (x : K) * c⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hcN (x : K)).mp x.2
    refine ⟨⟨c * (x : K) * c⁻¹, hmem⟩, ?_, rfl⟩
    show (⟨c * (x : K) * c⁻¹, hmem⟩ : ↥X) ∈ center ↥X
    rw [Subgroup.mem_center_iff]
    intro y
    have hcinv : c⁻¹ ∈ normalizer (X : Set K) := inv_mem hcN
    have hy' : c⁻¹ * (y : K) * c⁻¹⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hcinv (y : K)).mp y.2
    have hxc := Subgroup.mem_center_iff.mp hx' ⟨c⁻¹ * (y : K) * c⁻¹⁻¹, hy'⟩
    have e1 : (c⁻¹ * (y : K) * c⁻¹⁻¹) * (x : K) = (x : K) * (c⁻¹ * (y : K) * c⁻¹⁻¹) :=
      congrArg Subtype.val hxc
    apply Subtype.ext
    show (y : K) * (c * (x : K) * c⁻¹) = c * (x : K) * c⁻¹ * (y : K)
    calc (y : K) * (c * (x : K) * c⁻¹) = c * ((c⁻¹ * (y : K) * c⁻¹⁻¹) * (x : K)) * c⁻¹ := by group
      _ = c * ((x : K) * (c⁻¹ * (y : K) * c⁻¹⁻¹)) * c⁻¹ := by rw [e1]
      _ = c * (x : K) * c⁻¹ * (y : K) := by group
  let W : Subgroup K := pTorsionSub p Z hZcomm
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => hZcomm a ha.1 b hb.1
  have hWp : ∀ w ∈ W, w ^ p = 1 := fun w hw => hw.2
  have hWinv : ∀ c ∈ centralizer ({u} : Set K), ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c hc w hw
    refine ⟨hZinv c hc w hw.1, ?_⟩
    have : (c * w * c⁻¹) ^ p = c * w ^ p * c⁻¹ := by
      rw [conj_pow]
    rw [this, hw.2]
    group
  have hu_mem : u ∈ centralizer ({u} : Set K) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hW1 : W ≠ ⊥ := by
    have hXn : Nontrivial ↥X := by
      rw [Subgroup.nontrivial_iff_ne_bot]; exact hX1
    have hcn : Nontrivial (center ↥X) := hX.center_nontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : center ↥X)
    have hxx : (x : ↥X) ≠ 1 := fun h => hx (Subtype.ext h)
    obtain ⟨k, hk⟩ := hX (x : ↥X)
    have hord : orderOf (x : ↥X) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hpp).mp hord
    have hj0 : j ≠ 0 := by
      rintro rfl
      have h1 : orderOf (x : ↥X) = 1 := by simpa using hjeq
      exact hxx (orderOf_eq_one_iff.mp h1)
    set y : ↥X := (x : ↥X) ^ (p ^ (j - 1)) with hy
    have hppos : 0 < p ^ (j - 1) := pow_pos hpp.pos _
    have hyord : orderOf y = p := by
      have : orderOf ((x : ↥X) ^ (p ^ (j - 1))) =
          orderOf (x : ↥X) / Nat.gcd (orderOf (x : ↥X)) (p ^ (j - 1)) := orderOf_pow' _ hppos.ne'
      rw [this, hjeq]
      have hg : Nat.gcd (p ^ j) (p ^ (j - 1)) = p ^ (j - 1) :=
        Nat.gcd_eq_right (pow_dvd_pow p (by omega))
      rw [hg]
      have : p ^ j = p ^ (j - 1) * p := by rw [← pow_succ]; congr 1; omega
      rw [this, Nat.mul_div_cancel_left _ hppos]
    have hyz : (y : K) ∈ W := by
      refine ⟨⟨y, ?_, rfl⟩, ?_⟩
      · exact (center ↥X).pow_mem x.2 _
      · have := pow_orderOf_eq_one y
        rw [hyord] at this
        exact congrArg Subtype.val this
    intro hbot
    rw [hbot] at hyz
    have : y = 1 := Subtype.ext (Subgroup.mem_bot.mp hyz)
    rw [this, orderOf_one] at hyord
    exact hpp.one_lt.ne hyord
  have hCW : W ⊓ centralizer ({u} : Set K) = ⊥ := by
    apply hodd (W ⊓ centralizer ({u} : Set K)) inf_le_right
    · intro c hc n hn
      refine Subgroup.mem_inf.mpr ⟨hWinv c hc n (Subgroup.mem_inf.mp hn).1, ?_⟩
      have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
      have hn2 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hn).2
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hcu : c * u = u * c := hc'
      have hcu' : c⁻¹ * u = u * c⁻¹ := by
        calc c⁻¹ * u = c⁻¹ * (u * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * u) * c⁻¹ := by rw [hcu]
          _ = u * c⁻¹ := by group
      calc c * n * c⁻¹ * u = c * n * (c⁻¹ * u) := by group
        _ = c * n * (u * c⁻¹) := by rw [hcu']
        _ = c * (n * u) * c⁻¹ := by group
        _ = c * (u * n) * c⁻¹ := by rw [hn2]
        _ = (c * u) * n * c⁻¹ := by group
        _ = (u * c) * n * c⁻¹ := by rw [hcu]
        _ = u * (c * n * c⁻¹) := by group
    · have : IsPGroup p ↥(W ⊓ centralizer ({u} : Set K)) := fun g => ⟨1, by
        rw [pow_one]
        exact Subtype.ext (hWp g.1 (Subgroup.mem_inf.mp g.2).1)⟩
      exact odd_card_of_isPGroup_odd_prime hp2 this
  refine ⟨W, hW1, hWc, hWp, hWinv, ?_⟩
  intro w hw
  have h1 : u * w * u⁻¹ ∈ W := hWinv u hu_mem w hw
  have hv : w * (u * w * u⁻¹) ∈ W ⊓ centralizer ({u} : Set K) := by
    refine Subgroup.mem_inf.mpr ⟨W.mul_mem hw h1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have e : u * (w * (u * w * u⁻¹)) * u⁻¹ = (u * w * u⁻¹) * w := by
      calc u * (w * (u * w * u⁻¹)) * u⁻¹ = u * w * u⁻¹ * ((u * u) * w * (u * u)⁻¹) := by group
        _ = u * w * u⁻¹ * w := by rw [hu]; group
    have e2 : (u * w * u⁻¹) * w = w * (u * w * u⁻¹) := hWc _ h1 _ hw
    have e3 : u * (w * (u * w * u⁻¹)) * u⁻¹ = w * (u * w * u⁻¹) := by rw [e, e2]
    calc w * (u * w * u⁻¹) * u = u⁻¹⁻¹ * (u⁻¹ * (w * (u * w * u⁻¹)) * u) := by group
      _ = u * (w * (u * w * u⁻¹)) := by
          have : u⁻¹ * (w * (u * w * u⁻¹)) * u = u⁻¹ * (u * (w * (u * w * u⁻¹)) * u⁻¹) * u := by
            rw [e3]
          rw [this]
          group
  rw [hCW, Subgroup.mem_bot] at hv
  exact eq_inv_of_mul_eq_one_right hv

theorem card_mul_dvd_of_normalizes {K : Type} [Group K] [Finite K] (W D : Subgroup K)
    (hDW : D ≤ normalizer (W : Set K)) (hWD : W ⊓ D = ⊥) :
    Nat.card ↥W * Nat.card ↥D ∣ Nat.card K := by
  classical
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient D W hDW
  let _ := Subgroup.normal_subgroupOf_of_le_normalizer hDW
  let _ := Subgroup.normal_subgroupOf_sup_of_le_normalizer hDW
  have h1 : W.subgroupOf D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : K) ∈ W ⊓ D := ⟨hx, x.2⟩
    rw [hWD, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hcardL : Nat.card (↥D ⧸ W.subgroupOf D) = Nat.card ↥D := by
    rw [h1]
    exact Nat.card_congr (QuotientGroup.quotientBot.toEquiv)
  have hcardR := Subgroup.card_eq_card_quotient_mul_card_subgroup (W.subgroupOf (D ⊔ W))
  have hW' : Nat.card ↥(W.subgroupOf (D ⊔ W)) = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hq : Nat.card (↥(D ⊔ W) ⧸ W.subgroupOf (D ⊔ W)) = Nat.card ↥D := by
    rw [← Nat.card_congr e.toEquiv, hcardL]
  have hDW' : Nat.card ↥(D ⊔ W) = Nat.card ↥D * Nat.card ↥W := by
    rw [hcardR, hq, hW']
  have := Subgroup.card_subgroup_dvd_card (D ⊔ W)
  rw [hDW', mul_comm] at this
  exact this

theorem orderOf_eq_two_of_inv {K : Type} [Group K] {u : K} (hu : u * u = 1) (hu1 : u ≠ 1) :
    orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact hu) hu1

theorem ringChar_eq_of_card {F : Type} [Field F] [Finite F] {r f : ℕ} (hr : r.Prime)
    (hcard : Nat.card F = r ^ f) : ringChar F = r := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact r.Prime := ⟨hr⟩
  have : CharP F r := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hcard])
  exact ringChar.eq F r

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
