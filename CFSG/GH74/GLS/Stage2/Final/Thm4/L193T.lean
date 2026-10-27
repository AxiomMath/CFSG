module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.L193FactA

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.L193

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20
open scoped commutatorElement

open CFSG.GH74.Uniqueness.SU.SU1

section Tcore

variable {G : Type} [Group G] [Finite G]

theorem zpowers_eq_of_mem {p : ℕ} {a b : G} (hb : b ∈ zpowers a) (ha : orderOf a = p) (hbo : orderOf b = p) :
    zpowers b = zpowers a := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, ha, hbo]

theorem fb {p : ℕ} [hp : Fact p.Prime] {P U : Subgroup G} (hP : IsPGroup p P)
    (hUn : ∀ g ∈ P, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hUp : ∀ u ∈ U, u ^ p = 1) {z₀ c : G} (hz₀U : z₀ ∈ U) (hz₀1 : z₀ ≠ 1) (hz₀c : ∀ g ∈ P, g * z₀ = z₀ * g)
    (hcU : c ∈ U) (hcz : c ∉ zpowers z₀) (hdec : ∀ u ∈ U, ∃ a b : ℤ, u = c ^ a * z₀ ^ b)
    {g : G} (hg : g ∈ P) : g * c * g⁻¹ * c⁻¹ ∈ zpowers z₀ := by
  have hc1 : c ≠ 1 := fun h => hcz (h ▸ Subgroup.one_mem _)
  have hco : orderOf c = p := orderOf_eq_prime (hUp c hcU) hc1
  have hz₀o : orderOf z₀ = p := orderOf_eq_prime (hUp z₀ hz₀U) hz₀1
  have hcomm : Commute c z₀ := hUc c hcU z₀ hz₀U
  obtain ⟨i, j, hij⟩ := hdec (g * c * g⁻¹) (hUn g hg c hcU)
  have hgz : g * z₀ * g⁻¹ = z₀ := by
    rw [hz₀c g hg]; group
  have hiter : ∀ n : ℕ, ∃ s : ℤ, g ^ n * c * (g ^ n)⁻¹ = c ^ (i ^ n) * z₀ ^ s := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨s, hs⟩ := ih
      refine ⟨j * i ^ n + s, ?_⟩
      have e1 : g ^ (n + 1) * c * (g ^ (n + 1))⁻¹ = g * (g ^ n * c * (g ^ n)⁻¹) * g⁻¹ := by
        rw [pow_succ']; group
      rw [e1, hs]
      have e2 : g * (c ^ (i ^ n) * z₀ ^ s) * g⁻¹ = (g * c * g⁻¹) ^ (i ^ n) * (g * z₀ * g⁻¹) ^ s := by
        rw [conj_zpow, conj_zpow]; group
      rw [e2, hij, hgz, Commute.mul_zpow (hcomm.zpow_left i |>.zpow_right j), ← zpow_mul, ← zpow_mul, pow_succ',
        zpow_add, mul_assoc]
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have hgk : g ^ (p ^ k) = 1 := congrArg Subtype.val hk
  obtain ⟨s, hs⟩ := hiter (p ^ k)
  rw [hgk] at hs
  have hs' : c = c ^ (i ^ (p ^ k)) * z₀ ^ s := by simpa using hs
  have hv : c ^ (i ^ (p ^ k) - 1) = z₀ ^ (-s) := by
    have h1 : c ^ (i ^ (p ^ k)) = c * z₀ ^ (-s) := by
      conv_lhs => rw [show c ^ (i ^ (p ^ k)) = c ^ (i ^ (p ^ k)) * z₀ ^ s * z₀ ^ (-s) by
        rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]]
      rw [← hs']
    rw [zpow_sub_one, h1]
    have : Commute c (z₀ ^ (-s)) := hcomm.zpow_right _
    rw [this.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hv1 : c ^ (i ^ (p ^ k) - 1) = 1 := by
    by_contra hv1
    have hvU : c ^ (i ^ (p ^ k) - 1) ∈ U := Subgroup.zpow_mem _ hcU _
    have hvo : orderOf (c ^ (i ^ (p ^ k) - 1)) = p := orderOf_eq_prime (hUp _ hvU) hv1
    have hvz : c ^ (i ^ (p ^ k) - 1) ∈ zpowers z₀ := hv ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers z₀) _
    have hvc : c ^ (i ^ (p ^ k) - 1) ∈ zpowers c := Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _
    have e1 := zpowers_eq_of_mem hvz hz₀o hvo
    have e2 := zpowers_eq_of_mem hvc hco hvo
    exact hcz (by rw [← e1, e2]; exact Subgroup.mem_zpowers c)
  have hd1 : (p : ℤ) ∣ i ^ (p ^ k) - 1 := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := c) (i := i ^ (p ^ k) - 1)).mpr hv1
    rwa [hco] at this
  have hi1 : (p : ℤ) ∣ i - 1 := by
    have h1 : ((i ^ (p ^ k) - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd1
    push_cast at h1
    have h2 : ((i : ZMod p)) ^ (p ^ k) = 1 := sub_eq_zero.mp h1
    rw [ZMod.pow_card_pow] at h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by push_cast; rw [h2, sub_self])
  have hci : c ^ (i - 1) = 1 := by
    rw [← hco] at hi1
    exact (orderOf_dvd_iff_zpow_eq_one (x := c) (i := i - 1)).mp hi1
  have hfin : g * c * g⁻¹ * c⁻¹ = c ^ (i - 1) * z₀ ^ j := by
    rw [hij]
    have h2 : Commute (z₀ ^ j) c⁻¹ := (hcomm.symm.zpow_left j).inv_right
    calc c ^ i * z₀ ^ j * c⁻¹ = c ^ i * (c⁻¹ * z₀ ^ j) := by rw [mul_assoc, h2.eq]
      _ = (c ^ i * c⁻¹) * z₀ ^ j := by rw [mul_assoc]
      _ = c ^ (i - 1) * z₀ ^ j := by rw [zpow_sub_one]
  rw [hfin, hci, one_mul]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z₀) _

omit [Finite G] in
theorem isPGroup_zpowers' {p : ℕ} {x : G} (hx : x ^ p = 1) : IsPGroup p ↥(zpowers x) := by
  intro a
  refine ⟨1, ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
  apply Subtype.ext
  rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  rfl

@[expose] def NEp (p : ℕ) (P U : Subgroup G) : Prop :=
  U ≤ P ∧ (∀ g ∈ P, ∀ u ∈ U, g * u * g⁻¹ ∈ U) ∧ Open.IsElemAbelian p U ∧ Nat.card ↥U = p ^ 2

theorem fb' {p : ℕ} [hp : Fact p.Prime] {P U : Subgroup G} (hP : IsPGroup p P) (hU : NEp p P U)
    {z₀ : G} (hz₀U : z₀ ∈ U) (hz₀1 : z₀ ≠ 1) (hz₀c : ∀ g ∈ P, g * z₀ = z₀ * g)
    {c : G} (hcU : c ∈ U) {g : G} (hg : g ∈ P) : g * c * g⁻¹ * c⁻¹ ∈ zpowers z₀ := by
  obtain ⟨hUP, hUn, hUel, hUc⟩ := hU
  have hUcomm := (isElemAbelian_iff.mp hUel).1
  have hUp := (isElemAbelian_iff.mp hUel).2
  by_cases hcz : c ∈ zpowers z₀
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hcz
    have : g * z₀ ^ m * g⁻¹ = z₀ ^ m := by
      rw [Commute.eq ((show Commute g z₀ from hz₀c g hg).zpow_right m)]; group
    rw [this]; simp
  · have hc1 : c ≠ 1 := fun h => hcz (h ▸ Subgroup.one_mem _)
    obtain ⟨hel2, hcard2⟩ := isElemAbelian_card_sup_zpowers hp.out (a := z₀) (y := c) (hUp z₀ hz₀U) (hUp c hcU) hz₀1 hcz
      (hUcomm z₀ hz₀U c hcU)
    have hUeq : zpowers z₀ ⊔ zpowers c = U :=
      Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hz₀U) (Subgroup.zpowers_le.mpr hcU))
        (by rw [hUc, hcard2])
    have hdec : ∀ u ∈ U, ∃ a b : ℤ, u = c ^ a * z₀ ^ b := by
      intro u hu
      rw [← hUeq] at hu
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute (fun a ha b hb => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact ((Commute.zpow_zpow (show Commute z₀ c from hUcomm z₀ hz₀U c hcU) m n)).eq) hu
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ⟨n, m, ((Commute.zpow_zpow (show Commute z₀ c from hUcomm z₀ hz₀U c hcU) m n)).eq⟩
    exact fb hP hUn hUcomm hUp hz₀U hz₀1 hz₀c hcU hcz hdec hg

theorem Tcore {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {P : Subgroup G} (hP : IsPGroup p P) {t : G}
    (ht2 : t * t = 1) (htP : ∀ x ∈ P, t * x * t⁻¹ ∈ P)
    (FA : ∀ V : Subgroup G, NEp p P V → ∀ x ∈ P, (∀ u ∈ V, x * u = u * x) → t * x = x * t → x ^ p = 1 → x = 1)
    {U : Subgroup G} (hU : NEp p P U) :
    ∀ y ∈ P, (∀ u ∈ U, y * u = u * y) → t * y * t⁻¹ = y⁻¹ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hU' := hU
  obtain ⟨hUP, hUn, hUel, hUc⟩ := hU
  have hUcomm := (isElemAbelian_iff.mp hUel).1
  have hUp := (isElemAbelian_iff.mp hUel).2
  have hfixiff : ∀ y : G, t * y * t⁻¹ = y → t * y = y * t := fun y h => by
    calc t * y = (t * y * t⁻¹) * t := by group
      _ = y * t := by rw [h]
  suffices hQinv : ∀ y ∈ P, (∀ u ∈ U, y * u = u * y) → ∀ u ∈ U, (t * y * t⁻¹) * u = u * (t * y * t⁻¹) by
    set Q := P ⊓ centralizer (U : Set G) with hQ
    have hQp : IsPGroup p ↥Q := hP.to_le inf_le_left
    have hinv := inverted_of_no_fixed hQp ht2
      (fun e he => ⟨htP e he.1, Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (hQinv e he.1 (fun u' hu' => (Subgroup.mem_centralizer_iff.mp he.2 u' hu').symm) u hu).symm⟩)
      (fun e he hte hep => FA U hU' e he.1 (fun u hu => (Subgroup.mem_centralizer_iff.mp he.2 u hu).symm)
        (hfixiff e hte) hep)
    intro y hy hyc
    exact hinv y ⟨hy, Subgroup.mem_centralizer_iff.mpr fun u hu => (hyc u hu).symm⟩
  by_contra hnot
  have hUne : U ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hUc
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.out.one_lt
    omega
  obtain ⟨z₀, hz₀U, hz₀1, hz₀c⟩ := exists_central_of_normal hp.out hP hUP hUn hUne
  have hz₀p : z₀ ^ p = 1 := hUp z₀ hz₀U
  have hz₀P : z₀ ∈ P := hUP hz₀U
  have hzc : ∀ e ∈ zpowers z₀, ∀ g ∈ P, g * e = e * g := by
    intro e he g hg
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact Commute.eq ((show Commute g z₀ from hz₀c g hg).zpow_right m)
  set z₁ := t * z₀ * t⁻¹ with hz₁
  have hz₁P : z₁ ∈ P := htP z₀ hz₀P
  have hz₁p : z₁ ^ p = 1 := by rw [hz₁, conj_pow, hz₀p]; group
  have hz₁c : ∀ g ∈ P, g * z₁ = z₁ * g := by
    intro g hg
    have hg' : t⁻¹ * g * t ∈ P := by
      rw [hti]
      have := htP g hg
      rwa [hti] at this
    have h1 := hz₀c (t⁻¹ * g * t) hg'
    calc g * z₁ = t * ((t⁻¹ * g * t) * z₀) * t⁻¹ := by rw [hz₁]; group
      _ = t * (z₀ * (t⁻¹ * g * t)) * t⁻¹ := by rw [h1]
      _ = z₁ * g := by rw [hz₁]; group
  by_cases hz₁Z : z₁ ∈ zpowers z₀
  ·
    set Z₀ := zpowers z₀ with hZ₀
    have hZ₀U : Z₀ ≤ U := Subgroup.zpowers_le.mpr hz₀U
    have hZ₀P : Z₀ ≤ P := hZ₀U.trans hUP
    have hZnorm : ∀ e ∈ Z₀, t * e * t⁻¹ ∈ Z₀ := by
      intro e he
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
      have : t * z₀ ^ m * t⁻¹ = z₁ ^ m := by rw [hz₁, conj_zpow]
      rw [this]; exact Subgroup.zpow_mem _ hz₁Z m
    have hZinv : ∀ e ∈ Z₀, t * e * t⁻¹ = e⁻¹ :=
      inverted_of_no_fixed (isPGroup_zpowers' hz₀p) ht2 hZnorm (fun e he hte hep =>
        FA U hU' e (hZ₀P he) (fun u hu => (hzc e he u (hUP hu)).symm) (hfixiff e hte) hep)
    obtain ⟨c, hcU, hct⟩ : ∃ c ∈ U, t * c * t⁻¹ ∉ U := by
      by_contra hno
      push Not at hno
      apply hnot
      intro y hy hyc u hu
      have hu' : t⁻¹ * u * t ∈ U := by
        rw [hti]
        have := hno u hu
        rwa [hti] at this
      have h1 := hyc (t⁻¹ * u * t) hu'
      calc t * y * t⁻¹ * u = t * (y * (t⁻¹ * u * t)) * t⁻¹ := by group
        _ = t * ((t⁻¹ * u * t) * y) * t⁻¹ := by rw [h1]
        _ = u * (t * y * t⁻¹) := by group
    have hfbc : ∀ c' ∈ U, ∀ g ∈ P, g * c' * g⁻¹ * c'⁻¹ ∈ Z₀ := fun c' hc' g hg =>
      fb' hP hU' hz₀U hz₀1 hz₀c hc' hg
    have hconjP : ∀ g ∈ P, t⁻¹ * g * t ∈ P := by
      intro g hg
      rw [hti]
      have := htP g hg
      rwa [hti] at this
    set c₂ := t * c * t⁻¹ with hc₂
    have hc₂P : c₂ ∈ P := htP c (hUP hcU)
    have hfb₂ : ∀ g ∈ P, g * c₂ * g⁻¹ * c₂⁻¹ ∈ Z₀ := by
      intro g hg
      have h2 := hZnorm _ (hfbc c hcU (t⁻¹ * g * t) (hconjP g hg))
      convert h2 using 1
      rw [hc₂]; group
    have htc₂ : t * c₂ * t⁻¹ = c := by
      rw [hc₂, hti]
      calc t * (t * c * t) * t = (t * t) * c * (t * t) := by group
        _ = c := by rw [ht2]; group
    set w := c * c₂ with hw
    have htw : t * w * t⁻¹ = c₂ * c := by
      calc t * w * t⁻¹ = (t * c * t⁻¹) * (t * c₂ * t⁻¹) := by rw [hw]; group
        _ = c₂ * c := by rw [htc₂]
    set ζ := w⁻¹ * (t * w * t⁻¹) with hζ
    have hwζ : w * ζ = c₂ * c := by rw [hζ, htw]; group
    have hζZ : ζ ∈ Z₀ := by
      have := hfbc c⁻¹ (U.inv_mem hcU) c₂⁻¹ (P.inv_mem hc₂P)
      convert this using 1
      rw [hζ, htw, hw]; group
    obtain ⟨n, hn⟩ : ∃ n : ℕ, p = 2 * n + 1 := by
      rcases hp.out.eq_two_or_odd' with h | ⟨n, hn⟩
      · exact absurd h hp2
      · exact ⟨n, hn⟩
    have hζp : ζ ^ p = 1 := by
      obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hζZ
      rw [← he, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz₀p, one_zpow]
    have hζP : ζ ∈ P := hZ₀P hζZ
    have hwP : w ∈ P := P.mul_mem (hUP hcU) hc₂P
    set x₀ := w * ζ ^ (n + 1) with hx₀
    have hx₀P : x₀ ∈ P := P.mul_mem hwP (P.pow_mem hζP _)
    have hζn : ζ * (ζ ^ (n + 1))⁻¹ = ζ ^ (n + 1) := by
      rw [mul_inv_eq_iff_eq_mul, ← pow_add]
      have : (n + 1) + (n + 1) = p + 1 := by omega
      rw [this, pow_succ, hζp, one_mul]
    have hx₀t : t * x₀ * t⁻¹ = x₀ := by
      have h1 : t * x₀ * t⁻¹ = (t * w * t⁻¹) * (t * ζ * t⁻¹) ^ (n + 1) := by
        rw [conj_pow, hx₀]; group
      rw [h1, htw, hZinv ζ hζZ, inv_pow]
      calc c₂ * c * (ζ ^ (n + 1))⁻¹ = (w * ζ) * (ζ ^ (n + 1))⁻¹ := by rw [hwζ]
        _ = w * (ζ * (ζ ^ (n + 1))⁻¹) := by rw [mul_assoc]
        _ = w * ζ ^ (n + 1) := by rw [hζn]
    have hx₀Z : x₀ ∉ Z₀ := by
      intro h
      apply hct
      have hwZ : w ∈ Z₀ := by
        have : w = x₀ * (ζ ^ (n + 1))⁻¹ := by rw [hx₀]; group
        rw [this]
        exact Z₀.mul_mem h (Z₀.inv_mem (Z₀.pow_mem hζZ _))
      have : c₂ = c⁻¹ * w := by rw [hw]; group
      rw [this]
      exact U.mul_mem (U.inv_mem hcU) (hZ₀U hwZ)
    have hx₀1 : x₀ ≠ 1 := fun h => hx₀Z (h ▸ Z₀.one_mem)
    obtain ⟨k, hk⟩ := hP ⟨x₀, hx₀P⟩
    have hx₀pow : x₀ ^ (p ^ k) = 1 := congrArg Subtype.val hk
    have hx₀ord : ∃ k : ℕ, orderOf x₀ = p ^ k := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hx₀pow)
      exact ⟨j, hj⟩
    obtain ⟨m, hm1, hm2⟩ := exists_pow_order_p hx₀ord hx₀1
    set x := x₀ ^ m with hx
    have hxP : x ∈ P := P.pow_mem hx₀P m
    have hxt : t * x * t⁻¹ = x := by rw [hx, conj_pow.symm, hx₀t]
    have hxZ : x ∉ Z₀ := by
      intro h
      have h1 : x = x⁻¹ := by rw [← hZinv x h, hxt]
      have h2 : x * x = 1 := mul_eq_one_iff_eq_inv.mpr h1
      have h3 : x ^ (2 * n + 1) = x := by rw [pow_succ, pow_mul, sq, h2, one_pow, one_mul]
      rw [← hn, hm1] at h3
      exact hm2 h3.symm
    have hconj : ∀ g ∈ P, ∃ ζ' ∈ Z₀, g * x₀ * g⁻¹ = ζ' * x₀ := by
      intro g hg
      set ζ₁ := g * c * g⁻¹ * c⁻¹ with hζ₁
      set ζ₂ := g * c₂ * g⁻¹ * c₂⁻¹ with hζ₂
      have hζ₁Z := hfbc c hcU g hg
      have hζ₂Z := hfb₂ g hg
      refine ⟨ζ₁ * ζ₂, Z₀.mul_mem hζ₁Z hζ₂Z, ?_⟩
      have e1 : g * c * g⁻¹ = ζ₁ * c := by rw [hζ₁]; group
      have e2 : g * c₂ * g⁻¹ = ζ₂ * c₂ := by rw [hζ₂]; group
      have e3 : g * ζ * g⁻¹ = ζ := by rw [hzc ζ hζZ g hg]; group
      have e4 : c * ζ₂ = ζ₂ * c := hzc ζ₂ hζ₂Z c (hUP hcU)
      calc g * x₀ * g⁻¹ = (g * c * g⁻¹) * (g * c₂ * g⁻¹) * (g * ζ * g⁻¹) ^ (n + 1) := by
            rw [conj_pow, hx₀, hw]; group
        _ = (ζ₁ * c) * (ζ₂ * c₂) * ζ ^ (n + 1) := by rw [e1, e2, e3]
        _ = ζ₁ * (c * ζ₂) * c₂ * ζ ^ (n + 1) := by group
        _ = ζ₁ * (ζ₂ * c) * c₂ * ζ ^ (n + 1) := by rw [e4]
        _ = (ζ₁ * ζ₂) * x₀ := by rw [hx₀, hw]; group
    have hconjx : ∀ g ∈ P, ∃ ζ' ∈ Z₀, g * x * g⁻¹ = ζ' * x := by
      intro g hg
      obtain ⟨ζ', hζ'Z, hζ'⟩ := hconj g hg
      refine ⟨ζ' ^ m, Z₀.pow_mem hζ'Z m, ?_⟩
      have hcm : Commute ζ' x₀ := (hzc ζ' hζ'Z x₀ hx₀P).symm
      rw [hx, ← conj_pow, hζ', hcm.mul_pow]
    have hxo : orderOf x = p := orderOf_eq_prime hm1 hm2
    have hz₀o : orderOf z₀ = p := orderOf_eq_prime hz₀p hz₀1
    have hz₀x : z₀ ∉ zpowers x := fun h => hxZ (by
      have := zpowers_eq_of_mem h hxo hz₀o
      show x ∈ zpowers z₀
      rw [this]; exact Subgroup.mem_zpowers x)
    obtain ⟨hel'', hcard''⟩ := isElemAbelian_card_sup_zpowers hp.out (a := x) (y := z₀) hm1 hz₀p hm2 hz₀x
      (hz₀c x hxP)
    have hxz₀ : ∀ a ∈ zpowers x, ∀ b ∈ zpowers z₀, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k₁, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨k₂, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((Commute.zpow_zpow (show Commute x z₀ from hz₀c x hxP) k₁ k₂)).eq
    have hU''P : zpowers x ⊔ zpowers z₀ ≤ P := sup_le (Subgroup.zpowers_le.mpr hxP) hZ₀P
    have hU''n : ∀ g ∈ P, ∀ u ∈ zpowers x ⊔ zpowers z₀, g * u * g⁻¹ ∈ zpowers x ⊔ zpowers z₀ := by
      intro g hg u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hxz₀ hu
      obtain ⟨ζ', hζ'Z, hζ'⟩ := hconjx g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hga : g * x ^ k * g⁻¹ = ζ' ^ k * x ^ k := by
        rw [← conj_zpow, hζ', (show Commute ζ' x from (hzc ζ' hζ'Z x hxP).symm).mul_zpow]
      have hgb : g * b * g⁻¹ = b := by rw [hzc b hb g hg]; group
      have : g * (x ^ k * b) * g⁻¹ = (g * x ^ k * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this, hga, hgb]
      exact (zpowers x ⊔ zpowers z₀).mul_mem
        ((zpowers x ⊔ zpowers z₀).mul_mem (Subgroup.mem_sup_right (Z₀.zpow_mem hζ'Z k))
          (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k)))
        (Subgroup.mem_sup_right hb)
    have hU'' : NEp p P (zpowers x ⊔ zpowers z₀) := ⟨hU''P, hU''n, hel'', hcard''⟩
    have hxU'' : x ∈ zpowers x ⊔ zpowers z₀ := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    exact hm2 (FA _ hU'' x hxP (fun u hu => (isElemAbelian_iff.mp hel'').1 x hxU'' u hu)
      (hfixiff x hxt) hm1)
  ·
    obtain ⟨hel2, hcard2⟩ := isElemAbelian_card_sup_zpowers hp.out hz₀p hz₁p hz₀1 hz₁Z (hz₀c z₁ hz₁P).symm
    have hU₂c : ∀ u ∈ zpowers z₀ ⊔ zpowers z₁, ∀ g ∈ P, g * u = u * g := by
      intro u hu g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute (fun a ha b hb => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact ((Commute.zpow_zpow (show Commute z₀ z₁ from (hz₀c z₁ hz₁P).symm) m n)).eq) hu
      have hza : g * a = a * g := hzc a ha g hg
      have hzb : g * b = b * g := by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact Commute.eq ((show Commute g z₁ from hz₁c g hg).zpow_right n)
      calc g * (a * b) = (g * a) * b := by group
        _ = (a * g) * b := by rw [hza]
        _ = a * (g * b) := by group
        _ = a * (b * g) := by rw [hzb]
        _ = a * b * g := by group
    have hU₂P : zpowers z₀ ⊔ zpowers z₁ ≤ P := sup_le (Subgroup.zpowers_le.mpr hz₀P) (Subgroup.zpowers_le.mpr hz₁P)
    have hU₂ : NEp p P (zpowers z₀ ⊔ zpowers z₁) := ⟨hU₂P, fun g hg u hu => by
      rw [show g * u * g⁻¹ = u by rw [hU₂c u hu g hg]; group]; exact hu, hel2, hcard2⟩
    have hPinv := inverted_of_no_fixed hP ht2 htP (fun e he hte hep =>
      FA _ hU₂ e he (fun u hu => hU₂c u hu e he) (hfixiff e hte) hep)
    apply hnot
    intro y hy hyc u hu
    rw [hPinv y hy]
    exact (Commute.inv_left (show Commute y u from hyc u hu)).eq

end Tcore


section Glue

variable {G : Type} [Group G] [Finite G] {z t g : G} {p : ℕ}

omit [Finite G] in
theorem NEp_of_IsU {U : Subgroup G} (hU : IsU z p U) : NEp p (Op p (Cen z)) U := by
  obtain ⟨hle, hn, hel, hc⟩ := hU
  refine ⟨hle, fun g' hg u hu => ?_, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p U).mp hel, hc⟩
  have := hn.conj_mem ⟨u, hle hu⟩ (by exact hu) ⟨g', hg⟩
  exact this

omit [Finite G] in
theorem IsU_of_NEp {U : Subgroup G} (hU : NEp p (Op p (Cen z)) U) : IsU z p U := by
  obtain ⟨hle, hn, hel, hc⟩ := hU
  refine ⟨hle, ⟨fun n hn' g' => ?_⟩, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p U).mpr hel, hc⟩
  rw [Subgroup.mem_subgroupOf] at hn' ⊢
  exact hn g' g'.2 n hn'

theorem lemma19_3a (h : Ab G z t g p) {U : Subgroup G} (hU : IsU z p U) :
    ∀ y ∈ Qof p (Cen z) U, t * y * t⁻¹ = y⁻¹ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hPp : IsPGroup p ↥(Op p (Cen z)) := isPGroup_Op p _
  have hTP : ∀ x ∈ Op p (Cen z), t * x * t⁻¹ ∈ Op p (Cen z) := fun x hx => Op_norm p _ h.t_mem_M hx
  have FA : ∀ V : Subgroup G, NEp p (Op p (Cen z)) V → ∀ x ∈ Op p (Cen z), (∀ u ∈ V, x * u = u * x) →
      t * x = x * t → x ^ p = 1 → x = 1 := fun V hV x hx hxV hxt hxp =>
    by_contra fun hx1 => factA h (IsU_of_NEp hV) hx hxV hxt hxp hx1
  have := Tcore h.odd hPp h.t2 hTP FA (NEp_of_IsU hU)
  intro y hy
  obtain ⟨hyP, hyU⟩ := mem_Qof.mp hy
  exact this y hyP hyU

end Glue

end CFSG.GH74.GLS.Stage2.Final.Thm4.L193
