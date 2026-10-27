module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section UComm

variable {G : Type*} [Group G]

theorem s11_zpow_eq_one_of_two_mul {y : G} (hy : orderOf y = 3) {k : ℤ} (h : y ^ (2 * k) = 1) :
    y ^ k = 1 := by
  have h1 : (3 : ℤ) ∣ 2 * k := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h
    rw [hy] at this
    exact_mod_cast this
  have h2 : (3 : ℤ) ∣ k := by omega
  exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [hy]; exact_mod_cast h2)

theorem s11_u_comm_O {O : Subgroup G} {t u u₁ y : G} (ht : t * t = 1) (hu : u * u = 1)
    (hu₁ : u₁ * u₁ = 1) (hy3 : orderOf y = 3) (hyO : y ∈ O)
    (hOy : ∀ o ∈ O, o * y = y * o) (hty : t * y = y * t) (huy : u * y = y * u)
    (hu₁y : u₁ * y = y * u₁) (hOu₁ : ∀ o ∈ O, u₁ * o * u₁⁻¹ ∈ O)
    (hOinv : ∀ o ∈ O, t * o * t⁻¹ * o ∈ zpowers y) (htu₁ : t * u₁ * t⁻¹ = u * u₁) :
    ∀ o ∈ O, u * o = o * u := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hu₁' : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right hu₁
  have hyc : ∀ (n : ℤ), Commute u₁ (y ^ n) := fun n => (show Commute u₁ y from hu₁y).zpow_right n
  have hyt : ∀ (n : ℤ), Commute t (y ^ n) := fun n => (show Commute t y from hty).zpow_right n
  have huc : ∀ (n : ℤ), Commute u (y ^ n) := fun n => (show Commute u y from huy).zpow_right n
  have key : ∀ w ∈ O, ∃ k : ℤ, u * w * u⁻¹ = y ^ k * w := by
    intro w hw
    set p : G := u₁ * w * u₁⁻¹ with hp
    have hpO : p ∈ O := hOu₁ w hw
    obtain ⟨a, ha⟩ := mem_zpowers_iff.1 (hOinv p hpO)
    obtain ⟨b, hb⟩ := mem_zpowers_iff.1 (hOinv w hw)
    have e1 : t * p * t⁻¹ = y ^ a * p⁻¹ := by
      calc t * p * t⁻¹ = t * p * t⁻¹ * p * p⁻¹ := by group
        _ = y ^ a * p⁻¹ := by rw [ha]
    have e2 : t * w * t⁻¹ = y ^ b * w⁻¹ := by
      calc t * w * t⁻¹ = t * w * t⁻¹ * w * w⁻¹ := by group
        _ = y ^ b * w⁻¹ := by rw [hb]
    have hwp : u₁ * p * u₁⁻¹ = w := by
      rw [hp, hu₁']
      calc u₁ * (u₁ * w * u₁) * u₁ = (u₁ * u₁) * w * (u₁ * u₁) := by group
        _ = w := by rw [hu₁]; group
    refine ⟨a - b, ?_⟩
    have hconj : u * w * u⁻¹ = (t * u₁ * t⁻¹) * p * (t * u₁ * t⁻¹)⁻¹ := by
      rw [htu₁, ← hwp]
      group
    rw [hconj]
    have e3 : (t * u₁ * t⁻¹) * p * (t * u₁ * t⁻¹)⁻¹ =
        t * (u₁ * (t⁻¹ * p * t) * u₁⁻¹) * t⁻¹ := by group
    rw [e3]
    have e4 : t⁻¹ * p * t = y ^ a * p⁻¹ := by
      rw [ht']
      rw [ht'] at e1
      exact e1
    rw [e4]
    have e5 : u₁ * (y ^ a * p⁻¹) * u₁⁻¹ = y ^ a * w⁻¹ := by
      have h1 : u₁ * y ^ a * u₁⁻¹ = y ^ a := by rw [(hyc a).eq]; group
      calc u₁ * (y ^ a * p⁻¹) * u₁⁻¹ = (u₁ * y ^ a * u₁⁻¹) * (u₁ * p⁻¹ * u₁⁻¹) := by group
        _ = y ^ a * w⁻¹ := by
          have : u₁ * p⁻¹ * u₁⁻¹ = (u₁ * p * u₁⁻¹)⁻¹ := by group
          rw [h1, this, hwp]
    rw [e5]
    have e6 : t * (y ^ a * w⁻¹) * t⁻¹ = y ^ a * (t * w * t⁻¹)⁻¹ := by
      have h1 : t * y ^ a * t⁻¹ = y ^ a := by rw [(hyt a).eq]; group
      calc t * (y ^ a * w⁻¹) * t⁻¹ = (t * y ^ a * t⁻¹) * (t * w⁻¹ * t⁻¹) := by group
        _ = y ^ a * (t * w * t⁻¹)⁻¹ := by
          rw [h1]
          group
    rw [e6, e2]
    calc y ^ a * (y ^ b * w⁻¹)⁻¹ = y ^ a * (w * y ^ (-b)) := by
          rw [mul_inv_rev, inv_inv, zpow_neg]
      _ = y ^ a * (y ^ (-b) * w) := by
          rw [← (show Commute w (y ^ (-b)) from ((show Commute w y from hOy w hw).zpow_right _)).eq]
      _ = y ^ (a - b) * w := by rw [← mul_assoc, ← zpow_add, sub_eq_add_neg]
  intro o ho
  obtain ⟨k, hk⟩ := key o ho
  have hyo : y ^ k * o ∈ O := O.mul_mem (O.zpow_mem hyO k) ho
  obtain ⟨k', hk'⟩ := key (y ^ k * o) hyo
  have hsq : u * (u * o * u⁻¹) * u⁻¹ = o := by
    rw [hu']
    calc u * (u * o * u) * u = (u * u) * o * (u * u) := by group
      _ = o := by rw [hu]; group
  have h2 : u * (y ^ k * o) * u⁻¹ = y ^ (2 * k) * o := by
    have h1 : u * y ^ k * u⁻¹ = y ^ k := by rw [(huc k).eq]; group
    calc u * (y ^ k * o) * u⁻¹ = (u * y ^ k * u⁻¹) * (u * o * u⁻¹) := by group
      _ = y ^ (2 * k) * o := by
        rw [h1, hk, ← mul_assoc, ← zpow_add, two_mul]
  rw [hk] at hsq
  rw [h2] at hsq
  have hy2 : y ^ (2 * k) = 1 := by
    have := hsq
    calc y ^ (2 * k) = y ^ (2 * k) * o * o⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  have hk0 : y ^ k = 1 := s11_zpow_eq_one_of_two_mul hy3 hy2
  rw [hk0, one_mul] at hk
  calc u * o = u * o * u⁻¹ * u := by group
    _ = o * u := by rw [hk]

end UComm

section Plane

variable {G : Type*} [Group G]

theorem s11_conj_zpow (t x : G) (k : ℤ) : t * x ^ k * t⁻¹ = (t * x * t⁻¹) ^ k := by
  simp

theorem s11_split {t x : G} {X Xt O : Subgroup G} (ht : t * t = 1) (hxX : x ∈ X)
    (hXt : ∀ c ∈ X, t * c * t⁻¹ ∈ Xt) (hcomm : ∀ a ∈ X, ∀ b ∈ Xt, a * b = b * a)
    (hinf : ∀ a ∈ X, a ∈ Xt → a = 1)
    (hOinv : ∀ o ∈ O, t * o * t⁻¹ * o ∈ zpowers (x * (t * x * t⁻¹)))
    {o a c : G} (ho : o ∈ O) (ha : a ∈ X) (hc : c ∈ X) (hoe : o = a * (t * c * t⁻¹)) :
    ∃ k : ℤ, a = c⁻¹ * x ^ k := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hOinv o ho)
  have hxt : t * x * t⁻¹ ∈ Xt := hXt x hxX
  have hcx : Commute x (t * x * t⁻¹) := hcomm x hxX _ hxt
  rw [hcx.mul_zpow] at hk
  have e1 : t * o * t⁻¹ = (t * a * t⁻¹) * c := by
    rw [hoe]
    calc t * (a * (t * c * t⁻¹)) * t⁻¹ = (t * a * t⁻¹) * (t * t) * c * (t⁻¹ * t⁻¹) := by group
      _ = (t * a * t⁻¹) * c := by rw [ht, ht', ht]; group
  have hta : t * a * t⁻¹ ∈ Xt := hXt a ha
  have htac : t * (a * c) * t⁻¹ ∈ Xt := by
    have := hXt (a * c) (X.mul_mem ha hc)
    exact this
  have e2 : t * o * t⁻¹ * o = (c * a) * (t * (a * c) * t⁻¹) := by
    rw [e1, hoe]
    have h1 : (t * a * t⁻¹) * c = c * (t * a * t⁻¹) := (hcomm c hc _ hta).symm
    have h2 : (t * a * t⁻¹) * a = a * (t * a * t⁻¹) := (hcomm a ha _ hta).symm
    calc t * a * t⁻¹ * c * (a * (t * c * t⁻¹))
        = c * (t * a * t⁻¹) * a * (t * c * t⁻¹) := by rw [h1]; simp only [mul_assoc]
      _ = c * (a * (t * a * t⁻¹)) * (t * c * t⁻¹) := by rw [mul_assoc c, h2, ← mul_assoc]
      _ = (c * a) * (t * (a * c) * t⁻¹) := by group
  have hxk : x ^ k ∈ X := X.zpow_mem hxX k
  have hxtk : (t * x * t⁻¹) ^ k ∈ Xt := Xt.zpow_mem hxt k
  have h3 : (c * a) * (x ^ k)⁻¹ = (t * x * t⁻¹) ^ k * (t * (a * c) * t⁻¹)⁻¹ := by
    have : (c * a) * (t * (a * c) * t⁻¹) = x ^ k * (t * x * t⁻¹) ^ k := e2.symm.trans hk.symm
    have hcomm' : x ^ k * (t * x * t⁻¹) ^ k = (t * x * t⁻¹) ^ k * x ^ k :=
      hcomm _ hxk _ hxtk
    calc (c * a) * (x ^ k)⁻¹ = (c * a) * (t * (a * c) * t⁻¹) * (t * (a * c) * t⁻¹)⁻¹ *
          (x ^ k)⁻¹ := by group
      _ = (t * x * t⁻¹) ^ k * x ^ k * (t * (a * c) * t⁻¹)⁻¹ * (x ^ k)⁻¹ := by
          rw [this, hcomm']
      _ = (t * x * t⁻¹) ^ k * (t * (a * c) * t⁻¹)⁻¹ := by
          have hc2 : x ^ k * (t * (a * c) * t⁻¹)⁻¹ = (t * (a * c) * t⁻¹)⁻¹ * x ^ k :=
            hcomm _ hxk _ (Xt.inv_mem htac)
          calc (t * x * t⁻¹) ^ k * x ^ k * (t * (a * c) * t⁻¹)⁻¹ * (x ^ k)⁻¹
              = (t * x * t⁻¹) ^ k * (x ^ k * (t * (a * c) * t⁻¹)⁻¹) * (x ^ k)⁻¹ := by
                simp only [mul_assoc]
            _ = (t * x * t⁻¹) ^ k * ((t * (a * c) * t⁻¹)⁻¹ * x ^ k) * (x ^ k)⁻¹ := by rw [hc2]
            _ = _ := by group
  have h4 : (c * a) * (x ^ k)⁻¹ = 1 :=
    hinf _ (X.mul_mem (X.mul_mem hc ha) (X.inv_mem hxk)) (by
      rw [h3]; exact Xt.mul_mem hxtk (Xt.inv_mem htac))
  refine ⟨k, ?_⟩
  have h5 : c * a = x ^ k := mul_inv_eq_one.1 h4
  calc a = c⁻¹ * (c * a) := by group
    _ = c⁻¹ * x ^ k := by rw [h5]

theorem s11_plane [Finite G] {t x g : G} {X Xt O : Subgroup G} (ht : t * t = 1)
    (hx3 : orderOf x = 3)
    (hxX : x ∈ X) (hXcard : Nat.card X = 9)
    (hXt : ∀ c ∈ X, t * c * t⁻¹ ∈ Xt)
    (hcomm : ∀ a ∈ X, ∀ b ∈ Xt, a * b = b * a) (hinf : ∀ a ∈ X, a ∈ Xt → a = 1)
    (hOinv : ∀ o ∈ O, t * o * t⁻¹ * o ∈ zpowers (x * (t * x * t⁻¹)))
    (hOg : ∀ o ∈ O, g * o * g⁻¹ ∈ O) (hOT : ∀ o ∈ O, ∃ a ∈ X, ∃ b ∈ Xt, o = a * b)
    (hXt' : ∀ b ∈ Xt, ∃ c ∈ X, b = t * c * t⁻¹)
    (hgx : g * x = x * g) (hgXt : ∀ b ∈ Xt, g * b = b * g) (hgX : ∀ c ∈ X, g * c * g⁻¹ ∈ X)
    (hgsq : ∀ c ∈ X, g * g * c = c * g * g) (hgnt : ∃ c ∈ X, g * c ≠ c * g) :
    ∀ o ∈ O, o ∈ zpowers x ⊔ zpowers (t * x * t⁻¹) := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hfix : ∀ c ∈ X, g * c = c * g → c ∈ zpowers x := by
    let Fix : Subgroup G := X ⊓ centralizer ({g} : Set G)
    have hxF : x ∈ Fix := ⟨hxX, mem_centralizer_singleton_iff.2 hgx.symm⟩
    have hle : zpowers x ≤ Fix := (zpowers_le).2 hxF
    have hFX : Fix ≤ X := inf_le_left
    have hcz : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx3]
    have hdvd : Nat.card Fix ∣ 9 := hXcard ▸ Subgroup.card_dvd_of_le hFX
    have hge : 3 ≤ Nat.card Fix := hcz ▸ Subgroup.card_le_of_le hle
    have hne : Nat.card Fix ≠ 9 := by
      intro h9
      obtain ⟨c, hc, hgc⟩ := hgnt
      have : Fix = X := Subgroup.eq_of_le_of_card_ge hFX (by rw [h9, hXcard])
      have hcF : c ∈ Fix := this ▸ hc
      exact hgc (mem_centralizer_singleton_iff.1 hcF.2).symm
    have h3 : Nat.card Fix = 3 := by
      have hle9 : Nat.card Fix ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
      generalize Nat.card Fix = n at *
      interval_cases n <;> omega
    have heq : zpowers x = Fix := Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hcz])
    intro c hc hgc
    have : c ∈ Fix := ⟨hc, mem_centralizer_singleton_iff.2 hgc.symm⟩
    rw [← heq] at this
    exact this
  intro o ho
  obtain ⟨a, haX, b, hbXt, hoe⟩ := hOT o ho
  obtain ⟨c, hcX, hbc⟩ := hXt' b hbXt
  obtain ⟨k, hak⟩ := s11_split ht hxX hXt hcomm hinf hOinv ho haX hcX (hoe.trans (by rw [hbc]))
  obtain ⟨d, hd⟩ : ∃ d : G, d = g * c * g⁻¹ := ⟨_, rfl⟩
  have hdX : d ∈ X := hd ▸ hgX c hcX
  have hgxk : g * x ^ k * g⁻¹ = x ^ k := by
    have : Commute g (x ^ k) := (show Commute g x from hgx).zpow_right k
    rw [this.eq]; group
  have hgb : g * b * g⁻¹ = b := by rw [hgXt b hbXt]; group
  have ho' : o = c⁻¹ * x ^ k * b := by rw [hoe, hak]
  have hgo : g * o * g⁻¹ = d⁻¹ * x ^ k * b := by
    calc g * o * g⁻¹ = g * (c⁻¹ * x ^ k * b) * g⁻¹ := by rw [← ho']
      _ = (g * c * g⁻¹)⁻¹ * (g * x ^ k * g⁻¹) * (g * b * g⁻¹) := by group
      _ = d⁻¹ * x ^ k * b := by rw [hgxk, hgb, hd]
  have hq : (g * o * g⁻¹) * o⁻¹ = d⁻¹ * c := by
    calc (g * o * g⁻¹) * o⁻¹ = d⁻¹ * x ^ k * b * (c⁻¹ * x ^ k * b)⁻¹ := by rw [hgo, ← ho']
      _ = d⁻¹ * c := by group
  have hqO : d⁻¹ * c ∈ O := hq ▸ O.mul_mem (hOg o ho) (O.inv_mem ho)
  have hqX : d⁻¹ * c ∈ X := X.mul_mem (X.inv_mem hdX) hcX
  obtain ⟨m, hm⟩ := s11_split ht hxX hXt hcomm hinf hOinv hqO hqX (c := 1) (one_mem X)
    (by rw [mul_one, mul_inv_cancel, mul_one])
  have hgm : g * (d⁻¹ * c) * g⁻¹ = (d⁻¹ * c)⁻¹ := by
    have h1 : g * g * c * g⁻¹ * g⁻¹ = c := by
      rw [hgsq c hcX]; group
    calc g * (d⁻¹ * c) * g⁻¹ = (g * d * g⁻¹)⁻¹ * (g * c * g⁻¹) := by group
      _ = (g * (g * c * g⁻¹) * g⁻¹)⁻¹ * (g * c * g⁻¹) := by rw [← hd]
      _ = c⁻¹ * (g * c * g⁻¹) := by
          have : g * (g * c * g⁻¹) * g⁻¹ = c :=
            (show g * (g * c * g⁻¹) * g⁻¹ = g * g * c * g⁻¹ * g⁻¹ by group).trans h1
          rw [this]
      _ = (d⁻¹ * c)⁻¹ := by rw [← hd]; group
  have hxm : g * x ^ m * g⁻¹ = x ^ m := by
    have : Commute g (x ^ m) := (show Commute g x from hgx).zpow_right m
    rw [this.eq]; group
  rw [hm, inv_one, one_mul] at hgm
  rw [hm, inv_one, one_mul] at hqX
  have hinv : x ^ m = (x ^ m)⁻¹ := by rw [← hgm, hxm]
  have h2m : x ^ (2 * m) = 1 := by
    rw [two_mul, zpow_add]
    nth_rewrite 1 [hinv]
    exact inv_mul_cancel _
  have hm0 : x ^ m = 1 := s11_zpow_eq_one_of_two_mul hx3 h2m
  have hdc : d = c := by
    rw [hm0] at hm
    have : d⁻¹ * c = 1 := by rw [hm]; simp
    exact (inv_mul_eq_one.1 this)
  have hgc : g * c = c * g := by
    have : g * c * g⁻¹ = c := by rw [← hd, hdc]
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hcz : c ∈ zpowers x := hfix c hcX hgc
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hcz
  rw [ho', hbc, s11_conj_zpow]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · exact Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers x j))
  · exact Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers x k)
  · exact Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ j)

end Plane

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
