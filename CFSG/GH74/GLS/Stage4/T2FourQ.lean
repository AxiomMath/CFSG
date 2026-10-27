module

public import CFSG.GH74.GLS.Stage4.T2HCard
public import CFSG.GH74.GLS.Stage4.T2HZmod
public import CFSG.GH74.GLS.Stage4.T2Four

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

section Odd

variable {G : Type} [Group G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}

theorem T2Four.odd_part (h : T2Four z u K₁ K₂ H w₁ w₂) (hzK₁ : z ∈ K₁) (hzK₂ : z ∈ K₂) (k : ℕ)
    (hk : Odd k) (hcyc₁ : IsCyclic ↥(H ⊓ K₁)) (hcyc₂ : IsCyclic ↥(H ⊓ K₂))
    (hcard₁ : Nat.card ↥(H ⊓ K₁) = 2 * k) (hcard₂ : Nat.card ↥(H ⊓ K₂) = 2 * k)
    (hform : ∀ x ∈ H, x ∈ (H ⊓ K₁) ⊔ (H ⊓ K₂) ∨ ∃ y ∈ (H ⊓ K₁) ⊔ (H ⊓ K₂), x = y * u) :
    ∃ Q₁ Q₂ : Subgroup G, Q₁ ≤ H ⊓ K₁ ∧ Q₂ ≤ H ⊓ K₂ ∧ Nat.card ↥Q₁ = k ∧ Nat.card ↥Q₂ = k ∧
      (∀ x ∈ Q₁, x ^ k = 1) ∧ (∀ x ∈ Q₂, x ^ k = 1) ∧ Q₁ ⊓ Q₂ = ⊥ ∧
      (∀ x ∈ H, ∃ a ∈ t2U z u, ∃ b ∈ Q₁ ⊔ Q₂, x = a * b) := by
  obtain ⟨Q₁, hQ₁H, hQ₁c, hQ₁odd, hdec₁, hZQ₁⟩ :=
    t2H_cyclic_even_part (H ⊓ K₁) hcyc₁ k hk hcard₁ z ⟨h.z_mem_H, hzK₁⟩ h.zz h.z_ne
  obtain ⟨Q₂, hQ₂H, hQ₂c, hQ₂odd, hdec₂, hZQ₂⟩ :=
    t2H_cyclic_even_part (H ⊓ K₂) hcyc₂ k hk hcard₂ z ⟨h.z_mem_H, hzK₂⟩ h.zz h.z_ne
  have hpow : ∀ (Q : Subgroup G), Nat.card ↥Q = k → ∀ x ∈ Q, x ^ k = 1 := by
    intro Q hQ x hx
    have := pow_card_eq_one' (G := ↥Q) (x := (⟨x, hx⟩ : ↥Q))
    rw [hQ] at this
    exact congrArg Subtype.val this
  have hzU : Subgroup.zpowers z ≤ t2U z u :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  refine ⟨Q₁, Q₂, hQ₁H, hQ₂H, hQ₁c, hQ₂c, hpow Q₁ hQ₁c, hpow Q₂ hQ₂c, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro x ⟨hx₁, hx₂⟩
    have hxz : x ∈ Subgroup.zpowers z := h.K_inter ⟨(hQ₁H hx₁).2, (hQ₂H hx₂).2⟩
    have : x ∈ Subgroup.zpowers z ⊓ Q₁ := ⟨hxz, hx₁⟩
    rw [hZQ₁] at this
    exact this
  · intro x hx
    have hHc := h.H_comm
    have hcommHK : ∀ x ∈ H ⊓ K₁, ∀ y ∈ H ⊓ K₂, x * y = y * x := fun x hx y hy =>
      h.K_comm x hx.2 y hy.2
    have hcommQ : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := fun x hx y hy =>
      h.K_comm x (hQ₁H hx).2 y (hQ₂H hy).2
    have huU : u ∈ t2U z u := Subgroup.subset_closure (by simp)
    have hzH : Subgroup.zpowers z ≤ H := Subgroup.zpowers_le.2 h.z_mem_H
    have hpair : ∀ p ∈ (H ⊓ K₁) ⊔ (H ⊓ K₂), ∃ a ∈ Subgroup.zpowers z, ∃ b ∈ Q₁ ⊔ Q₂, p = a * b := by
      intro p hp
      obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := (mem_sup_iff_of_comm hcommHK p).1 hp
      obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hdec₁ h₁ hh₁
      obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hdec₂ h₂ hh₂
      refine ⟨a₁ * a₂, Subgroup.mul_mem _ ha₁ ha₂, b₁ * b₂,
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hb₁) (Subgroup.mem_sup_right hb₂), ?_⟩
      calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
        _ = a₁ * (a₂ * b₁) * b₂ := by rw [hHc b₁ (hQ₁H hb₁).1 a₂ (hzH ha₂)]
        _ = (a₁ * a₂) * (b₁ * b₂) := by group
    rcases hform x hx with hp | ⟨p, hp, rfl⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := hpair x hp
      exact ⟨a, hzU ha, b, hb, hab⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := hpair p hp
      have hbH : b ∈ H := by
        obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_sup_iff_of_comm hcommQ b).1 hb
        exact H.mul_mem (hQ₁H hb₁).1 (hQ₂H hb₂).1
      refine ⟨a * u, Subgroup.mul_mem _ (hzU ha) huU, b, hb, ?_⟩
      calc a * b * u = a * (b * u) := by group
        _ = a * (u * b) := by rw [hHc b hbH u h.u_mem_H]
        _ = a * u * b := by group

end Odd

section QProps

variable {G : Type} [Group G] {z u : G} {K₁ K₂ H Q₁ Q₂ : Subgroup G} {w₁ w₂ : G} {k : ℕ}

theorem t2Q_exp (hcomm : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x) (h1 : ∀ x ∈ Q₁, x ^ k = 1)
    (h2 : ∀ x ∈ Q₂, x ^ k = 1) : ∀ x ∈ Q₁ ⊔ Q₂, x ^ k = 1 := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcomm x).1 hx
  have hab : Commute a b := hcomm a ha b hb
  rw [hab.mul_pow, h1 a ha, h2 b hb, one_mul]

theorem t2_pow_odd_trivial (hk : Odd k) {x : G} (hk1 : x ^ k = 1) (hx2 : x * x = 1) : x = 1 := by
  obtain ⟨j, hj⟩ := hk
  have : x ^ k = x := by
    rw [hj, pow_succ, pow_mul, pow_two, hx2, one_pow, one_mul]
  rw [← this]; exact hk1

theorem t2U_inf_Q_eq_bot (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    {Q : Subgroup G} (hk : Odd k) (hQ : ∀ x ∈ Q, x ^ k = 1) : t2U z u ⊓ Q = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxU, hxQ⟩
  have hx2 : x * x = 1 := by
    rcases (t2U_mem hz2 hu2 hzu).1 hxU with rfl | rfl | rfl | rfl
    · simp
    · exact hz2
    · exact hu2
    · calc z * u * (z * u) = z * (u * z) * u := by group
        _ = z * (z * u) * u := by rw [← hzu]
        _ = (z * z) * (u * u) := by group
        _ = 1 := by rw [hz2, hu2, one_mul]
  exact (Subgroup.mem_bot).2 (t2_pow_odd_trivial hk (hQ x hxQ) hx2)

theorem t2Q_odd_mem (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) (hk : Odd k)
    {Q : Subgroup G} (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hQH : Q ≤ H)
    (hUH : t2U z u ≤ H) (hQ : ∀ x ∈ Q, x ^ k = 1)
    (hdec : ∀ x ∈ H, ∃ a ∈ t2U z u, ∃ b ∈ Q, x = a * b) {x : G} (hx : x ∈ H)
    (hodd : Odd (orderOf x)) : x ∈ Q := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
  have hab : Commute a b := hHc a (hUH ha) b (hQH hb)
  have ha2 : a * a = 1 := by
    rcases (t2U_mem hz2 hu2 hzu).1 ha with rfl | rfl | rfl | rfl
    · simp
    · exact hz2
    · exact hu2
    · calc z * u * (z * u) = z * (u * z) * u := by group
        _ = z * (z * u) * u := by rw [← hzu]
        _ = (z * z) * (u * u) := by group
        _ = 1 := by rw [hz2, hu2, one_mul]
  have hxk : (a * b) ^ k = a := by
    rw [hab.mul_pow, hQ b hb, mul_one]
    obtain ⟨j, hj⟩ := hk
    rw [hj, pow_succ, pow_mul, pow_two, ha2, one_pow, one_mul]
  have haodd : Odd (orderOf a) := by
    have : orderOf ((a * b) ^ k) ∣ orderOf (a * b) := orderOf_pow_dvd k
    rw [hxk] at this
    exact Odd.of_dvd_nat hodd this
  have ha1 : a = 1 := by
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha2)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact orderOf_eq_one_iff.1 h1
    · exact absurd haodd (by rw [h2]; decide)
  rw [ha1, one_mul]
  exact hb

theorem t2Q_normalized (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) (hk : Odd k)
    {Q : Subgroup G} (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hQH : Q ≤ H)
    (hUH : t2U z u ≤ H) (hQ : ∀ x ∈ Q, x ^ k = 1)
    (hdec : ∀ x ∈ H, ∃ a ∈ t2U z u, ∃ b ∈ Q, x = a * b) {g : G}
    (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
  intro q hq
  refine t2Q_odd_mem hz2 hu2 hzu hk hHc hQH hUH hQ hdec (hg q (hQH hq)) ?_
  have : orderOf (g * q * g⁻¹) = orderOf q := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective q
    simpa [MulAut.conj_apply] using this
  rw [this]
  exact Odd.of_dvd_nat hk (orderOf_dvd_of_pow_eq_one (hQ q hq))

end QProps

section Card

variable {G : Type} [Group G] {z u : G}

theorem t2U_card (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) (hz1 : z ≠ 1)
    (hu1 : u ≠ 1) (hzne : z ≠ u) : Nat.card ↥(t2U z u) = 4 := by
  classical
  have hzu1 : z * u ≠ 1 := by
    intro h1
    apply hzne
    have : z⁻¹ = u := inv_eq_of_mul_eq_one_right h1
    rw [← this, inv_eq_of_mul_eq_one_right hz2]
  have hzu2 : z * u ≠ z := by
    intro h1
    apply hu1
    have : z * u = z * 1 := by rw [h1, mul_one]
    exact mul_left_cancel this
  have hzu3 : z * u ≠ u := by
    intro h1
    apply hz1
    have : z * u = 1 * u := by rw [h1, one_mul]
    exact mul_right_cancel this
  have e : ((t2U z u : Subgroup G) : Set G) = ↑({1, z, u, z * u} : Finset G) := by
    ext x
    simp [SetLike.mem_coe, t2U_mem hz2 hu2 hzu]
  have h1 : Nat.card ↥(t2U z u) = Set.ncard ((t2U z u : Subgroup G) : Set G) :=
    Nat.card_coe_set_eq _
  rw [h1, e, Set.ncard_coe_finset]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  all_goals simp [hzne, hz1.symm, hu1.symm, hzu1.symm, hzu2.symm, hzu3.symm]

end Card

section Z10

variable {G : Type} [Group G] [Finite G] {z t : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}

omit [Finite G] in
theorem t2_zpow_pow_five {x : G} (hx : x * x = 1) (a : ℤ) : (x ^ a) ^ 5 = x ^ a := by
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  rcases Int.even_or_odd' a with ⟨s, hs | hs⟩
  · have : x ^ a = 1 := by rw [hs, zpow_mul, hx2, one_zpow]
    rw [this]; simp
  · have h1 : x ^ a = x := by
      rw [hs, zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one]
    rw [h1]
    have hx2' : x ^ 2 = 1 := by rw [pow_two]; exact hx
    calc x ^ 5 = (x ^ 2) ^ 2 * x := by rw [← pow_mul, ← pow_succ]
      _ = x := by rw [hx2']; simp

theorem T2Four.zmodProd_ten (h : T2Four z t K₁ K₂ H w₁ w₂) {Q₁ Q₂ : Subgroup G} (hQ₁H : Q₁ ≤ H)
    (hQ₂H : Q₂ ≤ H) (hQ₁c : Nat.card ↥Q₁ = 5) (hQ₂c : Nat.card ↥Q₂ = 5) (hQ₁₂ : Q₁ ⊓ Q₂ = ⊥)
    (hcard : Nat.card ↥H = 100) :
    Nonempty (↥H ≃* Multiplicative (ZMod 10) × Multiplicative (ZMod 10)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g₁, hg₁⟩ := (isCyclic_of_prime_card hQ₁c).exists_generator
  obtain ⟨g₂, hg₂⟩ := (isCyclic_of_prime_card hQ₂c).exists_generator
  set q₁ : G := (g₁ : G) with hq₁
  set q₂ : G := (g₂ : G) with hq₂
  have hq₁o : orderOf q₁ = 5 := by
    rw [hq₁, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg₁, hQ₁c]
  have hq₂o : orderOf q₂ = 5 := by
    rw [hq₂, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg₂, hQ₂c]
  have hq₁H : q₁ ∈ H := hQ₁H g₁.2
  have hq₂H : q₂ ∈ H := hQ₂H g₂.2
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.zz) h.z_ne
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.uu) h.u_ne
  have hHc := h.H_comm
  have hc₁ : Commute z q₁ := hHc z h.z_mem_H q₁ hq₁H
  have hc₂ : Commute t q₂ := hHc t h.u_mem_H q₂ hq₂H
  have ho₁ : orderOf (z * q₁) = 10 := by
    rw [hc₁.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hzo, hq₁o]; norm_num), hzo, hq₁o]
  have ho₂ : orderOf (t * q₂) = 10 := by
    rw [hc₂.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hto, hq₂o]; norm_num), hto, hq₂o]
  have he₁ : z * q₁ ∈ H := H.mul_mem h.z_mem_H hq₁H
  have he₂ : t * q₂ ∈ H := H.mul_mem h.u_mem_H hq₂H
  let _ : CommGroup ↥H :=
    { Subgroup.toGroup H with mul_comm := fun a b => Subtype.ext (hHc a a.2 b b.2) }
  refine t2H_zmodProd 10 (⟨z * q₁, he₁⟩ : ↥H) (⟨t * q₂, he₂⟩ : ↥H) ?_ ?_ ?_ ?_
  · rw [Subgroup.orderOf_mk]; exact ho₁
  · rw [Subgroup.orderOf_mk]; exact ho₂
  · intro x hx₁ hx₂
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hx₁
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.1 hx₂
    have hxa : (x : G) = (z * q₁) ^ a := by rw [← ha]; simp
    have hxb : (x : G) = (t * q₂) ^ b := by rw [← hb]; simp
    have hq₁a : (q₁ ^ a) ^ 5 = 1 := by
      have : (q₁ ^ a) ^ 5 = (q₁ ^ 5) ^ a := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      rw [this, ← hq₁o, pow_orderOf_eq_one, one_zpow]
    have hq₂b : (q₂ ^ b) ^ 5 = 1 := by
      have : (q₂ ^ b) ^ 5 = (q₂ ^ 5) ^ b := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      rw [this, ← hq₂o, pow_orderOf_eq_one, one_zpow]
    have h5a : (x : G) ^ 5 = z ^ a := by
      rw [hxa, hc₁.mul_zpow, ((hc₁.zpow_left a).zpow_right a).mul_pow, hq₁a, mul_one,
        t2_zpow_pow_five h.zz a]
    have h5b : (x : G) ^ 5 = t ^ b := by
      rw [hxb, hc₂.mul_zpow, ((hc₂.zpow_left b).zpow_right b).mul_pow, hq₂b, mul_one,
        t2_zpow_pow_five h.uu b]
    have hzt : z ^ a = t ^ b := h5a.symm.trans h5b
    have hza : z ^ a = 1 := by
      rcases t2C_zpowers_cases h.zz (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) a) with h1 | h1
      · exact h1
      · exfalso
        rcases t2C_zpowers_cases h.uu (Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) b) with h2 | h2
        · rw [h1, h2] at hzt; exact h.z_ne hzt
        · rw [h1, h2] at hzt; exact h.zu_ne hzt
    have htb : t ^ b = 1 := by rw [← hzt, hza]
    have hy₁ : (x : G) ∈ Q₁ := by
      rw [hxa, hc₁.mul_zpow, hza, one_mul]
      exact Subgroup.zpow_mem Q₁ g₁.2 a
    have hy₂ : (x : G) ∈ Q₂ := by
      rw [hxb, hc₂.mul_zpow, htb, one_mul]
      exact Subgroup.zpow_mem Q₂ g₂.2 b
    have hy : (x : G) ∈ Q₁ ⊓ Q₂ := ⟨hy₁, hy₂⟩
    rw [hQ₁₂] at hy
    exact Subtype.ext (Subgroup.mem_bot.1 hy)
  · exact hcard.trans (by norm_num)

end Z10

end CFSG.GH74.GLS.Stage4.Rest
