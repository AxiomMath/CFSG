module

public import CFSG.GH74.GLS.Stage4.T6RA
public import CFSG.GH74.GLS.Stage4.T6Avg
public import CFSG.GH74.GLS.Stage4.T2HCard

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem t6_pelt_K {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {r : G} (hrz : r * N.z = N.z * r)
    (hrodd : Odd (orderOf r)) {v : G} (hv : v ∈ N.S) (hvr : v * r * v⁻¹ = r⁻¹) :
    r ∈ N.K₁ ⊔ N.K₂ := by
  have hF := h.sec5.F5
  have hFz : ∀ f ∈ N.F, f * N.z = N.z * f := fun f hf => h.FS f hf _ h.sec5.loc.z_mem_S
  have hrC : r ∈ centralizer ({N.z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hrz
  have hFn := t2P53_F_normC₁ h.ctx hFz
  obtain ⟨c, hc, f, hf, hrcf⟩ := t2P53_split hFn (hF.C_le hrC)
  have hvC₁ : v ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := Subgroup.mem_sup_right hv
  have hfv : f * v = v * f := h.FS f hf v hv
  have hfv' : f * v⁻¹ = v⁻¹ * f := by
    calc f * v⁻¹ = v⁻¹ * (v * f) * v⁻¹ := by group
      _ = v⁻¹ * (f * v) * v⁻¹ := by rw [hfv]
      _ = v⁻¹ * f := by group
  have e1 : v * (c * f) * v⁻¹ = (v * c * v⁻¹) * f := by
    calc v * (c * f) * v⁻¹ = v * c * (f * v⁻¹) := by group
      _ = v * c * (v⁻¹ * f) := by rw [hfv']
      _ = (v * c * v⁻¹) * f := by group
  have e2 : (v * c * v⁻¹) * f = f⁻¹ * c⁻¹ := by
    rw [← e1, ← mul_inv_rev, ← hrcf]
    exact hvr
  have e3 : f⁻¹ = (v * c * v⁻¹) * f * c := by
    calc f⁻¹ = f⁻¹ * c⁻¹ * c := by group
      _ = (v * c * v⁻¹) * f * c := by rw [← e2]
  have hf2 : f * f ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := by
    have hcf : f * c * f⁻¹ ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := (Subgroup.mem_normalizer_iff.1 (hFn hf) c).1 hc
    have : f⁻¹ * f⁻¹ = (v * c * v⁻¹) * (f * c * f⁻¹) := by
      calc f⁻¹ * f⁻¹ = ((v * c * v⁻¹) * f * c) * f⁻¹ := by rw [← e3]
        _ = (v * c * v⁻¹) * (f * c * f⁻¹) := by group
    have hmem : f⁻¹ * f⁻¹ ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := by
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hvC₁ hc) (Subgroup.inv_mem _ hvC₁)) hcf
    have := Subgroup.inv_mem _ hmem
    simpa [mul_inv_rev] using this
  have hfodd : Odd (orderOf (f * f)) := by
    have : orderOf (f * f) ∣ orderOf f := by rw [← pow_two]; exact orderOf_pow_dvd 2
    exact Odd.of_dvd_nat (hF.F_odd f hf) this
  have hfK : f * f ∈ N.K₁ ⊔ N.K₂ := h.oddK _ hf2 hfodd
  have hbot : f * f ∈ N.F ⊓ (N.K₁ ⊔ N.K₂) := ⟨N.F.mul_mem hf hf, hfK⟩
  rw [hF.F_inter_K, Subgroup.mem_bot] at hbot
  have hf1 : f = 1 := t2P53_odd_sq (hF.F_odd f hf) hbot
  subst hf1
  rw [mul_one] at hrcf
  rw [hrcf] at hrodd ⊢
  exact h.oddK c hc hrodd

theorem a_conj_facts {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) :
    N.a * u * N.a⁻¹ = N.z ∧ N.a * N.z * N.a⁻¹ = N.z * u := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  have hu : N.a⁻¹ * N.z * N.a = u := h.sec5.u_eq
  have hcyc : N.a⁻¹ * u * N.a = N.z * u := by
    have := h.sec5.weyl.a_cycle
    rwa [show N.u = u from h.sec5.u_eq] at this
  have h1 : N.a * u * N.a⁻¹ = N.z := by
    calc N.a * u * N.a⁻¹ = N.a * (N.a⁻¹ * N.z * N.a) * N.a⁻¹ := by rw [hu]
      _ = N.z := by group
  refine ⟨h1, ?_⟩
  have h2 : N.a * (N.z * u) * N.a⁻¹ = u := by
    rw [← hcyc]; group
  have h3 : (N.a * N.z * N.a⁻¹) * N.z = u := by
    calc (N.a * N.z * N.a⁻¹) * N.z = (N.a * N.z * N.a⁻¹) * (N.a * u * N.a⁻¹) := by rw [h1]
      _ = N.a * (N.z * u) * N.a⁻¹ := by group
      _ = u := h2
  have hz : N.z⁻¹ = N.z := inv_eq_of_mul_eq_one_right hz2
  calc N.a * N.z * N.a⁻¹ = ((N.a * N.z * N.a⁻¹) * N.z) * N.z⁻¹ := by group
    _ = u * N.z⁻¹ := by rw [h3]
    _ = u * N.z := by rw [hz]
    _ = N.z * u := hzu.symm

theorem RA_conj_K {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {r : G} (hr : r ∈ RA N p u) :
    N.a * r * N.a⁻¹ ∈ N.K₁ ⊔ N.K₂ := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  obtain ⟨ha1, ha2⟩ := a_conj_facts h
  have hru : r * u = u * r := Subgroup.mem_centralizer_singleton_iff.1 hr.2
  have hpg := R₂_pGroup N h.prime
  have hrz := (RA_inv h).1 r hr
  have hodd : Odd (orderOf (N.a * r * N.a⁻¹)) := by
    have : orderOf (N.a * r * N.a⁻¹) = orderOf r := by
      have := MulEquiv.orderOf_eq (MulAut.conj N.a) r
      simpa [MulAut.conj_apply] using this
    rw [this]
    exact t6_odd_of_pGroup h.prime h.p_ne_two hpg hr.1
  refine t6_pelt_K h ?_ hodd (v := N.z * u)
    (N.S.mul_mem h.sec5.loc.z_mem_S h.sec5.loc.u_mem_S) ?_
  ·
    calc N.a * r * N.a⁻¹ * N.z = N.a * r * N.a⁻¹ * (N.a * u * N.a⁻¹) := by rw [ha1]
      _ = N.a * (r * u) * N.a⁻¹ := by group
      _ = N.a * (u * r) * N.a⁻¹ := by rw [hru]
      _ = (N.a * u * N.a⁻¹) * (N.a * r * N.a⁻¹) := by group
      _ = N.z * (N.a * r * N.a⁻¹) := by rw [ha1]
  ·
    rw [← ha2]
    calc N.a * N.z * N.a⁻¹ * (N.a * r * N.a⁻¹) * (N.a * N.z * N.a⁻¹)⁻¹
        = N.a * (N.z * r * N.z⁻¹) * N.a⁻¹ := by group
      _ = N.a * r⁻¹ * N.a⁻¹ := by rw [hrz]
      _ = (N.a * r * N.a⁻¹)⁻¹ := by group

theorem t6_mem_of_pow {p : ℕ} {c : G} {L : Subgroup G} {n : ℕ}
    (hord : ∃ j : ℕ, orderOf c = p ^ j) (hn : Nat.Coprime p n) (hcn : c ^ n ∈ L) : c ∈ L := by
  obtain ⟨j, hj⟩ := hord
  have hcop : (orderOf c).Coprime n := by rw [hj]; exact Nat.Coprime.pow_left j hn
  have hord' : orderOf (c ^ n) = orderOf c := Nat.Coprime.orderOf_pow hcop
  have hle : Subgroup.zpowers (c ^ n) ≤ Subgroup.zpowers c := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) n
  have heq : Subgroup.zpowers (c ^ n) = Subgroup.zpowers c := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, Nat.card_zpowers, hord']
  have : c ∈ Subgroup.zpowers (c ^ n) := by rw [heq]; exact Subgroup.mem_zpowers c
  exact (Subgroup.zpowers_le.2 hcn) this

theorem t6_hinv {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {A : Subgroup G}
    (hAK : A ≤ N.K₁ ⊔ N.K₂) (hAp : IsPGroup p ↥A) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAH : ∀ x ∈ N.H, ∀ y ∈ A, x * y * x⁻¹ ∈ A) :
    ∃ A₁ A₂ : Subgroup G, A₁ ≤ N.K₁ ∧ A₂ ≤ N.K₂ ∧ A = A₁ ⊔ A₂ ∧
      Nat.card ↥A = Nat.card ↥A₁ * Nat.card ↥A₂ ∧ (Nat.card ↥A₁ = 1 ∨ Nat.card ↥A₁ = N.q₁) ∧
      (Nat.card ↥A₂ = 1 ∨ Nat.card ↥A₂ = N.q₂) ∧ (∀ x ∈ A₁, x ^ p = 1) ∧ (∀ x ∈ A₂, x ^ p = 1) := by
  have hloc := h.sec5.loc
  obtain ⟨F₁, iF₁, fF₁, φ₁, hcard₁, hinj₁, hrange₁, hz₁, hX₁, hX₁', hw₁, hHK₁⟩ := h.coord.coord₁
  obtain ⟨F₂, iF₂, fF₂, φ₂, hcard₂, hinj₂, hrange₂, hz₂, hX₂, hX₂', hw₂, hHK₂⟩ := h.coord.coord₂
  obtain ⟨m, hm⟩ := h.q₁_pow
  obtain ⟨n, hn⟩ := h.q₂_pow
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have := hloc.q₁_ge; rw [hm, h0] at this; simp at this
    · exact h0
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have := hloc.q₂_ge; rw [hn, h0] at this; simp at this
    · exact h0
  set A₁ : Subgroup G := A ⊓ N.K₁ with hA₁
  set A₂ : Subgroup G := A ⊓ N.K₂ with hA₂
  have hK₁r : N.K₁ ≤ φ₁.range := hrange₁ ▸ le_rfl
  have hK₂r : N.K₂ ≤ φ₂.range := hrange₂ ▸ le_rfl
  have hA₁c : (Nat.card ↥A₁ = 1 ∨ Nat.card ↥A₁ = N.q₁) ∧ ∀ x ∈ A₁, x ^ p = 1 := by
    have := t6_pSub_card hinj₁ h.prime (hcard₁.trans hm) hm1 (by rw [hcard₁]; exact hloc.q₁_odd)
      (B := A₁) (inf_le_right.trans hK₁r) (hAp.to_le inf_le_left) (fun t ht b hb => by
        have hφt : φ₁ t ∈ N.H ⊓ N.K₁ := by rw [hHK₁]; exact Subgroup.mem_map_of_mem φ₁ ht
        exact ⟨hAH _ hφt.1 b hb.1, N.K₁.mul_mem (N.K₁.mul_mem hφt.2 hb.2) (N.K₁.inv_mem hφt.2)⟩)
    rwa [← hm] at this
  have hA₂c : (Nat.card ↥A₂ = 1 ∨ Nat.card ↥A₂ = N.q₂) ∧ ∀ x ∈ A₂, x ^ p = 1 := by
    have := t6_pSub_card hinj₂ h.prime (hcard₂.trans hn) hn1 (by rw [hcard₂]; exact hloc.q₂_odd)
      (B := A₂) (inf_le_right.trans hK₂r) (hAp.to_le inf_le_left) (fun t ht b hb => by
        have hφt : φ₂ t ∈ N.H ⊓ N.K₂ := by rw [hHK₂]; exact Subgroup.mem_map_of_mem φ₂ ht
        exact ⟨hAH _ hφt.1 b hb.1, N.K₂.mul_mem (N.K₂.mul_mem hφt.2 hb.2) (N.K₂.inv_mem hφt.2)⟩)
    rwa [← hn] at this
  have hH₁A : ∀ x ∈ N.H ⊓ N.K₁, ∀ y ∈ A, x * y * x⁻¹ ∈ A := fun x hx y hy => hAH x hx.1 y hy
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥(N.H ⊓ N.K₁)) := by
    have : Fact p.Prime := ⟨h.prime⟩
    obtain ⟨k, hk⟩ := hAp.exists_card_eq
    rw [hk, hloc.card_H_K₁, hm]
    have hnd : ¬ p ∣ p ^ m - 1 := by
      intro hd
      have h1 : p ∣ p ^ m := dvd_pow_self p (by omega)
      have h2 : p ∣ p ^ m - (p ^ m - 1) := Nat.dvd_sub h1 hd
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ h.prime.pos)] at h2
      exact h.prime.one_lt.ne' (Nat.dvd_one.1 h2)
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd h.prime).2 hnd)
  have hAeq : A = A₁ ⊔ A₂ := by
    apply le_antisymm
    · intro a ha
      obtain ⟨c, hc, d, hd, hcd, hacd⟩ := t6_avg hAab hH₁A hcop a ha
      have hdA₁ : d ∈ A₁ := by
        refine (Subgroup.closure_le A₁).2 ?_ hd
        rintro y ⟨x, hx, b, hb, rfl⟩
        refine ⟨A.mul_mem (hAH x hx.1 b hb) (A.inv_mem hb), ?_⟩
        obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_sup_iff_of_comm hloc.K_comm b).1 (hAK hb)
        have hxk₂ : x * k₂ = k₂ * x := hloc.K_comm x hx.2 k₂ hk₂
        have hxk₂' : k₂ * x⁻¹ = x⁻¹ * k₂ := by
          calc k₂ * x⁻¹ = x⁻¹ * (x * k₂) * x⁻¹ := by group
            _ = x⁻¹ * (k₂ * x) * x⁻¹ := by rw [hxk₂]
            _ = x⁻¹ * k₂ := by group
        have e : x * (k₁ * k₂) * x⁻¹ * (k₁ * k₂)⁻¹ = x * k₁ * x⁻¹ * k₁⁻¹ := by
          calc x * (k₁ * k₂) * x⁻¹ * (k₁ * k₂)⁻¹ = x * k₁ * (k₂ * x⁻¹) * k₂⁻¹ * k₁⁻¹ := by group
            _ = x * k₁ * (x⁻¹ * k₂) * k₂⁻¹ * k₁⁻¹ := by rw [hxk₂']
            _ = x * k₁ * x⁻¹ * k₁⁻¹ := by group
        rw [e]
        exact N.K₁.mul_mem (N.K₁.mul_mem (N.K₁.mul_mem hx.2 hk₁) (N.K₁.inv_mem hx.2)) (N.K₁.inv_mem hk₁)
      have hcK₂ : c ∈ N.K₂ := by
        obtain ⟨k₁, hk₁, k₂, hk₂, hck⟩ := (mem_sup_iff_of_comm hloc.K_comm c).1 (hAK hc)
        have hk₁c : ∀ t ∈ tSub F₁, k₁ * φ₁ t = φ₁ t * k₁ := by
          intro t ht
          have hφt : φ₁ t ∈ N.H ⊓ N.K₁ := by rw [hHK₁]; exact Subgroup.mem_map_of_mem φ₁ ht
          have h1 := hcd _ hφt
          have h2 : φ₁ t * k₂ = k₂ * φ₁ t := hloc.K_comm _ hφt.2 k₂ hk₂
          rw [hck] at h1
          have h3 : φ₁ t * (k₁ * k₂) * (φ₁ t)⁻¹ = (φ₁ t * k₁ * (φ₁ t)⁻¹) * k₂ := by
            calc φ₁ t * (k₁ * k₂) * (φ₁ t)⁻¹ = φ₁ t * k₁ * (k₂ * (φ₁ t)⁻¹) := by group
              _ = φ₁ t * k₁ * ((φ₁ t)⁻¹ * k₂) := by
                congr 1
                calc k₂ * (φ₁ t)⁻¹ = (φ₁ t)⁻¹ * (φ₁ t * k₂) * (φ₁ t)⁻¹ := by group
                  _ = (φ₁ t)⁻¹ * (k₂ * φ₁ t) * (φ₁ t)⁻¹ := by rw [h2]
                  _ = (φ₁ t)⁻¹ * k₂ := by group
              _ = (φ₁ t * k₁ * (φ₁ t)⁻¹) * k₂ := by group
          rw [h3] at h1
          have h4 : φ₁ t * k₁ * (φ₁ t)⁻¹ = k₁ := mul_right_cancel h1
          calc k₁ * φ₁ t = (φ₁ t * k₁ * (φ₁ t)⁻¹) * φ₁ t := by rw [h4]
            _ = φ₁ t * k₁ := by group
        have hk₁H : k₁ ∈ N.H ⊓ N.K₁ := by
          rw [hHK₁]
          exact t6_cent_torus hinj₁ (by rw [hcard₁, hm]; have := hloc.q₁_ge; rw [hm] at this; exact this)
            (hrange₁ ▸ hk₁) hk₁c
        set nH := Nat.card ↥(N.H ⊓ N.K₁) with hnH
        have hk₁n : k₁ ^ nH = 1 := by
          have := pow_card_eq_one' (G := ↥(N.H ⊓ N.K₁)) (x := ⟨k₁, hk₁H⟩)
          simpa [hnH] using congrArg Subtype.val this
        have hcn : c ^ nH ∈ N.K₂ := by
          have hcomm : Commute k₁ k₂ := hloc.K_comm k₁ hk₁ k₂ hk₂
          rw [hck, hcomm.mul_pow, hk₁n, one_mul]
          exact Subgroup.pow_mem _ hk₂ _
        have hcop' : Nat.Coprime p nH := by
          rw [hnH, hloc.card_H_K₁, hm]
          have hnd : ¬ p ∣ p ^ m - 1 := by
            intro hd
            have h1 : p ∣ p ^ m := dvd_pow_self p (by omega)
            have h2 : p ∣ p ^ m - (p ^ m - 1) := Nat.dvd_sub h1 hd
            rw [Nat.sub_sub_self (Nat.one_le_pow _ _ h.prime.pos)] at h2
            exact h.prime.one_lt.ne' (Nat.dvd_one.1 h2)
          exact (Nat.Prime.coprime_iff_not_dvd h.prime).2 hnd
        have : Fact p.Prime := ⟨h.prime⟩
        have hord : ∃ j : ℕ, orderOf c = p ^ j := by
          obtain ⟨j, hj⟩ := hAp ⟨c, hc⟩
          have hj' : c ^ (p ^ j) = 1 := by simpa using congrArg Subtype.val hj
          obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow h.prime).1 (orderOf_dvd_of_pow_eq_one hj')
          exact ⟨i, hi⟩
        exact t6_mem_of_pow hord hcop' hcn
      rw [hacd]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (⟨hc, hcK₂⟩ : c ∈ A₂))
        (Subgroup.mem_sup_left hdA₁)
    · exact sup_le inf_le_left inf_le_left
  have hA₁A₂ : A₁ ⊓ A₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases t2C_zpowers_cases h.ctx.zz (hloc.K_inter ⟨hx.1.2, hx.2.2⟩) with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hx.1.1) (z_not_mem_pGroup h hAp)
  have hcard : Nat.card ↥A = Nat.card ↥A₁ * Nat.card ↥A₂ := by
    conv_lhs => rw [hAeq]
    exact t2H_card_sup_comm_disjoint A₁ A₂ (fun x hx y hy => hloc.K_comm x hx.2 y hy.2) hA₁A₂
  exact ⟨A₁, A₂, inf_le_right, inf_le_right, hAeq, hcard, hA₁c.1, hA₂c.1, hA₁c.2, hA₂c.2⟩

end CFSG.GH74.GLS.Stage4.Rest.T6
