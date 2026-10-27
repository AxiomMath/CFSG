module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Pair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private lemma s888_conj_eq_of_comm {a x : G} (h : a * x = x * a) : x * a * x⁻¹ = a := by
  rw [h.symm, mul_assoc, mul_inv_cancel, mul_one]

private lemma s888_conj_mul_eq {a m : G} (h : Commute a m) : a * m * a⁻¹ = m := by
  rw [h.eq, mul_assoc, mul_inv_cancel, mul_one]

private lemma s888_comm_of_commutator {a x : G} (h : a * x * a⁻¹ * x⁻¹ = 1) :
    a * x = x * a := by
  have h1 : a * x * a⁻¹ = x := mul_inv_eq_one.mp h
  have h2 := congrArg (· * a) h1
  simpa [mul_assoc] using h2

private lemma s888_commutator_eq {a b q : G} (hbq : b * q = q * b) :
    a * b * q * (a * b)⁻¹ * q⁻¹ = a * q * a⁻¹ * q⁻¹ := by
  rw [mul_inv_rev]
  calc a * b * q * (b⁻¹ * a⁻¹) * q⁻¹
      = a * (b * q * b⁻¹) * a⁻¹ * q⁻¹ := by group
    _ = a * q * a⁻¹ * q⁻¹ := by rw [s888_conj_eq_of_comm hbq.symm]

private lemma s888_commutator_eq_right {a b q : G} (hab : a * b = b * a) (haq : a * q = q * a) :
    a * b * q * (a * b)⁻¹ * q⁻¹ = b * q * b⁻¹ * q⁻¹ := by
  have habc : Commute a b := hab
  have haqc : Commute a q := haq
  have hN : Commute a (b * q * b⁻¹ * q⁻¹) :=
    ((habc.mul_right haqc).mul_right habc.inv_right).mul_right haqc.inv_right
  rw [mul_inv_rev]
  rw [show a * b * q * (b⁻¹ * a⁻¹) * q⁻¹ = a * (b * q * b⁻¹) * (a⁻¹ * q⁻¹) by group]
  rw [show a⁻¹ * q⁻¹ = q⁻¹ * a⁻¹ from haqc.inv_inv.eq]
  rw [show a * (b * q * b⁻¹) * (q⁻¹ * a⁻¹) = a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ by group]
  rw [s888_conj_mul_eq hN]

private lemma s888_sl23_central_q8 (a : SL23)
    (h : ∀ q : SL23, q ^ 4 = 1 → a * q = q * a) : a = 1 ∨ a = -1 := by
  revert a
  decide +kernel

private lemma s888_comm_q8 {K : Subgroup G} (e : ↥K ≃* SL23) {z u : G} (hz : z ∈ K)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hu : u ∈ K)
    (h : ∀ v ∈ K, v ^ 4 = 1 → u * v = v * u) : u = 1 ∨ u = z := by
  have hζ : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext (by simpa using hz2)
  have hζ1 : e ⟨z, hz⟩ ≠ 1 := by
    intro hc
    have hsub : (⟨z, hz⟩ : ↥K) = 1 := e.injective (by rw [hc]; exact (map_one e).symm)
    exact hz1 (congrArg Subtype.val hsub)
  have h' : ∀ q : SL23, q ^ 4 = 1 → e ⟨u, hu⟩ * q = q * e ⟨u, hu⟩ := by
    intro q hq
    obtain ⟨c, rfl⟩ := e.surjective q
    have hc4 : c.1 ^ 4 = 1 := by
      have hc4' : (c : ↥K) ^ 4 = 1 := e.injective (by rw [map_pow, hq, map_one])
      exact congrArg Subtype.val hc4'
    have hh : u * c.1 = c.1 * u := h c.1 c.2 hc4
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hh
  rcases s888_sl23_central_q8 (e ⟨u, hu⟩) h' with h1 | h1
  · left
    have hsub : (⟨u, hu⟩ : ↥K) = 1 := e.injective (by rw [h1]; exact (map_one e).symm)
    exact congrArg Subtype.val hsub
  · right
    have hzneg : e ⟨z, hz⟩ = -1 := (sl23_unique_involution _ hζ).resolve_left hζ1
    have hzu : e ⟨u, hu⟩ = e ⟨z, hz⟩ := by
      calc e ⟨u, hu⟩ = -1 := h1
        _ = e ⟨z, hz⟩ := hzneg.symm
    exact congrArg Subtype.val (e.injective hzu)

private lemma s888_commutator_pow4 {K : Subgroup G} (e : ↥K ≃* SL23) {x y : G}
    (hx : x ∈ K) (hy : y ∈ K) (hy4 : y ^ 4 = 1) :
    (x * y * x⁻¹ * y⁻¹) ^ 4 = 1 := by
  have hk : x * y * x⁻¹ ∈ K := K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)
  have hk4 : (x * y * x⁻¹) ^ 4 = 1 := by
    rw [conj_pow, hy4]
    group
  have hyi4 : (y⁻¹) ^ 4 = 1 := by rw [inv_pow, hy4, inv_one]
  exact sec5b517_pow4_mul e hk (K.inv_mem hy) hk4 hyi4

private lemma s888_odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem s888_card_sup_mul_card_inf [Finite G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  let f : ↥H × ↥K →* ↥(H ⊔ K) :=
    { toFun := fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro p q
        apply Subtype.ext
        calc ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G))
            = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
                rw [hc q.1 q.1.2 p.2 p.2.2]
          _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by group }
  have hker : Nat.card f.ker = Nat.card ↥(H ⊓ K) := by
    let e : ↥f.ker ≃ ↥(H ⊓ K) :=
      { toFun := fun x =>
          ⟨(x.1.1 : G), x.1.1.2, by
            have hx : (x.1.1 : G) * (x.1.2 : G) = 1 := by
              have := congrArg (fun y : ↥(H ⊔ K) => (y : G)) x.2
              simpa [f] using this
            exact (eq_inv_of_mul_eq_one_left hx) ▸ K.inv_mem x.1.2.2⟩
        invFun := fun a =>
          ⟨(⟨a.1, a.2.1⟩, ⟨a.1⁻¹, K.inv_mem a.2.2⟩), by
            apply Subtype.ext
            simp [f]⟩
        left_inv := fun x => by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            have hx : (x.1.1 : G) * (x.1.2 : G) = 1 := by
              have := congrArg (fun y : ↥(H ⊔ K) => (y : G)) x.2
              simpa [f] using this
            exact (eq_inv_of_mul_eq_one_right hx).symm
        right_inv := fun a => by
          apply Subtype.ext
          rfl }
    exact Nat.card_congr e
  have hrange : f.range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨h, hh, k, hk, hkx⟩ := sec5b_mem_sup_of_comm hc x.2
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hkx.symm⟩
  have hquot : Nat.card ((↥H × ↥K) ⧸ f.ker) = Nat.card ↥(H ⊔ K) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).trans
      (by rw [hrange, Subgroup.card_top])
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_prod, hquot, hker] at hcard
  exact hcard.symm

theorem Sec5Pair.two_elt {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z) {x : G}
    (hx : x ∈ K₁ ⊔ K₂) (hx4 : x ^ 4 = 1) :
    ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b ∧ a ^ 4 = 1 ∧ b ^ 4 = 1 := by
  obtain ⟨a, ha, b, hb, hxab⟩ := sec5b_mem_sup_of_comm h.comm hx
  have hab : Commute a b := h.comm a ha b hb
  have hp : a ^ 4 * b ^ 4 = 1 := by
    have h1 : (a * b) ^ 4 = 1 := by rw [← hxab]; exact hx4
    rw [hab.mul_pow 4] at h1
    exact h1
  have ha4_mem : a ^ 4 ∈ K₂ := by
    have h1 : a ^ 4 = (b ^ 4)⁻¹ := eq_inv_of_mul_eq_one_left hp
    rw [h1]
    exact K₂.inv_mem (K₂.pow_mem hb 4)
  have ha4 : a ^ 4 = 1 ∨ a ^ 4 = z := h.inf_eq (K₁.pow_mem ha 4) ha4_mem
  have ha8 : a ^ 8 = 1 := by
    rcases ha4 with h1 | hz
    · rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add, h1, one_mul]
    · rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add, hz, h.z_sq]
  have ha4_one : a ^ 4 = 1 :=
    sec5b517_pow4 (Classical.choice h.iso₁) ha (m := 3) (by simpa using ha8)
  have hb4_one : b ^ 4 = 1 := by
    rw [ha4_one, one_mul] at hp
    exact hp
  exact ⟨a, ha, b, hb, hxab, ha4_one, hb4_one⟩

theorem Sec5Pair.odd_elt {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z) {a b : G}
    (ha : a ∈ K₁) (hb : b ∈ K₂) (hb4 : b ^ 4 = 1) (hodd : Odd (orderOf (a * b))) :
    b = 1 ∨ b = z := by
  set m := orderOf (a * b) with hm
  have hoddm : Odd m := by rw [hm]; exact hodd
  have hm_pow : (a * b) ^ m = 1 := by rw [hm]; exact pow_orderOf_eq_one _
  have habc : Commute a b := h.comm a ha b hb
  have hab_comm : (a * b) ^ m = a ^ m * b ^ m := habc.mul_pow m
  have hbm_eq : b ^ m = (a ^ m)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← hab_comm]; exact hm_pow)
  have hbm_mem1 : b ^ m ∈ K₁ := by
    rw [hbm_eq]
    exact K₁.inv_mem (K₁.pow_mem ha m)
  have hbm : b ^ m = 1 ∨ b ^ m = z := h.inf_eq hbm_mem1 (K₂.pow_mem hb m)
  have hb2m : b ^ (2 * m) = 1 := by
    rw [show (2 : ℕ) * m = m + m from by ring, pow_add]
    rcases hbm with h1 | hz
    · rw [h1, one_mul]
    · rw [hz, h.z_sq]
  have hb2 : b ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := hoddm
    have h2m : b ^ (2 * m) = (b ^ 4) ^ k * b ^ 2 := by
      rw [hk]
      rw [show 2 * (2 * k + 1) = 4 * k + 2 from by ring, pow_add, pow_mul]
    rw [h2m, hb4, one_pow, one_mul] at hb2m
    exact hb2m
  exact sec5b517_sq (Classical.choice h.iso₂) h.z_mem₂ h.z_sq h.z_ne hb
    (by simpa [pow_two] using hb2)

theorem Sec5Pair.card_sup [Finite G] {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z) :
    Nat.card ↥(K₁ ⊔ K₂) = 288 := by
  obtain ⟨e₁⟩ := h.iso₁
  obtain ⟨e₂⟩ := h.iso₂
  have hcard1 : Nat.card ↥K₁ = 24 := by
    rw [Nat.card_congr e₁.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hcard2 : Nat.card ↥K₂ = 24 := by
    rw [Nat.card_congr e₂.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hinf : K₁ ⊓ K₂ = zpowers z := by
    apply le_antisymm
    · intro u hu
      rcases h.inf_eq hu.1 hu.2 with h1 | hz
      · rw [h1]; exact Subgroup.one_mem _
      · rw [hz]; exact Subgroup.mem_zpowers z
    · exact Subgroup.zpowers_le.mpr ⟨h.z_mem₁, h.z_mem₂⟩
  have hcardinf : Nat.card ↥(K₁ ⊓ K₂) = 2 := by
    rw [hinf, Nat.card_zpowers]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by simpa [pow_two] using h.z_sq) h.z_ne
  have hcard := s888_card_sup_mul_card_inf h.comm
  rw [hcard1, hcard2, hcardinf] at hcard
  omega

theorem Sec5Pair.oddCore_bot [Finite G] {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z) :
    CFSG.oddCore ↥(K₁ ⊔ K₂) = ⊥ := by
  let M : Subgroup G := K₁ ⊔ K₂
  let R : Subgroup ↥M := CFSG.oddCore ↥M
  have hRodd : Odd (Nat.card R) := s888_odd_card_oddCore ↥M
  have hRnorm : R.Normal := CFSG.oddCore_normal (G := ↥M)
  have hbot : R = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro r hr
    obtain ⟨a, ha, b, hb, hr_eq⟩ := sec5b_mem_sup_of_comm h.comm (x := (r : G)) r.2
    have ha_comm : ∀ v ∈ K₁, v ^ 4 = 1 → a * v = v * a := by
      intro v hv hv4
      let vM : ↥M := ⟨v, Subgroup.mem_sup_left hv⟩
      let c : ↥M := r * vM * r⁻¹ * vM⁻¹
      have hcR : c ∈ R := by
        have h1 : vM * r⁻¹ * vM⁻¹ ∈ R := hRnorm.conj_mem r⁻¹ (R.inv_mem hr) vM
        have h2 : r * (vM * r⁻¹ * vM⁻¹) ∈ R := R.mul_mem hr h1
        simpa only [c, mul_assoc] using h2
      have hcG : (c : G) = a * v * a⁻¹ * v⁻¹ := by
        have hcast : (c : G) = (r : G) * vM * (r : G)⁻¹ * vM⁻¹ := rfl
        rw [hcast, hr_eq]
        change a * b * v * (a * b)⁻¹ * v⁻¹ = a * v * a⁻¹ * v⁻¹
        exact s888_commutator_eq (a := a) (b := b) (q := v) ((h.comm v hv b hb).symm)
      have hc4 : c ^ 4 = 1 := by
        have h4 : ((c : ↥M) : G) ^ 4 = 1 := by
          rw [hcG]
          exact s888_commutator_pow4 (Classical.choice h.iso₁) ha hv hv4
        apply Subtype.ext
        simpa using h4
      have hdvd4 : orderOf c ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hc4
      have hcodd : Odd (orderOf c) :=
        Odd.of_dvd_nat hRodd (Subgroup.orderOf_dvd_natCard R hcR)
      have hcop : Nat.Coprime (orderOf c) 2 := Nat.coprime_two_right.mpr hcodd
      have h1dvd : orderOf c ∣ 1 := by
        have h4' : orderOf c ∣ 2 * 2 := by simpa using hdvd4
        have h2' : orderOf c ∣ 2 := (hcop.dvd_mul_right (m := 2) (n := 2)).mp h4'
        exact (hcop.dvd_mul_right (m := 1) (n := 2)).mp (by simpa using h2')
      have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1dvd)
      have hv1 : a * v * a⁻¹ * v⁻¹ = 1 := by
        have h1 : (c : G) = 1 := by rw [hc1]; rfl
        rw [hcG] at h1
        exact h1
      exact s888_comm_of_commutator hv1
    have ha_res : a = 1 ∨ a = z :=
      s888_comm_q8 (Classical.choice h.iso₁) h.z_mem₁ h.z_sq h.z_ne ha ha_comm
    have hb_comm : ∀ v ∈ K₂, v ^ 4 = 1 → b * v = v * b := by
      intro v hv hv4
      let vM : ↥M := ⟨v, Subgroup.mem_sup_right hv⟩
      let c : ↥M := r * vM * r⁻¹ * vM⁻¹
      have hcR : c ∈ R := by
        have h1 : vM * r⁻¹ * vM⁻¹ ∈ R := hRnorm.conj_mem r⁻¹ (R.inv_mem hr) vM
        have h2 : r * (vM * r⁻¹ * vM⁻¹) ∈ R := R.mul_mem hr h1
        simpa only [c, mul_assoc] using h2
      have hcG : (c : G) = b * v * b⁻¹ * v⁻¹ := by
        have hcast : (c : G) = (r : G) * vM * (r : G)⁻¹ * vM⁻¹ := rfl
        rw [hcast, hr_eq]
        change a * b * v * (a * b)⁻¹ * v⁻¹ = b * v * b⁻¹ * v⁻¹
        exact s888_commutator_eq_right (a := a) (b := b) (q := v)
          (h.comm a ha b hb) (h.comm a ha v hv)
      have hc4 : c ^ 4 = 1 := by
        have h4 : ((c : ↥M) : G) ^ 4 = 1 := by
          rw [hcG]
          exact s888_commutator_pow4 (Classical.choice h.iso₂) hb hv hv4
        apply Subtype.ext
        simpa using h4
      have hdvd4 : orderOf c ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hc4
      have hcodd : Odd (orderOf c) :=
        Odd.of_dvd_nat hRodd (Subgroup.orderOf_dvd_natCard R hcR)
      have hcop : Nat.Coprime (orderOf c) 2 := Nat.coprime_two_right.mpr hcodd
      have h1dvd : orderOf c ∣ 1 := by
        have h4' : orderOf c ∣ 2 * 2 := by simpa using hdvd4
        have h2' : orderOf c ∣ 2 := (hcop.dvd_mul_right (m := 2) (n := 2)).mp h4'
        exact (hcop.dvd_mul_right (m := 1) (n := 2)).mp (by simpa using h2')
      have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1dvd)
      have hv1 : b * v * b⁻¹ * v⁻¹ = 1 := by
        have h1 : (c : G) = 1 := by rw [hc1]; rfl
        rw [hcG] at h1
        exact h1
      exact s888_comm_of_commutator hv1
    have hb_res : b = 1 ∨ b = z :=
      s888_comm_q8 (Classical.choice h.iso₂) h.z_mem₂ h.z_sq h.z_ne hb hb_comm
    have hrG : (r : G) = 1 ∨ (r : G) = z := by
      rcases ha_res with ha1 | haz <;> rcases hb_res with hb1 | hbz
      · left; rw [hr_eq, ha1, hb1, one_mul]
      · right; rw [hr_eq, ha1, hbz, one_mul]
      · right; rw [hr_eq, haz, hb1, mul_one]
      · left; rw [hr_eq, haz, hbz, h.z_sq]
    rcases hrG with h1 | hz
    · exact Subtype.ext h1
    · have hr2 : r ^ 2 = 1 := by
        apply Subtype.ext
        have h2 : ((r : ↥M) : G) ^ 2 = 1 := by rw [hz, pow_two]; exact h.z_sq
        simpa using h2
      have hdvd2 : orderOf r ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hr2
      have hrodd : Odd (orderOf r) :=
        Odd.of_dvd_nat hRodd (Subgroup.orderOf_dvd_natCard R hr)
      have hcop : Nat.Coprime (orderOf r) 2 := Nat.coprime_two_right.mpr hrodd
      have h1dvd : orderOf r ∣ 1 :=
        (hcop.dvd_mul_right (m := 1) (n := 2)).mp (by simpa using hdvd2)
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1dvd)
  simpa only [R, M] using hbot

end CFSG.OddStandard.SmallF3.Omega
