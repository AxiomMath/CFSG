module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYGrp

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open Subgroup Equiv

abbrev DBar (D : Type) [Group D] : Type := D ⧸ CFSG.oddCore D

structure DConfig (D : Type) [Group D] where
  y : D
  t : D
  v : D
  J : Subgroup D
  ψ : Perm (Fin 5) ≃* ↥J
  σ₀ : Perm (Fin 5)
  y_ord : orderOf y = 3
  y_central : ∀ d : D, d * y = y * d
  t_sq : t * t = 1
  v_sq : v * v = 1
  t_ne_one : t ≠ 1
  v_ne_one : v ≠ 1
  t_ne_v : t ≠ v
  tv_comm : t * v = v * t
  J_t : ∀ j ∈ J, j * t = t * j
  J_v : ∀ j ∈ J, j * v = v * j
  t_not_J : t ∉ J
  v_not_J : v ∉ J
  tv_not_J : t * v ∉ J
  card_cent : Nat.card ↥(centralizer ({t} : Set D)) ≤ 1440
  σ₀_sq : σ₀ * σ₀ = 1
  σ₀_ne : σ₀ ≠ 1
  fus_v : ∃ g : D, g * t * g⁻¹ = v
  fus_tv : ∃ g : D, g * t * g⁻¹ = t * v
  fus_u : ∃ g : D, g * t * g⁻¹ = t * ((ψ σ₀ : ↥J) : D)

section OddCosets

variable {D : Type} [Group D] [Finite D]

theorem mem_of_mk_eq_of_comm {P : Subgroup D} {a j : D} (ha : a * a = 1) (hj : j ∈ P)
    (hcomm : j * a = a * j) (hmk : (QuotientGroup.mk a : DBar D) = QuotientGroup.mk j) :
    a ∈ P := by
  have hmem : a⁻¹ * j ∈ CFSG.oddCore D := QuotientGroup.eq.1 hmk
  have hodd : Odd (orderOf (a⁻¹ * j)) :=
    Odd.of_dvd_nat odd_card_oddCore' (Subgroup.orderOf_dvd_natCard _ hmem)
  obtain ⟨k, hk⟩ := hodd
  have hpow : (a⁻¹ * j) ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hcm : Commute a⁻¹ j := by rw [hai]; exact hcomm.symm
  rw [hcm.mul_pow, hai, pow_succ, pow_mul, pow_two, ha, one_pow, one_mul] at hpow
  have : a = (j ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_left hpow
  rw [this]
  exact P.inv_mem (P.pow_mem hj _)

end OddCosets

section Quotient

variable {D : Type} [Group D] [Finite D] (c : DConfig D)

@[expose] def DConfig.tb : DBar D := QuotientGroup.mk c.t

@[expose] def DConfig.vb : DBar D := QuotientGroup.mk c.v

omit [Finite D] in
theorem DConfig.y_mem_oddCore : c.y ∈ CFSG.oddCore D := by
  have hz : c.y ∈ center D := mem_center_iff.2 fun g => c.y_central g
  have : (zpowers c.y).Normal := normal_zpowers_of_mem_center hz
  have hodd : Odd (Nat.card (zpowers c.y)) := by
    rw [Nat.card_zpowers, c.y_ord]
    decide
  exact le_oddCore_of_normal' hodd (mem_zpowers c.y)

omit [Finite D] in
theorem DConfig.tb_sq : c.tb * c.tb = 1 := by
  rw [DConfig.tb, ← QuotientGroup.mk_mul, c.t_sq, QuotientGroup.mk_one]

omit [Finite D] in
theorem DConfig.vb_sq : c.vb * c.vb = 1 := by
  rw [DConfig.vb, ← QuotientGroup.mk_mul, c.v_sq, QuotientGroup.mk_one]

theorem DConfig.tb_ne_one : c.tb ≠ 1 := fun h =>
  c.t_ne_one (eq_one_of_sq_mem_oddCore ((QuotientGroup.eq_one_iff _).1 h) c.t_sq)

theorem DConfig.vb_ne_one : c.vb ≠ 1 := fun h =>
  c.v_ne_one (eq_one_of_sq_mem_oddCore ((QuotientGroup.eq_one_iff _).1 h) c.v_sq)

theorem DConfig.tb_ne_vb : c.tb ≠ c.vb := mk_ne_of_involutions c.t_sq c.v_sq c.tv_comm c.t_ne_v

omit [Finite D] in
theorem DConfig.tvb_comm : c.tb * c.vb = c.vb * c.tb := by
  rw [DConfig.tb, DConfig.vb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, c.tv_comm]

theorem DConfig.orderOf_tb : orderOf c.tb = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact c.tb_sq) c.tb_ne_one

theorem DConfig.orderOf_vb : orderOf c.vb = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact c.vb_sq) c.vb_ne_one

omit [Finite D] in
theorem DConfig.mem_V {a : DBar D} (ha : a ∈ zpowers c.tb ⊔ zpowers c.vb) :
    a = 1 ∨ a = c.tb ∨ a = c.vb ∨ a = c.tb * c.vb := by
  have hc : ∀ h ∈ zpowers c.tb, ∀ k ∈ zpowers c.vb, h * k = k * h := by
    intro h hh k hk
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hh
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk
    exact (Commute.zpow_zpow (show Commute c.tb c.vb from c.tvb_comm) m n).eq
  obtain ⟨h, hh, k, hk, rfl⟩ := mem_sup_of_commute hc ha
  rcases mem_zpowers_involution c.tb_sq hh with rfl | rfl <;>
    rcases mem_zpowers_involution c.vb_sq hk with rfl | rfl <;> simp

@[expose] def DConfig.fhom : Perm (Fin 5) →* DBar D :=
  (QuotientGroup.mk' (CFSG.oddCore D)).comp (c.J.subtype.comp c.ψ.toMonoidHom)

omit [Finite D] in
theorem DConfig.fhom_apply (σ : Perm (Fin 5)) :
    c.fhom σ = QuotientGroup.mk ((c.ψ σ : ↥c.J) : D) := rfl

theorem DConfig.fhom_injective : Function.Injective c.fhom := by
  set N := c.fhom.ker with hN
  have hker : ∀ σ : N, ((c.ψ (σ : Perm (Fin 5)) : ↥c.J) : D) ∈ CFSG.oddCore D := fun σ =>
    (QuotientGroup.eq_one_iff _).1 σ.2
  let g : ↥N →* ↥(CFSG.oddCore D) :=
    ((c.J.subtype.comp c.ψ.toMonoidHom).comp N.subtype).codRestrict _ hker
  have hg : Function.Injective g := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (c.ψ.injective (Subtype.ext this))
  have hodd : Odd (Nat.card N) :=
    Odd.of_dvd_nat odd_card_oddCore' (Subgroup.card_dvd_of_injective g hg)
  have hbot : N = ⊥ := eq_bot_of_normal_odd_perm_five N hodd
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have : σ ∈ N := hσ
  rw [hbot, mem_bot] at this
  exact this

theorem DConfig.card_J : Nat.card ↥c.fhom.range = 120 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective c.fhom_injective).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

omit [Finite D] in
theorem DConfig.V_comm_J :
    ∀ a ∈ zpowers c.tb ⊔ zpowers c.vb, ∀ b ∈ c.fhom.range, a * b = b * a := by
  intro a ha b hb
  obtain ⟨σ, rfl⟩ := hb
  rw [DConfig.fhom_apply]
  have hj := (c.ψ σ).2
  have h1 : (QuotientGroup.mk ((c.ψ σ : ↥c.J) : D) : DBar D) * c.tb = c.tb *
      QuotientGroup.mk ((c.ψ σ : ↥c.J) : D) := by
    rw [DConfig.tb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, c.J_t _ hj]
  have h2 : (QuotientGroup.mk ((c.ψ σ : ↥c.J) : D) : DBar D) * c.vb = c.vb *
      QuotientGroup.mk ((c.ψ σ : ↥c.J) : D) := by
    rw [DConfig.vb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, c.J_v _ hj]
  rcases c.mem_V ha with rfl | rfl | rfl | rfl
  · simp
  · exact h1.symm
  · exact h2.symm
  · rw [mul_assoc, ← h2, ← mul_assoc, ← h1, mul_assoc]

theorem DConfig.V_inf_J : (zpowers c.tb ⊔ zpowers c.vb) ⊓ c.fhom.range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxV, σ, rfl⟩
  rw [mem_bot]
  have hj := (c.ψ σ).2
  have hmk : ∀ a : D, a * a = 1 → (QuotientGroup.mk a : DBar D) = c.fhom σ →
      ∀ _ : (c.ψ σ : ↥c.J) * a = a * (c.ψ σ : ↥c.J), a ∈ c.J := by
    intro a ha h hcomm
    exact mem_of_mk_eq_of_comm ha hj hcomm h
  rcases c.mem_V hxV with h | h | h | h
  · exact h
  · exfalso
    exact c.t_not_J (hmk c.t c.t_sq h.symm (c.J_t _ hj))
  · exfalso
    exact c.v_not_J (hmk c.v c.v_sq h.symm (c.J_v _ hj))
  · exfalso
    have hsq : c.t * c.v * (c.t * c.v) = 1 := by
      calc c.t * c.v * (c.t * c.v) = c.t * (c.v * c.t) * c.v := by group
        _ = c.t * (c.t * c.v) * c.v := by rw [c.tv_comm]
        _ = (c.t * c.t) * (c.v * c.v) := by group
        _ = 1 := by rw [c.t_sq, c.v_sq, one_mul]
    have hcomm : (c.ψ σ : ↥c.J) * (c.t * c.v) = (c.t * c.v) * (c.ψ σ : ↥c.J) := by
      rw [← mul_assoc, c.J_t _ hj, mul_assoc, c.J_v _ hj, ← mul_assoc]
    refine c.tv_not_J (hmk (c.t * c.v) hsq ?_ hcomm)
    rw [h, DConfig.tb, DConfig.vb, QuotientGroup.mk_mul]

theorem DConfig.card_V : Nat.card ↥(zpowers c.tb ⊔ zpowers c.vb) = 4 := by
  have hc : ∀ h ∈ zpowers c.tb, ∀ k ∈ zpowers c.vb, h * k = k * h := by
    intro h hh k hk
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hh
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk
    exact (Commute.zpow_zpow (show Commute c.tb c.vb from c.tvb_comm) m n).eq
  have hd : zpowers c.tb ⊓ zpowers c.vb = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [mem_bot]
    rcases mem_zpowers_involution c.tb_sq hx1 with h | h
    · exact h
    · rcases mem_zpowers_involution c.vb_sq hx2 with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') c.tb_ne_vb
  rw [card_sup_of_commute hc hd, Nat.card_zpowers, Nat.card_zpowers, c.orderOf_tb,
    c.orderOf_vb]

theorem DConfig.card_VJ :
    Nat.card ↥((zpowers c.tb ⊔ zpowers c.vb) ⊔ c.fhom.range) = 480 := by
  rw [card_sup_of_commute c.V_comm_J c.V_inf_J, c.card_V, c.card_J]

end Quotient

end CFSG.EvenSporadicStandard.HSStd.FiveY
