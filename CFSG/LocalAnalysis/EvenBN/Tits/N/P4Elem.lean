module

public import Mathlib
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Generic

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup

variable {Γ : Type*} [Group Γ]

section OnePlus

variable (U : Subgroup Γ)

@[expose] def onePlus (hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (g : Γ) (hg : g ∈ normalizer (U : Set Γ)) :
    U →* U where
  toFun u := ⟨(u : Γ) * (g * u * g⁻¹), mul_mem u.2 ((mem_normalizer_iff.1 hg _).1 u.2)⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    have hga : (g * (a : Γ) * g⁻¹) ∈ U := (mem_normalizer_iff.1 hg _).1 a.2
    have hcomm : (b : Γ) * (g * (a : Γ) * g⁻¹) = (g * (a : Γ) * g⁻¹) * b := hc _ b.2 _ hga
    show ((a : Γ) * b) * (g * ((a : Γ) * b) * g⁻¹) =
      ((a : Γ) * (g * a * g⁻¹)) * ((b : Γ) * (g * b * g⁻¹))
    calc ((a : Γ) * b) * (g * ((a : Γ) * b) * g⁻¹)
        = (a : Γ) * ((b : Γ) * (g * (a : Γ) * g⁻¹)) * (g * b * g⁻¹) := by group
      _ = (a : Γ) * ((g * (a : Γ) * g⁻¹) * b) * (g * b * g⁻¹) := by rw [hcomm]
      _ = ((a : Γ) * (g * a * g⁻¹)) * ((b : Γ) * (g * b * g⁻¹)) := by group

variable {U}

theorem mem_ker_onePlus (hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hsq : ∀ a ∈ U, a * a = 1)
    (g : Γ) (hg : g ∈ normalizer (U : Set Γ)) (u : U) :
    u ∈ (onePlus U hc g hg).ker ↔ g * u = u * g := by
  rw [MonoidHom.mem_ker]
  have hu : (u : Γ)⁻¹ = u := inv_eq_of_mul_eq_one_right (hsq u u.2)
  constructor
  · intro h
    have h1 : (u : Γ) * (g * u * g⁻¹) = 1 := congrArg Subtype.val h
    have h2 : g * (u : Γ) * g⁻¹ = (u : Γ)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hu] at h2
    calc g * (u : Γ) = (g * u * g⁻¹) * g := by group
      _ = u * g := by rw [h2]
  · intro h
    apply Subtype.ext
    show (u : Γ) * (g * u * g⁻¹) = 1
    have : g * (u : Γ) * g⁻¹ = u := by rw [h]; group
    rw [this]
    exact hsq u u.2

end OnePlus

section F20

theorem card_inf_eq_card_subgroupOf (H U : Subgroup Γ) :
    Nat.card ↥(H ⊓ U) = Nat.card ↥(H.subgroupOf U) := by
  rw [← Subgroup.subgroupOf_map_subtype H U]
  exact Subgroup.card_subtype U _

theorem ker_onePlus_eq {U : Subgroup Γ} (hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hsq : ∀ a ∈ U, a * a = 1) (g : Γ) (hg : g ∈ normalizer (U : Set Γ)) :
    (onePlus U hc g hg).ker = (centralizer ({g} : Set Γ)).subgroupOf U := by
  ext u
  rw [mem_ker_onePlus hc hsq g hg u, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem card_inf_centralizer_eq {U : Subgroup Γ} (hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hsq : ∀ a ∈ U, a * a = 1) (g : Γ) (hg : g ∈ normalizer (U : Set Γ)) :
    Nat.card ↥(U ⊓ centralizer ({g} : Set Γ)) = Nat.card ↥(onePlus U hc g hg).ker := by
  rw [inf_comm, card_inf_eq_card_subgroupOf, ker_onePlus_eq hc hsq g hg]

theorem four_le_of_mul_eq {k r : ℕ} (h : k * r = 16) (hle : r ≤ k) : 4 ≤ k := by nlinarith

theorem eight_le_of_dvd_sixteen {k : ℕ} (h4 : 4 ≤ k) (hd : k ∣ 16) (hne : k ≠ 4) : 8 ≤ k := by
  have hk : k ≤ 16 := Nat.le_of_dvd (by norm_num) hd
  interval_cases k <;> omega

theorem le_two_of_mul_eq {k i : ℕ} (h : k * i = 16) (h8 : 8 ≤ k) : i ≤ 2 := by nlinarith

theorem le_four_of_le_mul {i a b : ℕ} (h : i ≤ a * b) (ha : a ≤ 2) (hb : b ≤ 2) : i ≤ 4 := by
  nlinarith

theorem conj_onePlus_of_involution {U : Subgroup Γ} (hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) {g : Γ}
    (hg : g ∈ normalizer (U : Set Γ)) (hgg : g * g = 1) (u : Γ) (hu : u ∈ U) :
    g * (u * (g * u * g⁻¹)) = (u * (g * u * g⁻¹)) * g := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hu' : g * u * g⁻¹ ∈ U := (mem_normalizer_iff.1 hg _).1 hu
  have h1 : g * (g * u * g⁻¹) * g⁻¹ = u := by
    rw [hgi]
    calc g * (g * u * g) * g = (g * g) * u * (g * g) := by group
      _ = u := by rw [hgg]; simp
  have hcomm : u * (g * u * g⁻¹) = (g * u * g⁻¹) * u := hc _ hu _ hu'
  have h2 : g * (u * (g * u * g⁻¹)) * g⁻¹ = u * (g * u * g⁻¹) := by
    calc g * (u * (g * u * g⁻¹)) * g⁻¹ = (g * u * g⁻¹) * (g * (g * u * g⁻¹) * g⁻¹) := by group
      _ = (g * u * g⁻¹) * u := by rw [h1]
      _ = u * (g * u * g⁻¹) := hcomm.symm
  calc g * (u * (g * u * g⁻¹)) = (g * (u * (g * u * g⁻¹)) * g⁻¹) * g := by group
    _ = (u * (g * u * g⁻¹)) * g := by rw [h2]

theorem card_centralizer_inverting {U : Subgroup Γ} (hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hsq : ∀ a ∈ U, a * a = 1) (hcard : Nat.card U = 16) {x w : Γ}
    (hx : x ∈ normalizer (U : Set Γ)) (hw : w ∈ normalizer (U : Set Γ)) (hww : w * w = 1)
    (hwx : w * x * w⁻¹ = x⁻¹) (hx5 : x ^ 5 = 1) (hfpf : ∀ u ∈ U, x * u * x⁻¹ = u → u = 1) :
    Nat.card ↥(U ⊓ centralizer ({w} : Set Γ)) = 4 := by
  classical
  haveI : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rw [card_inf_centralizer_eq hc hsq w hw]
  set φ := onePlus U hc w hw with hφ
  have hker : ∀ u : U, u ∈ φ.ker ↔ w * u = u * w := mem_ker_onePlus hc hsq w hw
  have hrk : φ.range ≤ φ.ker := by
    rintro _ ⟨u, rfl⟩
    rw [hker]
    exact conj_onePlus_of_involution hc hw hww u u.2
  have hmul : Nat.card φ.ker * Nat.card φ.range = 16 := by
    rw [Subgroup.card_ker_mul_card_range φ, hcard]
  have hle : Nat.card φ.range ≤ Nat.card φ.ker := Subgroup.card_le_of_le hrk
  have h4 : 4 ≤ Nat.card φ.ker := four_le_of_mul_eq hmul hle
  have hdvd : Nat.card φ.ker ∣ 16 := ⟨Nat.card φ.range, hmul.symm⟩
  by_contra hne
  have h8 : 8 ≤ Nat.card φ.ker := eight_le_of_dvd_sixteen h4 hdvd hne
  have hidx : φ.ker.index ≤ 2 := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [hcard] at h1
    exact le_two_of_mul_eq h1 h8
  let f : U →* U := (conjActHom U ⟨x⁻¹, inv_mem hx⟩).toMonoidHom
  have hfs : Function.Surjective f := (conjActHom U ⟨x⁻¹, inv_mem hx⟩).surjective
  have hidx' : (φ.ker.comap f).index ≤ 2 := by
    rw [Subgroup.index_comap_of_surjective φ.ker hfs]
    exact hidx
  have hidx2 : (φ.ker ⊓ φ.ker.comap f).index ≤ 4 :=
    le_four_of_le_mul Subgroup.index_inf_le hidx hidx'
  have hcard2 : 1 < Nat.card ↥(φ.ker ⊓ φ.ker.comap f) := by
    have h1 := Subgroup.card_mul_index (φ.ker ⊓ φ.ker.comap f)
    rw [hcard] at h1
    have hpos : 0 < (φ.ker ⊓ φ.ker.comap f).index := Nat.pos_of_ne_zero (by
      intro h0; rw [h0] at h1; simp at h1)
    nlinarith
  have hne1 : (φ.ker ⊓ φ.ker.comap f) ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot _).1 hcard2
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne1
  obtain ⟨huK0, huK'⟩ := hu
  have huK : u ∈ φ.ker := huK0
  rw [hker] at huK
  have huK'' : f u ∈ φ.ker := huK'
  rw [hker] at huK''
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hu1' : (u : Γ) ≠ 1 := fun h1 => hu1 (Subtype.ext (Subtype.ext h1))
  have e1 : (w : Γ) * u = u * w := huK
  have hfu : ((f u : U) : Γ) = x⁻¹ * u * x := by
    show x⁻¹ * (u : Γ) * (x⁻¹)⁻¹ = _
    rw [inv_inv]
  have e2 : (w : Γ) * (x⁻¹ * u * x) = (x⁻¹ * u * x) * w := by
    rw [hfu] at huK''
    exact huK''
  have e3 : (x * w * x⁻¹) * u = u * (x * w * x⁻¹) := by
    calc (x * w * x⁻¹) * u = x * (w * (x⁻¹ * u * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * u * x) * w) * x⁻¹ := by rw [e2]
      _ = u * (x * w * x⁻¹) := by group
  have e4 : w * (x * w * x⁻¹) = x⁻¹ * x⁻¹ := by
    have h' : w * x * w = x⁻¹ := by
      have := hwx
      rwa [hwi] at this
    calc w * (x * w * x⁻¹) = (w * x * w) * x⁻¹ := by group
      _ = x⁻¹ * x⁻¹ := by rw [h']
  have e5 : (x⁻¹ * x⁻¹) * u = u * (x⁻¹ * x⁻¹) := by
    rw [← e4]
    calc w * (x * w * x⁻¹) * u = w * ((x * w * x⁻¹) * u) := by group
      _ = w * (u * (x * w * x⁻¹)) := by rw [e3]
      _ = (w * u) * (x * w * x⁻¹) := by group
      _ = (u * w) * (x * w * x⁻¹) := by rw [e1]
      _ = u * (w * (x * w * x⁻¹)) := by group
  have e6 : x * u = u * x := by
    have h5 : x * x * x * x * x = 1 := by simpa [pow_succ] using hx5
    have hxx : x⁻¹ * x⁻¹ * (x⁻¹ * x⁻¹) = x := by
      calc x⁻¹ * x⁻¹ * (x⁻¹ * x⁻¹) = x * (x * x * x * x * x)⁻¹ := by group
        _ = x := by rw [h5]; simp
    calc x * u = (x⁻¹ * x⁻¹ * (x⁻¹ * x⁻¹)) * u := by rw [hxx]
      _ = (x⁻¹ * x⁻¹) * ((x⁻¹ * x⁻¹) * u) := by group
      _ = (x⁻¹ * x⁻¹) * (u * (x⁻¹ * x⁻¹)) := by rw [e5]
      _ = ((x⁻¹ * x⁻¹) * u) * (x⁻¹ * x⁻¹) := by group
      _ = (u * (x⁻¹ * x⁻¹)) * (x⁻¹ * x⁻¹) := by rw [e5]
      _ = u * (x⁻¹ * x⁻¹ * (x⁻¹ * x⁻¹)) := by group
      _ = u * x := by rw [hxx]
  have : x * (u : Γ) * x⁻¹ = u := by rw [e6]; group
  exact hu1' (hfpf u u.2 this)

structure IsF20 (U : Subgroup Γ) (x v : Γ) : Prop where
  comm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a
  sq : ∀ a ∈ U, a * a = 1
  card : Nat.card U = 16
  x_norm : x ∈ normalizer (U : Set Γ)
  v_norm : v ∈ normalizer (U : Set Γ)
  x5 : x ^ 5 = 1
  v4 : v ^ 4 = 1
  vx : v * x * v⁻¹ = x ^ 2 ∨ v * x * v⁻¹ = x ^ 3
  fpf : ∀ u ∈ U, x * u * x⁻¹ = u → u = 1

namespace IsF20

variable {U : Subgroup Γ} {x v : Γ}

theorem inv_eq_pow_four (h : IsF20 U x v) : x⁻¹ = x ^ 4 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ']
  exact h.x5

theorem sq_conj (h : IsF20 U x v) : v ^ 2 * x * (v ^ 2)⁻¹ = x⁻¹ := by
  have h4 : x ^ 4 = x⁻¹ := h.inv_eq_pow_four.symm
  have h9 : x ^ 9 = x⁻¹ := by
    rw [← h4, show (9 : ℕ) = 5 + 4 by norm_num, pow_add, h.x5, one_mul]
  have e : v ^ 2 * x * (v ^ 2)⁻¹ = v * (v * x * v⁻¹) * v⁻¹ := by
    rw [pow_two, mul_inv_rev]; simp only [mul_assoc]
  rw [e]
  rcases h.vx with hv | hv
  · rw [hv]
    have : v * x ^ 2 * v⁻¹ = (v * x * v⁻¹) ^ 2 := by
      have := conj_pow (i := (2 : ℕ)) (a := v) (b := x)
      simpa using this.symm
    rw [this, hv, ← pow_mul]
    exact h4
  · rw [hv]
    have : v * x ^ 3 * v⁻¹ = (v * x * v⁻¹) ^ 3 := by
      have := conj_pow (i := (3 : ℕ)) (a := v) (b := x)
      simpa using this.symm
    rw [this, hv, ← pow_mul]
    exact h9

theorem sq_mul_self (h : IsF20 U x v) : v ^ 2 * v ^ 2 = 1 := by
  rw [← pow_add]
  exact h.v4

theorem sq_norm (h : IsF20 U x v) : v ^ 2 ∈ normalizer (U : Set Γ) := pow_mem h.v_norm 2

end IsF20

end F20

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
