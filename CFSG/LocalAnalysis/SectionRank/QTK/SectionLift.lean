module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.SectionRank.QTK

open Subgroup

section Lift

variable {Y : Type*} [Group Y] {r : ℕ}

theorem conj_pow_eq_of_mem_center {c x y : Y} (hc : c ∈ center Y) (hxy : x * y * x⁻¹ = c * y)
    (n : ℕ) : x ^ n * y * (x ^ n)⁻¹ = c ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcx : x * c * x⁻¹ = c := by rw [mem_center_iff.mp hc x, mul_inv_cancel_right]
    calc x ^ (n + 1) * y * (x ^ (n + 1))⁻¹ = x * (x ^ n * y * (x ^ n)⁻¹) * x⁻¹ := by group
      _ = x * (c ^ n * y) * x⁻¹ := by rw [ih]
      _ = (x * c ^ n * x⁻¹) * (x * y * x⁻¹) := by group
      _ = (x * c * x⁻¹) ^ n * (x * y * x⁻¹) := by rw [conj_pow]
      _ = c ^ n * (c * y) := by rw [hcx, hxy]
      _ = c ^ (n + 1) * y := by rw [pow_succ, mul_assoc]

theorem eq_one_of_mem_center_of_not_dvd (hr : r.Prime) (hrZ : ¬ r ∣ Nat.card (center Y))
    {w : Y} (hw : w ∈ center Y) (hwr : w ^ r = 1) : w = 1 := by
  have hd : orderOf w ∣ r := orderOf_dvd_of_pow_eq_one hwr
  have hdZ : orderOf w ∣ Nat.card (center Y) := by
    rw [← Subgroup.orderOf_mk w hw]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime r (Nat.card (center Y)) := (Nat.Prime.coprime_iff_not_dvd hr).mpr hrZ
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left hd) hdZ)

theorem mul_comm_of_mk_mem (hr : r.Prime) (hrZ : ¬ r ∣ Nat.card (center Y))
    {E : Subgroup (Y ⧸ center Y)} (hE : CFSG.Open.IsElemAbelian r E) {x y : Y}
    (hx : (x : Y ⧸ center Y) ∈ E) (hy : (y : Y ⧸ center Y) ∈ E) : x * y = y * x := by
  set c := x * y * x⁻¹ * y⁻¹ with hcdef
  have hcomm : (x : Y ⧸ center Y) * y = y * x :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  have hc : c ∈ center Y := by
    rw [← QuotientGroup.eq_one_iff, hcdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hcomm]
    group
  have hxy : x * y * x⁻¹ = c * y := by rw [hcdef]; group
  have hxr : x ^ r ∈ center Y := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hE.2 _ hx
  have h1 := conj_pow_eq_of_mem_center hc hxy r
  have h2 : x ^ r * y * (x ^ r)⁻¹ = y := by
    rw [← mem_center_iff.mp hxr y, mul_inv_cancel_right]
  rw [h2] at h1
  have hcr : c ^ r = 1 := mul_right_cancel (h1.symm.trans (one_mul y).symm)
  have hc1 := eq_one_of_mem_center_of_not_dvd hr hrZ hc hcr
  calc x * y = c * (y * x) := by rw [hcdef]; group
    _ = y * x := by rw [hc1, one_mul]

theorem pow_pred_mod_eq_one (hr : r.Prime) {m : ℕ} (hrm : ¬ r ∣ m) : m ^ (r - 1) % r = 1 := by
  have hcop : Nat.Coprime m r := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrm)
  have h := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime hr] at h
  rw [h]
  exact Nat.mod_eq_of_lt hr.one_lt

theorem exists_lift (hr : r.Prime) (hrZ : ¬ r ∣ Nat.card (center Y))
    {E : Subgroup (Y ⧸ center Y)} (hE : CFSG.Open.IsElemAbelian r E) :
    ∃ P : Subgroup Y, CFSG.Open.IsElemAbelian r P ∧ Nat.card P = Nat.card E ∧
      P.map (QuotientGroup.mk' (center Y)) = E := by
  let P : Subgroup Y :=
    { carrier := {w | (w : Y ⧸ center Y) ∈ E ∧ w ^ r = 1}
      mul_mem' := fun {a b} ha hb => ⟨by rw [QuotientGroup.mk_mul]; exact E.mul_mem ha.1 hb.1,
        by rw [Commute.mul_pow (show Commute a b from mul_comm_of_mk_mem hr hrZ hE ha.1 hb.1),
          ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨by rw [QuotientGroup.mk_one]; exact E.one_mem, one_pow r⟩
      inv_mem' := fun {a} ha => ⟨by rw [QuotientGroup.mk_inv]; exact E.inv_mem ha.1,
        by rw [inv_pow, ha.2, inv_one]⟩ }
  have hmapE : P.map (QuotientGroup.mk' (center Y)) = E := by
    refine le_antisymm (by rintro _ ⟨w, hw, rfl⟩; exact hw.1) fun e he => ?_
    obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective e
    set m := Nat.card (center Y) with hm
    have hw₀r : w₀ ^ r ∈ center Y := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hE.2 _ he
    have hferm := pow_pred_mod_eq_one hr hrZ
    refine ⟨w₀ ^ (m ^ (r - 1)), ⟨?_, ?_⟩, ?_⟩
    · rw [QuotientGroup.mk_pow]
      exact E.pow_mem he _
    · have h1 : (⟨w₀ ^ r, hw₀r⟩ : center Y) ^ m = 1 := pow_card_eq_one'
      have h2 : (w₀ ^ r) ^ m = 1 := by
        simpa using congrArg Subtype.val h1
      obtain ⟨k, hk⟩ : m ∣ m ^ (r - 1) := dvd_pow_self m (by have := hr.two_le; omega)
      rw [← pow_mul, mul_comm, pow_mul, hk, pow_mul, h2, one_pow]
    · change ((w₀ ^ (m ^ (r - 1)) : Y) : Y ⧸ center Y) = w₀
      rw [QuotientGroup.mk_pow, ← Nat.div_add_mod (m ^ (r - 1)) r, hferm, pow_add, pow_mul,
        hE.2 _ he, one_pow, one_mul, pow_one]
  have hinj : Function.Injective ((QuotientGroup.mk' (center Y)).comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro w hw
    apply Subtype.ext
    have hwZ : (w : Y) ∈ center Y := (QuotientGroup.eq_one_iff _).mp hw
    exact eq_one_of_mem_center_of_not_dvd hr hrZ hwZ w.2.2
  refine ⟨P, ⟨⟨⟨fun a b => Subtype.ext (mul_comm_of_mk_mem hr hrZ hE a.2.1 b.2.1)⟩⟩,
    fun w hw => hw.2⟩, ?_, hmapE⟩
  rw [← hmapE, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, MonoidHom.range_comp,
    Subgroup.range_subtype]

end Lift

end CFSG.SectionRank.QTK
