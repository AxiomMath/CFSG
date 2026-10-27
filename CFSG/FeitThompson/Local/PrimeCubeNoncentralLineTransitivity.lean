module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
import CFSG.FeitThompson.Local.PrimeCubeNonabelianCommutatorCentre
import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise
open scoped commutatorElement

variable {p : ℕ} {Q : Type*} [Group Q] {A : Subgroup Q}

theorem conj_smul_zpowers (g x : Q) : MulAut.conj g • zpowers x = zpowers (g * x * g⁻¹) := by
  have h : (MulAut.conj g • zpowers x : Subgroup Q)
      = (zpowers x).map (MulAut.conj g : Q →* Q) := rfl
  rw [h, MonoidHom.map_zpowers]
  rfl

theorem zpowers_eq_of_card_eq_prime [Finite Q] {H : Subgroup Q} (hp : p.Prime)
    (hH : Nat.card H = p) {x : Q} (hx : x ∈ H) (hx1 : x ≠ 1) : zpowers x = H := by
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hx) ?_
  rw [hH, Nat.card_zpowers]
  rcases (Nat.dvd_prime hp).mp (hH ▸ H.orderOf_dvd_natCard hx) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx1
  · exact h.ge

theorem card_eq_prime_of_mulEquiv {H : Subgroup Q}
    (e : H ≃* (Fin 1 → Multiplicative (ZMod p))) : Nat.card H = p := by
  rw [Nat.card_congr e.toEquiv, card_pi_multiplicative_zmod, pow_one]

theorem exists_generator_notMem_center [Finite Q] (hp : p.Prime)
    (hZcard : Nat.card (center Q) = p) {H : Subgroup Q} (hHcard : Nat.card H = p)
    (hHZ : H ≠ center Q) : ∃ x ∈ H, x ∉ center Q ∧ zpowers x = H := by
  have hbot : H ≠ ⊥ := by
    intro h
    rw [h, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩] at hHcard
    exact hp.ne_one hHcard.symm
  obtain ⟨x, hxH, hx1⟩ := (Subgroup.bot_or_exists_ne_one H).resolve_left hbot
  have hgen : zpowers x = H := zpowers_eq_of_card_eq_prime hp hHcard hxH hx1
  refine ⟨x, hxH, fun hxZ => hHZ ?_, hgen⟩
  exact Subgroup.eq_of_le_of_card_ge (hgen ▸ zpowers_le.mpr hxZ) (by rw [hZcard, hHcard])

theorem conj_pow_eq_mul_commutatorElement_pow {y z : Q} (h : ⁅y, z⁆ ∈ center Q) (t : ℕ) :
    y ^ t * z * (y ^ t)⁻¹ = z * ⁅y, z⁆ ^ t := by
  have hdc : ∀ g : Q, ⁅y, z⁆ * g = g * ⁅y, z⁆ := fun g => (Subgroup.mem_center_iff.mp h g).symm
  induction t with
  | zero => simp
  | succ t ih =>
    have key : y * z * y⁻¹ = ⁅y, z⁆ * z := by rw [commutatorElement_def]; group
    calc y ^ (t + 1) * z * (y ^ (t + 1))⁻¹
        = y ^ t * (y * z * y⁻¹) * (y ^ t)⁻¹ := by rw [pow_succ, mul_inv_rev]; group
      _ = y ^ t * (⁅y, z⁆ * z) * (y ^ t)⁻¹ := by rw [key]
      _ = ⁅y, z⁆ * (y ^ t * z * (y ^ t)⁻¹) := by
            rw [show y ^ t * (⁅y, z⁆ * z) = ⁅y, z⁆ * (y ^ t * z) from by
              rw [← mul_assoc, ← hdc (y ^ t), mul_assoc], mul_assoc]
      _ = ⁅y, z⁆ * (z * ⁅y, z⁆ ^ t) := by rw [ih]
      _ = z * ⁅y, z⁆ ^ (t + 1) := by rw [← mul_assoc, hdc z, mul_assoc, ← pow_succ']

theorem exists_conj_smul_eq_of_card_eq_prime_sq (hp : p.Prime) (hQ : Nat.card Q = p ^ 3)
    (hnab : ¬ IsMulCommutative Q) (hA : Nat.card A = p ^ 2) {A₀ A₁ : Subgroup Q}
    (hA₀ : A₀ ≤ A) (hA₁ : A₁ ≤ A) (hA₀card : Nat.card A₀ = p) (hA₁card : Nat.card A₁ = p)
    (hA₀Z : A₀ ≠ center Q) (hA₁Z : A₁ ≠ center Q) : ∃ y : Q, MulAut.conj y • A₀ = A₁ := by
  have hfp : Fact p.Prime := ⟨hp⟩
  have hfin : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; exact pow_ne_zero _ hp.ne_zero)
  have hZcard : Nat.card (center Q) = p := card_center_of_card_eq_prime_cube hp hQ hnab
  obtain ⟨y, hy⟩ : ∃ y : Q, y ∉ A := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have h1 : Nat.card A = Nat.card Q :=
      (Subgroup.card_eq_iff_eq_top A).mpr ((Subgroup.eq_top_iff' A).mpr hcon)
    rw [hA, hQ] at h1
    exact absurd (Nat.pow_right_injective hp.two_le h1) (by omega)
  obtain ⟨z, hzA₀, hzZ, hzgen⟩ := exists_generator_notMem_center hp hZcard hA₀card hA₀Z
  obtain ⟨z₁, hz₁A₁, hz₁Z, hz₁gen⟩ := exists_generator_notMem_center hp hZcard hA₁card hA₁Z
  set w := ⁅y, z⁆ with hwdef
  have hwZ : zpowers w = center Q :=
    zpowers_commutatorElement_eq_center hp hQ hnab hA hy (hA₀ hzA₀) hzZ
  have hwmem : w ∈ center Q := hwZ ▸ Subgroup.mem_zpowers w
  have hcw : ∀ g : Q, Commute w g := fun g => (Subgroup.mem_center_iff.mp hwmem g).symm
  have hordz : orderOf z = p := by rw [← Nat.card_zpowers, hzgen, hA₀card]
  have hordw : orderOf w = p := by rw [← Nat.card_zpowers, hwZ, hZcard]
  have hAsup : zpowers z ⊔ center Q = A :=
    zpowers_sup_center_eq_of_card_eq_prime_sq hp hQ hnab hA (hA₀ hzA₀) hzZ
  obtain ⟨k, j, hkj⟩ : ∃ k j : ℕ, z ^ k * w ^ j = z₁ := by
    have h2 : z₁ ∈ (↑(zpowers z ⊔ center Q) : Set Q) := hAsup ▸ hA₁ hz₁A₁
    rw [Subgroup.mul_normal] at h2
    obtain ⟨u, hu, v, hv, huv⟩ := h2
    obtain ⟨k, hk⟩ : ∃ k : ℕ, z ^ k = u := (Submonoid.mem_powers_iff u z).mp
      ((IsOfFinOrder.mem_powers_iff_mem_zpowers (isOfFinOrder_of_finite z)).mpr hu)
    obtain ⟨j, hj⟩ : ∃ j : ℕ, w ^ j = v := (Submonoid.mem_powers_iff v w).mp
      ((IsOfFinOrder.mem_powers_iff_mem_zpowers (isOfFinOrder_of_finite w)).mpr (hwZ ▸ hv))
    exact ⟨k, j, by rw [hk, hj]; exact huv⟩
  have hkcop : Nat.Coprime k p := by
    rcases (Nat.coprime_or_dvd_of_prime hp k).symm with h | h
    · exact absurd (hkj ▸ (by
        rw [pow_eq_one_iff_modEq.mpr (by simpa [hordz] using (Nat.modEq_zero_iff_dvd).mpr h),
          one_mul]
        exact hwZ ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers w) j)) hz₁Z
    · exact h.symm
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t * k ≡ j [MOD p] := by
    have hk0 : (k : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => hp.coprime_iff_not_dvd.mp hkcop.symm h
    refine ⟨((j : ZMod p) / (k : ZMod p)).val, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, div_mul_cancel₀ _ hk0]
  refine ⟨y ^ t, ?_⟩
  have hzw : (z * w ^ t) ^ k = z₁ := by
    rw [((hcw z).pow_left t).symm.mul_pow, ← pow_mul, ← hkj]
    congr 1
    exact pow_eq_pow_iff_modEq.mpr (by rwa [hordw])
  have hmemA : z * w ^ t ∈ A := by
    rw [← hAsup]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers z) (Subgroup.pow_mem _ hwmem t)
  have hcop2 : Nat.Coprime k (orderOf (z * w ^ t)) :=
    Nat.Coprime.coprime_dvd_right (hA ▸ A.orderOf_dvd_natCard hmemA) (hkcop.pow_right 2)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop2
  rw [← hzgen, conj_smul_zpowers, conj_pow_eq_mul_commutatorElement_pow hwmem, ← hz₁gen]
  refine le_antisymm (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
  · refine ⟨(m : ℤ), ?_⟩
    change z₁ ^ (m : ℤ) = z * w ^ t
    rw [zpow_natCast, ← hzw, hm]
  · exact hzw ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k

theorem exists_conj_inv_smul_eq_of_card_eq_prime_sq (hp : p.Prime) (hQ : Nat.card Q = p ^ 3)
    (hnab : ¬ IsMulCommutative Q) (hA : Nat.card A = p ^ 2) {A₀ A₁ : Subgroup Q}
    (hA₀ : A₀ ≤ A) (hA₁ : A₁ ≤ A) (hA₀card : Nat.card A₀ = p) (hA₁card : Nat.card A₁ = p)
    (hA₀Z : A₀ ≠ center Q) (hA₁Z : A₁ ≠ center Q) : ∃ y : Q, MulAut.conj y⁻¹ • A₀ = A₁ := by
  obtain ⟨y, hy⟩ := exists_conj_smul_eq_of_card_eq_prime_sq hp hQ hnab hA hA₀ hA₁ hA₀card
    hA₁card hA₀Z hA₁Z
  exact ⟨y⁻¹, by simpa using hy⟩

theorem exists_conj_smul_eq_of_isElementaryAbelianPlane (hp : p.Prime) (hQ : Nat.card Q = p ^ 3)
    (hnab : ¬ IsMulCommutative Q) (e : A ≃* (Fin 2 → Multiplicative (ZMod p)))
    {A₀ A₁ : Subgroup Q} (hA₀ : A₀ ≤ A) (hA₁ : A₁ ≤ A)
    (e₀ : A₀ ≃* (Fin 1 → Multiplicative (ZMod p))) (e₁ : A₁ ≃* (Fin 1 → Multiplicative (ZMod p)))
    (hA₀Z : A₀ ≠ center Q) (hA₁Z : A₁ ≠ center Q) : ∃ y : Q, MulAut.conj y • A₀ = A₁ :=
  exists_conj_smul_eq_of_card_eq_prime_sq hp hQ hnab (card_eq_prime_sq_of_mulEquiv e) hA₀ hA₁
    (card_eq_prime_of_mulEquiv e₀) (card_eq_prime_of_mulEquiv e₁) hA₀Z hA₁Z

end

end CFSG.FeitThompson
