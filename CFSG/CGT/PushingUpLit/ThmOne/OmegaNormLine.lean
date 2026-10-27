module

public import CFSG.CGT.PushingUpLit.ThmOne.OmegaNorm
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG.Quasithin CFSG.Quasithin.XMod

namespace OmegaNorm

variable {P : Type*} [CommGroup P]

theorem eq_of_apply_mul_inv_mem {S : Subgroup (MulAut P)} (hS : IsIrrSec ↥S (⊥ : Subgroup P) ⊤)
    {U : Subgroup P} (hFU : ∀ f ∈ eqvEnd ↥S P, ∀ u ∈ U, toMonoidEnd f u ∈ U) {w : P}
    (hw : w ∉ U) {f g : AddMonoid.End (Additive P)} (hf : f ∈ eqvEnd ↥S P)
    (hg : g ∈ eqvEnd ↥S P) (h : toMonoidEnd f w * (toMonoidEnd g w)⁻¹ ∈ U) : f = g := by
  by_contra hne
  rcases eqvEnd_isUnit_or_eq_zero hS ⟨f - g, sub_mem hf hg⟩ with hu | hu
  · obtain ⟨e, he⟩ := hu.exists_left_inv
    have h1 : toMonoidEnd (f - g) w ∈ U := by
      rw [toMonoidEnd_sub]
      exact h
    have h2 := hFU _ e.2 _ h1
    rw [← toMonoidEnd_mul] at h2
    have h3 : (e : AddMonoid.End (Additive P)) * (f - g) = 1 := congrArg Subtype.val he
    rw [h3, toMonoidEnd_one] at h2
    exact hw h2
  · exact sub_ne_zero.mpr hne (congrArg Subtype.val hu)

variable [Finite P]

theorem exists_eqvEnd_mul_inv_mem {S : Subgroup (MulAut P)} (hS : IsIrrSec ↥S (⊥ : Subgroup P) ⊤)
    {U : Subgroup P} (hFU : ∀ f ∈ eqvEnd ↥S P, ∀ u ∈ U, toMonoidEnd f u ∈ U)
    (hcard : Nat.card P ≤ Nat.card ↥(eqvEnd ↥S P) * Nat.card ↥U) {w : P} (hw : w ∉ U) (p : P) :
    ∃ f ∈ eqvEnd ↥S P, p * (toMonoidEnd f w)⁻¹ ∈ U := by
  let Φ : ↥(eqvEnd ↥S P) → P ⧸ U := fun f => ((toMonoidEnd (f : AddMonoid.End _) w : P) : P ⧸ U)
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    rw [QuotientGroup.eq] at hfg
    refine Subtype.ext (eq_of_apply_mul_inv_mem hS hFU hw g.2 f.2 ?_).symm
    rw [mul_comm]
    exact hfg
  have hle : Nat.card (P ⧸ U) ≤ Nat.card ↥(eqvEnd ↥S P) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup U
    have h2 : 0 < Nat.card ↥U := Nat.card_pos
    rw [h1] at hcard
    exact Nat.le_of_mul_le_mul_right hcard h2
  obtain ⟨f, hf⟩ := (hΦ.bijective_of_nat_card_le hle).2 (p : P ⧸ U)
  refine ⟨f, f.2, ?_⟩
  have h1 := QuotientGroup.eq.mp hf
  rw [mul_comm]
  exact h1

theorem mul_inv_mem_of_commute_eqvEnd (hP : ∀ p : P, p ^ 2 = 1) {S : Subgroup (MulAut P)}
    (hS : IsIrrSec ↥S (⊥ : Subgroup P) ⊤) {U : Subgroup P}
    (hFU : ∀ f ∈ eqvEnd ↥S P, ∀ u ∈ U, toMonoidEnd f u ∈ U)
    (hcard : Nat.card P ≤ Nat.card ↥(eqvEnd ↥S P) * Nat.card ↥U) {t : MulAut P}
    (htU : ∀ u ∈ U, t u ∈ U)
    (htF : ∀ f ∈ eqvEnd ↥S P, ∀ p, toMonoidEnd f (t p) = t (toMonoidEnd f p))
    {k : ℕ} (htk : t ^ 2 ^ k = 1) (p : P) : t p * p⁻¹ ∈ U := by
  by_cases hU : U = ⊤
  · rw [hU]
    trivial
  obtain ⟨w, hw⟩ : ∃ w, w ∉ U := by
    by_contra h
    push Not at h
    exact hU (eq_top_iff.2 fun x _ => h x)
  obtain ⟨l, hl, hlw⟩ := exists_eqvEnd_mul_inv_mem hS hFU hcard hw (t w)
  have key : ∀ f ∈ eqvEnd ↥S P, t (toMonoidEnd f w) * (toMonoidEnd (f * l) w)⁻¹ ∈ U := by
    intro f hf
    rw [← htF f hf, toMonoidEnd_mul, ← map_inv, ← map_mul]
    exact hFU f hf _ hlw
  have hpow : ∀ j : ℕ, (t ^ j) w * (toMonoidEnd (l ^ j) w)⁻¹ ∈ U := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, pow_zero, MulAut.one_apply, toMonoidEnd_one, mul_inv_cancel]
      exact one_mem _
    | succ j ih =>
      have e : (t ^ (j + 1)) w * (toMonoidEnd (l ^ (j + 1)) w)⁻¹ =
          t ((t ^ j) w * (toMonoidEnd (l ^ j) w)⁻¹) *
            (t (toMonoidEnd (l ^ j) w) * (toMonoidEnd (l ^ j * l) w)⁻¹) := by
        rw [pow_succ', MulAut.mul_apply, pow_succ, map_mul, map_inv]
        group
      rw [e]
      exact mul_mem (htU _ ih) (key _ (pow_mem hl j))
  have hl2 : (⟨l, hl⟩ : ↥(eqvEnd ↥S P)) ^ 2 ^ k = 1 := by
    have h1 := hpow (2 ^ k)
    rw [htk, MulAut.one_apply] at h1
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    refine (eq_of_apply_mul_inv_mem hS hFU hw (one_mem _) (pow_mem hl _) ?_).symm
    rw [toMonoidEnd_one]
    exact h1
  have hl1 : l = 1 := by
    have hnt := nontrivial_eqvEnd hS
    have : CharP ↥(eqvEnd ↥S P) 2 := (eqvEnd_isField_charTwo hP hS).2.2
    have h0 : ((⟨l, hl⟩ : ↥(eqvEnd ↥S P)) - 1) ^ 2 ^ k = 0 := by
      rw [sub_pow_char_pow_of_commute 2 k (Commute.one_right _), hl2, one_pow, sub_self]
    rcases eqvEnd_isUnit_or_eq_zero hS (⟨l, hl⟩ - 1) with hu | hu
    · exact absurd (h0 ▸ hu.pow (2 ^ k)) not_isUnit_zero
    · exact congrArg Subtype.val (sub_eq_zero.mp hu)
  obtain ⟨f, hf, hfp⟩ := exists_eqvEnd_mul_inv_mem hS hFU hcard hw p
  have h1 := key f hf
  rw [hl1, mul_one] at h1
  have e : t p * p⁻¹ = t (p * (toMonoidEnd f w)⁻¹) *
      (t (toMonoidEnd f w) * (toMonoidEnd f w)⁻¹) * (p * (toMonoidEnd f w)⁻¹)⁻¹ := by
    rw [map_mul, map_inv]
    group
  rw [e]
  exact mul_mem (mul_mem (htU _ hfp) h1) (inv_mem hfp)

theorem mul_inv_mem_commV (hP : ∀ p : P, p ^ 2 = 1) {S Y : Subgroup (MulAut P)}
    (hS : IsIrrSec ↥S (⊥ : Subgroup P) ⊤) (hYS : Y ≤ S)
    (hirr : ∀ J : Subgroup P, (∀ y ∈ Y, ∀ j ∈ J, y j ∈ J) → commV Y ⊓ fixV Y ≤ J →
      J ≤ commV Y → J = commV Y ⊓ fixV Y ∨ J = commV Y)
    (hlt : commV Y ⊓ fixV Y < commV Y)
    (hcard : Nat.card P ≤ Nat.card ↥(eqvEnd ↥S P) * Nat.card ↥(commV Y)) {t : MulAut P}
    (htS : t ∈ Subgroup.normalizer (S : Set (MulAut P))) (htY : ∀ y ∈ Y, t * y = y * t)
    {k : ℕ} (htk : t ^ 2 ^ k = 1) (p : P) : t p * p⁻¹ ∈ commV Y :=
  mul_inv_mem_of_commute_eqvEnd hP hS (fun _ hf _ hu => toMonoidEnd_mem_commV hYS hf hu) hcard
    (fun _ hu => commV_apply_mem_of_commute (fun y hy => (htY y hy).symm) hu)
    (fun _ hf q => commute_eqvEnd_of_commute hS hYS hirr hlt htS htY hf q) htk p

end OmegaNorm

end CFSG.CGT.PushingUpLit.ThmOne
