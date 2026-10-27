module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedPointLifting
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GH74.Generic.BProg.B2.WeakSigCaseB

open CFSG Subgroup

section Lam

variable {Y : Type} [Group Y]

@[expose] def lam (L W : Subgroup Y) : Subgroup Y where
  carrier := {l | l ∈ L ∧ ∃ w ∈ W, ∀ y ∈ L, w * y * w⁻¹ = l * y * l⁻¹}
  mul_mem' := by
    rintro a b ⟨haL, w₁, hw₁, h₁⟩ ⟨hbL, w₂, hw₂, h₂⟩
    refine ⟨L.mul_mem haL hbL, w₁ * w₂, W.mul_mem hw₁ hw₂, fun y hy => ?_⟩
    have hy' : b * y * b⁻¹ ∈ L := L.mul_mem (L.mul_mem hbL hy) (L.inv_mem hbL)
    calc w₁ * w₂ * y * (w₁ * w₂)⁻¹ = w₁ * (w₂ * y * w₂⁻¹) * w₁⁻¹ := by group
      _ = w₁ * (b * y * b⁻¹) * w₁⁻¹ := by rw [h₂ y hy]
      _ = a * (b * y * b⁻¹) * a⁻¹ := h₁ _ hy'
      _ = a * b * y * (a * b)⁻¹ := by group
  one_mem' := ⟨L.one_mem, 1, W.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haL, w, hw, h⟩
    refine ⟨L.inv_mem haL, w⁻¹, W.inv_mem hw, fun y hy => ?_⟩
    have hy' : a⁻¹ * y * a ∈ L := L.mul_mem (L.mul_mem (L.inv_mem haL) hy) haL
    have h2 : w * (a⁻¹ * y * a) * w⁻¹ = y := by rw [h _ hy']; group
    calc w⁻¹ * y * w⁻¹⁻¹ = w⁻¹ * (w * (a⁻¹ * y * a) * w⁻¹) * w := by rw [h2]; simp
      _ = a⁻¹ * y * a⁻¹⁻¹ := by group

theorem lam_le {L W : Subgroup Y} : lam L W ≤ L := fun _ h => h.1

theorem lam_conj_mem {L W : Subgroup Y} {g l : Y} (hgL : g ∈ normalizer (L : Set Y))
    (hgW : g ∈ normalizer (W : Set Y)) (hl : l ∈ lam L W) : g * l * g⁻¹ ∈ lam L W := by
  obtain ⟨hlL, w, hw, h⟩ := hl
  have hgl : g * l * g⁻¹ ∈ L := (mem_normalizer_iff.mp hgL l).mp hlL
  refine ⟨hgl, g * w * g⁻¹, (mem_normalizer_iff.mp hgW w).mp hw, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ L := by
    simpa using (mem_normalizer_iff.mp (inv_mem hgL) y).mp hy
  calc g * w * g⁻¹ * y * (g * w * g⁻¹)⁻¹ = g * (w * (g⁻¹ * y * g) * w⁻¹) * g⁻¹ := by group
    _ = g * (l * (g⁻¹ * y * g) * l⁻¹) * g⁻¹ := by rw [h _ hy']
    _ = (g * l * g⁻¹) * y * (g * l * g⁻¹)⁻¹ := by group

theorem mem_normalizer_lam {L W : Subgroup Y} {g : Y} (hgL : g ∈ normalizer (L : Set Y))
    (hgW : g ∈ normalizer (W : Set Y)) : g ∈ normalizer (lam L W : Set Y) := by
  rw [mem_normalizer_iff]
  intro l
  constructor
  · exact lam_conj_mem hgL hgW
  · intro h
    have := lam_conj_mem (inv_mem hgL) (inv_mem hgW) h
    simpa [mul_assoc] using this

theorem lam_comm_mem {L W : Subgroup Y} {x c w : Y} (hWL : W ≤ normalizer (L : Set Y))
    (hxW : x ∈ normalizer (W : Set Y)) (hc : c ∈ L)
    (hx : ∀ y ∈ L, x * y * x⁻¹ = c * y * c⁻¹) (hw : w ∈ W) :
    c * w * c⁻¹ * w⁻¹ ∈ lam L W := by
  have hwL : ∀ y ∈ L, w * y * w⁻¹ ∈ L := fun y hy => (mem_normalizer_iff.mp (hWL hw) y).mp hy
  have hwL' : ∀ y ∈ L, w⁻¹ * y * w ∈ L := fun y hy => by
    simpa using (mem_normalizer_iff.mp (hWL (W.inv_mem hw)) y).mp hy
  have hpL : c * w * c⁻¹ * w⁻¹ ∈ L := by
    have := L.mul_mem hc (hwL _ (L.inv_mem hc))
    simpa [mul_assoc] using this
  have hxw : x * w * x⁻¹ * w⁻¹ ∈ W :=
    W.mul_mem ((mem_normalizer_iff.mp hxW w).mp hw) (W.inv_mem hw)
  refine ⟨hpL, x * w * x⁻¹ * w⁻¹, hxw, fun y hy => ?_⟩
  set z : Y := w⁻¹ * y * w with hz
  have hzL : z ∈ L := hwL' y hy
  set y' : Y := c⁻¹ * z * c with hy'
  have hy'L : y' ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hc) hzL) hc
  have h3 : x⁻¹ * z * x = y' := by
    have h1 := hx y' hy'L
    have h2 : c * y' * c⁻¹ = z := by rw [hy']; group
    rw [h2] at h1
    calc x⁻¹ * z * x = x⁻¹ * (x * y' * x⁻¹) * x := by rw [h1]
      _ = y' := by group
  have hwy' : w * y' * w⁻¹ ∈ L := hwL y' hy'L
  calc x * w * x⁻¹ * w⁻¹ * y * (x * w * x⁻¹ * w⁻¹)⁻¹
      = x * (w * (x⁻¹ * z * x) * w⁻¹) * x⁻¹ := by rw [hz]; group
    _ = x * (w * y' * w⁻¹) * x⁻¹ := by rw [h3]
    _ = c * (w * y' * w⁻¹) * c⁻¹ := hx _ hwy'
    _ = (c * w * c⁻¹ * w⁻¹) * y * (c * w * c⁻¹ * w⁻¹)⁻¹ := by rw [hy', hz]; group

theorem pow_conj_eq {L : Subgroup Y} {l w : Y} (hl : l ∈ L)
    (h : ∀ y ∈ L, w * y * w⁻¹ = l * y * l⁻¹) (n : ℕ) :
    ∀ y ∈ L, w ^ n * y * (w ^ n)⁻¹ = l ^ n * y * (l ^ n)⁻¹ := by
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    have hy' : l ^ n * y * (l ^ n)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.pow_mem hl n) hy) (L.inv_mem (L.pow_mem hl n))
    calc w ^ (n + 1) * y * (w ^ (n + 1))⁻¹ = w * (w ^ n * y * (w ^ n)⁻¹) * w⁻¹ := by
          rw [pow_succ']; group
      _ = w * (l ^ n * y * (l ^ n)⁻¹) * w⁻¹ := by rw [ih y hy]
      _ = l * (l ^ n * y * (l ^ n)⁻¹) * l⁻¹ := h _ hy'
      _ = l ^ (n + 1) * y * (l ^ (n + 1))⁻¹ := by rw [pow_succ']; group

theorem orderOf_dvd_of_induced {L : Subgroup Y}
    (hcen : ∀ l ∈ L, (∀ y ∈ L, y * l = l * y) → l = 1) {l w : Y} (hl : l ∈ L)
    (h : ∀ y ∈ L, w * y * w⁻¹ = l * y * l⁻¹) : orderOf l ∣ orderOf w := by
  apply orderOf_dvd_of_pow_eq_one
  apply hcen _ (L.pow_mem hl _)
  intro y hy
  have h1 := pow_conj_eq hl h (orderOf w) y hy
  rw [pow_orderOf_eq_one] at h1
  simp only [inv_one, mul_one, one_mul] at h1
  exact (mul_inv_eq_iff_eq_mul.mp h1.symm).symm

theorem odd_card_lam [Finite Y] {L W : Subgroup Y}
    (hcen : ∀ l ∈ L, (∀ y ∈ L, y * l = l * y) → l = 1) (hW : Odd (Nat.card ↥W)) :
    Odd (Nat.card ↥(lam L W)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(lam L W) := by
    rcases Nat.even_or_odd (Nat.card ↥(lam L W)) with h | h
    · exact even_iff_two_dvd.mp h
    · exact absurd h hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨hxL, w, hw, hind⟩ := x.2
  have h1 : orderOf (x : Y) ∣ orderOf w := orderOf_dvd_of_induced hcen hxL hind
  have h3 : orderOf w ∣ Nat.card ↥W := Subgroup.orderOf_dvd_natCard W hw
  have h4 : orderOf (x : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have : 2 ∣ Nat.card ↥W := h4 ▸ h1.trans h3
  exact (Nat.not_even_iff_odd.mpr hW) (even_iff_two_dvd.mpr this)

end Lam

end CFSG.GH74.Generic.BProg.B2.WeakSigCaseB
