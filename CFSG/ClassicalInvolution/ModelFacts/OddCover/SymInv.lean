module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Bilinear

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

theorem eq_one_of_scale {K W : Type*} [Field K] [CommGroup W] (f : K → W)
    (hf : ∀ x y, f (x + y) = f x * f y) {t : K} (ht : t ≠ 1) (hs : ∀ x, f (t * x) = f x) :
    ∀ x, f x = 1 := by
  have h0 : f 0 = 1 := by
    have := hf 0 0
    rw [add_zero] at this
    simpa using this
  have hneg : ∀ x, f (-x) = (f x)⁻¹ := fun x => by
    have := hf x (-x)
    rw [add_neg_cancel, h0] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  intro x
  have ht1 : t - 1 ≠ 0 := sub_ne_zero.2 ht
  have h1 : f ((t - 1) * (x / (t - 1))) = 1 := by
    rw [show (t - 1) * (x / (t - 1)) = t * (x / (t - 1)) + -(x / (t - 1)) by ring, hf, hs, hneg,
      mul_inv_cancel]
  rwa [mul_div_cancel₀ _ ht1] at h1

theorem eq_one_of_symInv {K W : Type*} [Field K] [CommGroup W]
    (h5 : ∃ a : K, a ≠ 0 ∧ a + 1 ≠ 0 ∧ a ^ 2 + a + 1 ≠ 0)
    (h3 : ∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ t ^ 2 ≠ 1) (B : K × K × K → K × K × K → W)
    (hadd₁ : ∀ x x' y, B (x + x') y = B x y * B x' y)
    (hadd₂ : ∀ x y y', B x (y + y') = B x y * B x y')
    (hT : ∀ t₁ t₂ : K, t₁ ≠ 0 → t₂ ≠ 0 → ∀ u u' : K × K × K,
      B (t₁ ^ 2 * u.1, t₁ * t₂ * u.2.1, t₂ ^ 2 * u.2.2)
        (t₁ ^ 2 * u'.1, t₁ * t₂ * u'.2.1, t₂ ^ 2 * u'.2.2) = B u u')
    (hG : ∀ u u' : K × K × K,
      B (u.1 + 2 * u.2.1 + u.2.2, u.2.1 + u.2.2, u.2.2)
        (u'.1 + 2 * u'.2.1 + u'.2.2, u'.2.1 + u'.2.2, u'.2.2) = B u u')
    (hW : ∀ u u' : K × K × K, B (u.2.2, u.2.1, u.1) (u'.2.2, u'.2.1, u'.1) = B u u') :
    ∀ u u', B u u' = 1 := by
  obtain ⟨t, ht0, ht1, ht2⟩ := h3
  have hL : ∀ x y : K × K × K,
      B x y = B (x.1, 0, 0) y * B (0, x.2.1, 0) y * B (0, 0, x.2.2) y := by
    intro x y
    have : x = (x.1, 0, 0) + (0, x.2.1, 0) + (0, 0, x.2.2) := by ext <;> simp
    conv_lhs => rw [this]
    rw [hadd₁, hadd₁]
  have hR : ∀ x y : K × K × K,
      B x y = B x (y.1, 0, 0) * B x (0, y.2.1, 0) * B x (0, 0, y.2.2) := by
    intro x y
    have : y = (y.1, 0, 0) + (0, y.2.1, 0) + (0, 0, y.2.2) := by ext <;> simp
    conv_lhs => rw [this]
    rw [hadd₂, hadd₂]
  have c12 : ∀ a b : K, B (a, 0, 0) (0, b, 0) = 1 := by
    intro a b
    exact eq_one_of_scale (fun b => B (a, 0, 0) (0, b, 0))
      (fun b b' => by simpa using hadd₂ (a, 0, 0) (0, b, 0) (0, b', 0)) ht1
      (fun b => by simpa using hT 1 t one_ne_zero ht0 (a, 0, 0) (0, b, 0)) b
  have c21 : ∀ a b : K, B (0, a, 0) (b, 0, 0) = 1 := by
    intro a b
    exact eq_one_of_scale (fun a => B (0, a, 0) (b, 0, 0))
      (fun a a' => by simpa using hadd₁ (0, a, 0) (0, a', 0) (b, 0, 0)) ht1
      (fun a => by simpa using hT 1 t one_ne_zero ht0 (0, a, 0) (b, 0, 0)) a
  have c13 : ∀ a b : K, B (a, 0, 0) (0, 0, b) = 1 := by
    intro a b
    exact eq_one_of_scale (fun b => B (a, 0, 0) (0, 0, b))
      (fun b b' => by simpa using hadd₂ (a, 0, 0) (0, 0, b) (0, 0, b')) (t := t ^ 2) ht2
      (fun b => by simpa using hT 1 t one_ne_zero ht0 (a, 0, 0) (0, 0, b)) b
  have c31 : ∀ a b : K, B (0, 0, a) (b, 0, 0) = 1 := by
    intro a b
    exact eq_one_of_scale (fun a => B (0, 0, a) (b, 0, 0))
      (fun a a' => by simpa using hadd₁ (0, 0, a) (0, 0, a') (b, 0, 0)) (t := t ^ 2) ht2
      (fun a => by simpa using hT 1 t one_ne_zero ht0 (0, 0, a) (b, 0, 0)) a
  have c23 : ∀ a b : K, B (0, a, 0) (0, 0, b) = 1 := by
    intro a b
    exact eq_one_of_scale (fun a => B (0, a, 0) (0, 0, b))
      (fun a a' => by simpa using hadd₁ (0, a, 0) (0, a', 0) (0, 0, b)) ht1
      (fun a => by simpa using hT t 1 ht0 one_ne_zero (0, a, 0) (0, 0, b)) a
  have c32 : ∀ a b : K, B (0, 0, a) (0, b, 0) = 1 := by
    intro a b
    exact eq_one_of_scale (fun b => B (0, 0, a) (0, b, 0))
      (fun b b' => by simpa using hadd₂ (0, 0, a) (0, b, 0) (0, b', 0)) ht1
      (fun b => by simpa using hT t 1 ht0 one_ne_zero (0, 0, a) (0, b, 0)) b
  have c22 : ∀ a b : K, B (0, a, 0) (0, b, 0) = 1 := by
    intro a b
    exact eq_one_of_scalar_invariant (F := K) (V := K) h5 (fun a b => B (0, a, 0) (0, b, 0))
      (fun x x' y => by simpa using hadd₁ (0, x, 0) (0, x', 0) (0, y, 0))
      (fun x y y' => by simpa using hadd₂ (0, x, 0) (0, y, 0) (0, y', 0))
      (fun s hs x y => by simpa using hT s 1 hs one_ne_zero (0, x, 0) (0, y, 0)) a b
  have hW' : ∀ a b : K, B (0, 0, a) (0, 0, b) = B (a, 0, 0) (b, 0, 0) := fun a b => by
    simpa using hW (a, 0, 0) (b, 0, 0)
  have hG' : ∀ a b : K, B (a, a, a) (b, b, b) = B (0, 0, a) (0, 0, b) := fun a b => by
    simpa using hG (0, 0, a) (0, 0, b)
  have c11 : ∀ a b : K, B (a, 0, 0) (b, 0, 0) = 1 := by
    intro a b
    have h := hG' a b
    rw [hL, hR (a, 0, 0), hR (0, a, 0), hR (0, 0, a)] at h
    simp only [c12, c13, c21, c22, c23, c31, c32, mul_one, one_mul] at h
    simpa using h
  have c33 : ∀ a b : K, B (0, 0, a) (0, 0, b) = 1 := fun a b => by rw [hW', c11]
  intro u u'
  rw [hL, hR (u.1, 0, 0), hR (0, u.2.1, 0), hR (0, 0, u.2.2)]
  simp only [c11, c12, c13, c21, c22, c23, c31, c32, c33, mul_one]

end CFSG.ClassicalInvolution.ModelFacts.OddCover
