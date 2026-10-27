module

public import CFSG.CGT.Stroth77.Section42CoreSplit

public section

namespace CFSG.CGT.Stroth77

namespace Stroth32Cent

open Stroth42Core

variable {m : ℕ}

theorem zsmul_eq_of_even_sub {M : Type*} [AddCommGroup M] {X : M} (hX : X + X = 0) {z z' : ℤ}
    (h : Even (z - z')) : z • X = z' • X := by
  obtain ⟨w, hw⟩ := h
  rw [show z = z' + w + w by linarith, add_zsmul, add_zsmul, add_assoc, ← add_zsmul,
    ← two_mul, mul_comm, mul_zsmul, two_zsmul, hX, zsmul_zero, add_zero]

theorem odd_of_fix {M : Type*} [AddCommGroup M] (hm : 1 ≤ m) (θ : M →+ M) {e A B : M}
    (hA : A + A = 0) (hB : B + B = 0) (hfix : θ ((2 ^ m : ℤ) • e) = (2 ^ m : ℤ) • e)
    (hord : ∀ z : ℤ, z • e = 0 → (2 : ℤ) ^ (m + 1) ∣ z) {α s r : ℤ}
    (h : θ e = α • e + s • A + r • B) : Odd α := by
  have hev : Even ((2 : ℤ) ^ m) := ⟨2 ^ (m - 1), by
    rw [← two_mul, ← pow_succ']; congr 1; omega⟩
  have hsA : ((2 ^ m : ℤ) * s) • A = (0 : ℤ) • A :=
    zsmul_eq_of_even_sub hA (by rw [sub_zero]; exact hev.mul_right s)
  have hrB : ((2 ^ m : ℤ) * r) • B = (0 : ℤ) • B :=
    zsmul_eq_of_even_sub hB (by rw [sub_zero]; exact hev.mul_right r)
  rw [map_zsmul, h, smul_add, smul_add, smul_smul, smul_smul, smul_smul, hsA, hrB, zero_smul,
    zero_smul, add_zero, add_zero] at hfix
  have hz : ((2 ^ m : ℤ) * α - 2 ^ m) • e = 0 := by
    rw [sub_eq_add_neg, add_zsmul, hfix, neg_zsmul, add_neg_cancel]
  obtain ⟨w, hw⟩ := hord _ hz
  have h2 : (2 : ℤ) ^ m * (α - 1) = 2 ^ m * (2 * w) := by
    rw [mul_sub, mul_one, hw, pow_succ]; ring
  have := mul_left_cancel₀ (pow_ne_zero m (two_ne_zero : (2 : ℤ) ≠ 0)) h2
  exact ⟨w, by linarith⟩

theorem two_pow_dvd_of_dvd_two_mul {x : ℤ} (h : (2 : ℤ) ^ (m + 1) ∣ 2 * x) : (2 : ℤ) ^ m ∣ x := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) (by rw [hc, pow_succ]; ring)⟩

theorem eq_of_twist₁ {y : Torus (StrothTypeIndex.t100 m).k}
    (h : (StrothTypeIndex.t100 m).action.φuv y = y) :
    ∃ α s r : ℤ, y = Torus.ofInt _ ![α, α + 2 ^ m * s, α + 2 ^ m * r] := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt y
  rw [t100_φuv, t100_ofInt_eq_iff] at h
  obtain ⟨-, h1, h2⟩ := h
  obtain ⟨r, hr⟩ := two_pow_dvd_of_dvd_two_mul (m := m) (x := v 0 - v 2)
    (by convert h1 using 1; simp; ring)
  obtain ⟨s, hs⟩ := two_pow_dvd_of_dvd_two_mul (m := m) (x := v 0 - v 1)
    (by convert h2 using 1; simp; ring)
  refine ⟨v 0, -s, -r, ?_⟩
  congr 1
  funext i
  fin_cases i <;> simp <;> linarith

theorem eq_of_twist₂ {y : Torus (StrothTypeIndex.t100 m).k}
    (huv : (StrothTypeIndex.t100 m).action.φuv y = -y)
    (ht : (StrothTypeIndex.t100 m).action.φt y = y) :
    ∃ α s r : ℤ, y = Torus.ofInt _ ![α, α + 2 ^ m * s, 2 ^ m * r] := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt y
  rw [t100_φuv, ← Torus.ofInt_neg, t100_ofInt_eq_iff] at huv
  rw [t100_φt, t100_ofInt_eq_iff] at ht
  obtain ⟨-, h1, -⟩ := huv
  obtain ⟨-, -, h2⟩ := ht
  obtain ⟨r, hr⟩ := two_pow_dvd_of_dvd_two_mul (m := m) (x := v 2)
    (by convert h2 using 1; simp; ring)
  obtain ⟨s, hs⟩ := two_pow_dvd_of_dvd_two_mul (m := m) (x := v 0 - v 1 - v 2)
    (by convert h1 using 1; simp; ring)
  refine ⟨v 0, -r - s, r, ?_⟩
  congr 1
  funext i
  fin_cases i <;> simp <;> linarith

theorem eq_of_twist₃ {y : Torus (StrothTypeIndex.t100 m).k}
    (huv : (StrothTypeIndex.t100 m).action.φuv y = -y)
    (ht : (StrothTypeIndex.t100 m).action.φt y = -y) :
    ∃ α s r : ℤ, y = Torus.ofInt _ ![α, 2 ^ m * s, α + 2 ^ m * r] := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt y
  rw [t100_φuv, ← Torus.ofInt_neg, t100_ofInt_eq_iff] at huv
  rw [t100_φt, ← Torus.ofInt_neg, t100_ofInt_eq_iff] at ht
  obtain ⟨-, h1, -⟩ := huv
  obtain ⟨-, h2, -⟩ := ht
  obtain ⟨r, hr⟩ := two_pow_dvd_of_dvd_two_mul (m := m) (x := v 2 - v 0)
    (by convert h2 using 1; simp; ring)
  obtain ⟨s, hs⟩ := two_pow_dvd_of_dvd_two_mul (m := m) (x := v 0 - v 1 - v 2)
    (by convert h1 using 1; simp; ring)
  refine ⟨v 0, -r - s, r, ?_⟩
  congr 1
  funext i
  fin_cases i <;> simp <;> linarith

theorem φuv_cab : (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ ![1, 1, 1]) =
    Torus.ofInt _ ![1, 1, 1] := by
  rw [t100_φuv]; congr 1

theorem φuv_ca : (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ ![1, 1, 0]) =
    -Torus.ofInt _ ![1, 1, 0] := by
  rw [t100_φuv, ← Torus.ofInt_neg]; congr 1; funext i; fin_cases i <;> simp

theorem φt_ca : (StrothTypeIndex.t100 m).action.φt (Torus.ofInt _ ![1, 1, 0]) =
    Torus.ofInt _ ![1, 1, 0] := by
  rw [t100_φt]; congr 1

theorem φuv_cb : (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ ![1, 0, 1]) =
    -Torus.ofInt _ ![1, 0, 1] := by
  rw [t100_φuv, ← Torus.ofInt_neg]; congr 1; funext i; fin_cases i <;> simp

theorem φt_cb : (StrothTypeIndex.t100 m).action.φt (Torus.ofInt _ ![1, 0, 1]) =
    -Torus.ofInt _ ![1, 0, 1] := by
  rw [t100_φt, ← Torus.ofInt_neg]; congr 1; funext i; fin_cases i <;> simp

theorem A_add_self : Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 2 ^ m, 0] +
    Torus.ofInt _ ![0, 2 ^ m, 0] = 0 := by
  rw [← Torus.ofInt_add, t100_ofInt_eq_zero_iff]
  exact ⟨by simp, ⟨1, by simp [pow_succ]; ring⟩, by simp⟩

theorem B_add_self : Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 0, 2 ^ m] +
    Torus.ofInt _ ![0, 0, 2 ^ m] = 0 := by
  rw [← Torus.ofInt_add, t100_ofInt_eq_zero_iff]
  exact ⟨by simp, by simp, ⟨1, by simp [pow_succ]; ring⟩⟩

theorem two_pow_zsmul_add_self (e : Fin 3 → ℤ) (he : ∀ i, e i = 0 ∨ e i = 1) :
    (2 ^ m : ℤ) • Torus.ofInt (StrothTypeIndex.t100 m).k e +
      (2 ^ m : ℤ) • Torus.ofInt (StrothTypeIndex.t100 m).k e = 0 := by
  rw [← Torus.ofInt_zsmul, ← Torus.ofInt_add, t100_ofInt_eq_zero_iff]
  have hd : ∀ i, (2 : ℤ) ^ (m + 1) ∣ (2 ^ m • e + 2 ^ m • e) i := fun i => by
    rcases he i with h | h <;> simp [h, pow_succ]; exact ⟨1, by ring⟩
  exact ⟨dvd_trans (pow_dvd_pow 2 (Nat.le_succ m)) (hd 0), hd 1, hd 2⟩

theorem decomp₁ (α s r : ℤ) :
    Torus.ofInt (StrothTypeIndex.t100 m).k ![α, α + 2 ^ m * s, α + 2 ^ m * r] =
      α • Torus.ofInt _ ![1, 1, 1] + s • Torus.ofInt _ ![0, 2 ^ m, 0] +
        r • Torus.ofInt _ ![0, 0, 2 ^ m] := by
  rw [← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_add,
    ← Torus.ofInt_add]
  congr 1; funext i; fin_cases i <;> simp <;> ring

theorem decomp₂ (α s r : ℤ) :
    Torus.ofInt (StrothTypeIndex.t100 m).k ![α, α + 2 ^ m * s, 2 ^ m * r] =
      α • Torus.ofInt _ ![1, 1, 0] + s • Torus.ofInt _ ![0, 2 ^ m, 0] +
        r • Torus.ofInt _ ![0, 0, 2 ^ m] := by
  rw [← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_add,
    ← Torus.ofInt_add]
  congr 1; funext i; fin_cases i <;> simp <;> ring

theorem decomp₃ (α s r : ℤ) :
    Torus.ofInt (StrothTypeIndex.t100 m).k ![α, 2 ^ m * s, α + 2 ^ m * r] =
      α • Torus.ofInt _ ![1, 0, 1] + s • Torus.ofInt _ ![0, 2 ^ m, 0] +
        r • Torus.ofInt _ ![0, 0, 2 ^ m] := by
  rw [← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_add,
    ← Torus.ofInt_add]
  congr 1; funext i; fin_cases i <;> simp <;> ring

theorem decomp_odd (hm : 1 ≤ m)
    (θ : Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k)
    (hΩ : ∀ x, x + x = 0 → θ x = x) (e : Fin 3 → ℤ) (he : ∀ i, e i = 0 ∨ e i = 1)
    (hord : ∀ z : ℤ, z • Torus.ofInt (StrothTypeIndex.t100 m).k e = 0 → (2 : ℤ) ^ (m + 1) ∣ z)
    {α s r : ℤ} (hθ : θ (Torus.ofInt _ e) = α • Torus.ofInt _ e +
      s • Torus.ofInt _ ![0, 2 ^ m, 0] + r • Torus.ofInt _ ![0, 0, 2 ^ m]) : Odd α :=
  odd_of_fix hm θ A_add_self B_add_self (hΩ _ (two_pow_zsmul_add_self e he)) hord hθ

theorem images (hm : 1 ≤ m)
    (θ : Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k)
    (huv : ∀ x, θ ((StrothTypeIndex.t100 m).action.φuv x) =
      (StrothTypeIndex.t100 m).action.φuv (θ x))
    (ht : ∀ x, θ ((StrothTypeIndex.t100 m).action.φt x) =
      (StrothTypeIndex.t100 m).action.φt (θ x))
    (hΩ : ∀ x, x + x = 0 → θ x = x) :
    (∃ α s r : ℤ, Odd α ∧ θ (Torus.ofInt _ ![1, 1, 1]) = α • Torus.ofInt _ ![1, 1, 1] +
        s • Torus.ofInt _ ![0, 2 ^ m, 0] + r • Torus.ofInt _ ![0, 0, 2 ^ m]) ∧
      (∃ α s r : ℤ, Odd α ∧ θ (Torus.ofInt _ ![1, 1, 0]) = α • Torus.ofInt _ ![1, 1, 0] +
        s • Torus.ofInt _ ![0, 2 ^ m, 0] + r • Torus.ofInt _ ![0, 0, 2 ^ m]) ∧
      (∃ α s r : ℤ, Odd α ∧ θ (Torus.ofInt _ ![1, 0, 1]) = α • Torus.ofInt _ ![1, 0, 1] +
        s • Torus.ofInt _ ![0, 2 ^ m, 0] + r • Torus.ofInt _ ![0, 0, 2 ^ m]) := by
  have hord₁ : ∀ e : Fin 3 → ℤ, e 1 = 1 →
      ∀ z : ℤ, z • Torus.ofInt (StrothTypeIndex.t100 m).k e = 0 → (2 : ℤ) ^ (m + 1) ∣ z := by
    intro e he z hz
    rw [← Torus.ofInt_zsmul, t100_ofInt_eq_zero_iff] at hz
    simpa [he] using hz.2.1
  have hord₂ : ∀ e : Fin 3 → ℤ, e 2 = 1 →
      ∀ z : ℤ, z • Torus.ofInt (StrothTypeIndex.t100 m).k e = 0 → (2 : ℤ) ^ (m + 1) ∣ z := by
    intro e he z hz
    rw [← Torus.ofInt_zsmul, t100_ofInt_eq_zero_iff] at hz
    simpa [he] using hz.2.2
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨α, s, r, h⟩ := eq_of_twist₁ (y := θ (Torus.ofInt _ ![1, 1, 1]))
      (by rw [← huv, φuv_cab])
    rw [decomp₁] at h
    exact ⟨α, s, r, decomp_odd hm θ hΩ ![1, 1, 1] (fun i => by fin_cases i <;> simp)
      (hord₁ _ rfl) h, h⟩
  · obtain ⟨α, s, r, h⟩ := eq_of_twist₂ (y := θ (Torus.ofInt _ ![1, 1, 0]))
      (by rw [← huv, φuv_ca, map_neg]) (by rw [← ht, φt_ca])
    rw [decomp₂] at h
    exact ⟨α, s, r, decomp_odd hm θ hΩ ![1, 1, 0] (fun i => by fin_cases i <;> simp)
      (hord₁ _ rfl) h, h⟩
  · obtain ⟨α, s, r, h⟩ := eq_of_twist₃ (y := θ (Torus.ofInt _ ![1, 0, 1]))
      (by rw [← huv, φuv_cb, map_neg]) (by rw [← ht, φt_cb, map_neg])
    rw [decomp₃] at h
    exact ⟨α, s, r, decomp_odd hm θ hΩ ![1, 0, 1] (fun i => by fin_cases i <;> simp)
      (hord₂ _ rfl) h, h⟩

end Stroth32Cent

end CFSG.CGT.Stroth77
