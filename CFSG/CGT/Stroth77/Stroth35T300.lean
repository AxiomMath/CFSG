module

public import CFSG.CGT.Stroth77.Stroth3FormII
public import CFSG.CGT.Stroth77.Section42CoreT300

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)
open Stroth42Core

namespace Type300

variable {n : ℕ}

theorem ofInt_apply_zero_eq_zero_iff (x : Fin 3 → ℤ) :
    (Torus.ofInt (StrothTypeIndex.t300 n).k x) 0 = 0 ↔ (2 : ℤ) ^ n ∣ x 0 := by
  rw [Torus.ofInt_apply, ZMod.intCast_zmod_eq_zero_iff_dvd, t300_k, Nat.cast_pow,
    Nat.cast_ofNat]

theorem inW_ofInt_iff (x : Fin 3 → ℤ) : InW (Torus.ofInt (StrothTypeIndex.t300 n).k x) ↔
    (2 : ℤ) ^ n ∣ x 0 ∧ (2 : ℤ) ^ n ∣ 2 * x 1 ∧ (2 : ℤ) ^ n ∣ 2 * x 2 := by
  rw [InW, ofInt_apply_zero_eq_zero_iff, ← Torus.ofInt_add, t300_ofInt_eq_zero_iff]
  simp only [Pi.add_apply, ← two_mul]
  exact ⟨fun ⟨h0, _, h1, h2⟩ => ⟨h0, h1, h2⟩,
    fun ⟨h0, h1, h2⟩ => ⟨h0, dvd_mul_of_dvd_right h0 2, h1, h2⟩⟩

theorem val_intCast_mod_two (hn : 1 ≤ n) (X : ℤ) :
    (((X : ZMod (2 ^ (StrothTypeIndex.t300 n).k 0)).val % 2 : ℕ) : ℤ) = X % 2 := by
  rw [Int.natCast_mod, ZMod.val_intCast]
  push_cast
  exact Int.emod_emod_of_dvd X (dvd_pow_self 2 (by rw [t300_k]; omega))

theorem two_pow_dvd_two_pow_pred_mul_iff (hn : 1 ≤ n) (z : ℤ) :
    (2 : ℤ) ^ n ∣ 2 ^ (n - 1) * z ↔ 2 ∣ z := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  exact mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)

theorem om300_add (ε ε' : Fin 3 → ℤ) : om300 n ε + om300 n ε' = om300 n (ε + ε') := by
  rw [om300, om300, om300, ← Torus.ofInt_add]
  congr 1
  funext i
  simp only [Pi.add_apply]
  ring

theorem eq_om300_of_add_self (hn : 1 ≤ n) {v : Torus (StrothTypeIndex.t300 n).k}
    (hv : v + v = 0) : ∃ ε : Fin 3 → ℤ, (∀ i, ε i = 0 ∨ ε i = 1) ∧ v = om300 n ε := by
  have h2 : (2 : ℤ) • v = 0 := by rw [two_zsmul]; exact hv
  obtain ⟨ε, hε, rfl⟩ :=
    (Torus.two_zsmul_eq_zero_iff (fun i => by rw [t300_k]; exact hn) v).mp h2
  refine ⟨ε, hε, ?_⟩
  funext i
  simp [om300, t300_k]

theorem om300_apply_zero_eq_zero_iff (hn : 1 ≤ n) (ε : Fin 3 → ℤ) :
    (om300 n ε) 0 = 0 ↔ 2 ∣ ε 0 := by
  have h : (om300 n ε) 0 = 0 ↔ (2 : ℤ) ^ n ∣ ε 0 * 2 ^ (n - 1) :=
    ofInt_apply_zero_eq_zero_iff (n := n) (fun i => ε i * 2 ^ (n - 1))
  rw [h, mul_comm]
  exact two_pow_dvd_two_pow_pred_mul_iff hn _

theorem classify (hn : 1 ≤ n)
    (δ : Torus (StrothTypeIndex.t300 n).k →+ Torus (StrothTypeIndex.t300 n).k)
    (hU : ∀ x, δ ((StrothTypeIndex.t300 n).action.φuv x) =
      (StrothTypeIndex.t300 n).action.φuv (δ x))
    (hT : ∀ x, δ ((StrothTypeIndex.t300 n).action.φt x) =
      (StrothTypeIndex.t300 n).action.φt (δ x))
    (h2 : ∀ x, x + x = 0 → δ x = x) (hinv : ∀ x, δ (δ x) = x) :
    ∃ α : ℤ, Odd α ∧ ∃ w, InW w ∧ ∀ x, δ x = α • x + (x 0).val • w := by
  obtain ⟨y, hy⟩ := Torus.exists_ofInt (δ (Torus.ofInt (StrothTypeIndex.t300 n).k ![1, 0, 0]))
  have c1 : Torus.ofInt (StrothTypeIndex.t300 n).k ![0, 1, 0] =
      (StrothTypeIndex.t300 n).action.φt (Torus.ofInt _ ![1, 0, 0]) - Torus.ofInt _ ![1, 0, 0] := by
    rw [t300_φt, ← Torus.ofInt_sub]
    congr 1
    funext i
    fin_cases i <;> simp
  have c2 : Torus.ofInt (StrothTypeIndex.t300 n).k ![0, 0, 1] =
      (-2 : ℤ) • Torus.ofInt _ ![1, 0, 0] -
        (StrothTypeIndex.t300 n).action.φuv (Torus.ofInt _ ![1, 0, 0]) -
        (StrothTypeIndex.t300 n).action.φt (Torus.ofInt _ ![1, 0, 0]) := by
    rw [t300_φuv, t300_φt, ← Torus.ofInt_zsmul, ← Torus.ofInt_sub, ← Torus.ofInt_sub]
    congr 1
    funext i
    fin_cases i <;> simp
  have d1 : δ (Torus.ofInt _ ![0, 1, 0]) = Torus.ofInt (StrothTypeIndex.t300 n).k
      ![-4 * y 2, y 0 - 2 * y 1 - 2 * y 2, -2 * y 2] := by
    rw [c1, map_sub, hT, ← hy, t300_φt, ← Torus.ofInt_sub]
    congr 1
    funext i
    fin_cases i <;> simp <;> ring
  have d2 : δ (Torus.ofInt _ ![0, 0, 1]) = Torus.ofInt (StrothTypeIndex.t300 n).k
      ![-4 * y 1, -2 * y 1, y 0 - 2 * y 1 - 2 * y 2] := by
    rw [c2, map_sub, map_sub, map_zsmul, hU, hT, ← hy, t300_φuv, t300_φt, ← Torus.ofInt_zsmul,
      ← Torus.ofInt_sub, ← Torus.ofInt_sub]
    congr 1
    funext i
    fin_cases i <;>
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta,
        Fin.mk_one, Fin.reduceFinMk] <;> ring
  have hδ : ∀ x : Fin 3 → ℤ, δ (Torus.ofInt _ x) = Torus.ofInt (StrothTypeIndex.t300 n).k
      ![x 0 * y 0 - 4 * x 1 * y 2 - 4 * x 2 * y 1,
        x 0 * y 1 + x 1 * (y 0 - 2 * y 1 - 2 * y 2) - 2 * x 2 * y 1,
        x 0 * y 2 - 2 * x 1 * y 2 + x 2 * (y 0 - 2 * y 1 - 2 * y 2)] := by
    intro x
    have hx : Torus.ofInt (StrothTypeIndex.t300 n).k x = x 0 • Torus.ofInt _ ![1, 0, 0] +
        x 1 • Torus.ofInt _ ![0, 1, 0] + x 2 • Torus.ofInt _ ![0, 0, 1] := by
      rw [← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_add,
        ← Torus.ofInt_add]
      congr 1
      funext i
      fin_cases i <;> simp
    rw [hx, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, ← hy, d1, d2,
      ← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_add,
      ← Torus.ofInt_add]
    congr 1
    funext i
    fin_cases i <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta,
        Fin.mk_one, Fin.reduceFinMk] <;> ring
  have hΩ := h2 (om300 n ![1, 0, 0]) (om300_add_self hn _)
  rw [om300, hδ, t300_ofInt_eq_iff] at hΩ
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hΩ
  obtain ⟨⟨k0, hk0⟩, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := hΩ
  have hA : 2 ∣ 1 - y 0 :=
    (two_pow_dvd_two_pow_pred_mul_iff hn _).mp ⟨k0, by linear_combination hk0⟩
  have hB : 2 ∣ -y 1 :=
    (two_pow_dvd_two_pow_pred_mul_iff hn _).mp ⟨k1, by linear_combination hk1⟩
  have hC : 2 ∣ -y 2 :=
    (two_pow_dvd_two_pow_pred_mul_iff hn _).mp ⟨k2, by linear_combination hk2⟩
  have hii := hinv (Torus.ofInt _ ![1, 0, 0])
  rw [← hy, hδ, t300_ofInt_eq_iff] at hii
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hii
  obtain ⟨-, ⟨j1, hj1⟩, ⟨j2, hj2⟩⟩ := hii
  have hB2 : (2 : ℤ) ^ n ∣ 2 * y 1 := by
    have hc : IsCoprime ((2 : ℤ) ^ n) (y 0 - y 1 - 2 * y 2) :=
      (Int.isCoprime_two_left.mpr (Int.odd_iff.mpr (by omega))).pow_left
    exact hc.dvd_of_dvd_mul_right ⟨-j1, by linear_combination -hj1⟩
  have hC2 : (2 : ℤ) ^ n ∣ 2 * y 2 := by
    have hc : IsCoprime ((2 : ℤ) ^ n) (y 0 - 2 * y 1 - y 2) :=
      (Int.isCoprime_two_left.mpr (Int.odd_iff.mpr (by omega))).pow_left
    exact hc.dvd_of_dvd_mul_right ⟨-j2, by linear_combination -hj2⟩
  obtain ⟨m1, hm1⟩ := hB2
  obtain ⟨m2, hm2⟩ := hC2
  have hw : InW (Torus.ofInt (StrothTypeIndex.t300 n).k ![0, y 1, y 2]) := by
    rw [inW_ofInt_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    exact ⟨dvd_zero _, ⟨m1, hm1⟩, ⟨m2, hm2⟩⟩
  refine ⟨y 0, Int.odd_iff.mpr (by omega), _, hw, fun x => ?_⟩
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt x
  have hpar : (v 0) • Torus.ofInt (StrothTypeIndex.t300 n).k ![0, y 1, y 2] =
      ((((v 0 : ℤ) : ZMod (2 ^ (StrothTypeIndex.t300 n).k 0)).val : ℕ) : ℤ) •
        Torus.ofInt (StrothTypeIndex.t300 n).k ![0, y 1, y 2] := by
    have hv := val_intCast_mod_two hn (v 0)
    obtain ⟨j, hj⟩ : ∃ j : ℤ,
        ((((v 0 : ℤ) : ZMod (2 ^ (StrothTypeIndex.t300 n).k 0)).val : ℕ) : ℤ) = v 0 + 2 * j := by
      refine ⟨(((((v 0 : ℤ) : ZMod (2 ^ (StrothTypeIndex.t300 n).k 0)).val : ℕ) : ℤ) - v 0) / 2,
        ?_⟩
      omega
    rw [hj, add_zsmul, mul_comm (2 : ℤ) j, mul_zsmul, two_zsmul, hw.2, zsmul_zero, add_zero]
  rw [Torus.ofInt_apply, ← natCast_zsmul, ← hpar, hδ, ← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul,
    ← Torus.ofInt_add, t300_ofInt_eq_iff]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  exact ⟨⟨2 * v 1 * m2 + 2 * v 2 * m1, by linear_combination (2 * v 1) * hm2 + (2 * v 2) * hm1⟩,
    ⟨v 1 * m1 + v 1 * m2 + v 2 * m1, by linear_combination v 1 * hm1 + v 1 * hm2 + v 2 * hm1⟩,
    ⟨v 1 * m2 + v 2 * m1 + v 2 * m2, by linear_combination v 1 * hm2 + v 2 * hm1 + v 2 * hm2⟩⟩

theorem even_uv (hn : 1 ≤ n) (r : Torus (StrothTypeIndex.t300 n).k)
    (h : r + (StrothTypeIndex.t300 n).action.φuv r = 0) : (r 0).val % 2 = 0 := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt r
  rw [t300_φuv, ← Torus.ofInt_add, t300_ofInt_eq_zero_iff] at h
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h
  have h2 : (2 : ℤ) ∣ x 1 + (-x 0 + x 1 + 2 * x 2) := dvd_trans (dvd_pow_self 2 (by omega)) h.2.1
  have hv := val_intCast_mod_two hn (x 0)
  rw [Torus.ofInt_apply]
  omega

theorem even_t (hn : 1 ≤ n) (r : Torus (StrothTypeIndex.t300 n).k)
    (h : r + (StrothTypeIndex.t300 n).action.φt r = 0) : (r 0).val % 2 = 0 := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt r
  rw [t300_φt, ← Torus.ofInt_add, t300_ofInt_eq_zero_iff] at h
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h
  have h2 : (2 : ℤ) ∣ x 1 + (x 0 - x 1 - 2 * x 2) := dvd_trans (dvd_pow_self 2 (by omega)) h.2.1
  have hv := val_intCast_mod_two hn (x 0)
  rw [Torus.ofInt_apply]
  omega

theorem fixed (z : Torus (StrothTypeIndex.t300 n).k)
    (hU : (StrothTypeIndex.t300 n).action.φuv z = z)
    (hT : (StrothTypeIndex.t300 n).action.φt z = z) : InW z := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt z
  rw [t300_φuv, t300_ofInt_eq_iff] at hU
  rw [t300_φt, t300_ofInt_eq_iff] at hT
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hU hT
  obtain ⟨-, ⟨u1, hu1⟩, ⟨u2, hu2⟩⟩ := hU
  obtain ⟨-, -, ⟨t2, ht2⟩⟩ := hT
  rw [inW_ofInt_iff]
  exact ⟨⟨u1 + t2, by linear_combination hu1 + ht2⟩,
    ⟨u1 + t2 - u2, by linear_combination hu1 + ht2 - hu2⟩, ⟨t2, by linear_combination ht2⟩⟩

theorem par_uv (hn : 1 ≤ n) (x : Torus (StrothTypeIndex.t300 n).k) :
    (((StrothTypeIndex.t300 n).action.φuv x) 0).val % 2 = (x 0).val % 2 := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt x
  rw [t300_φuv]
  simp only [Torus.ofInt_apply, Matrix.cons_val_zero]
  have h1 := val_intCast_mod_two hn (-3 * v 0 + 4 * v 1 + 4 * v 2)
  have h2 := val_intCast_mod_two hn (v 0)
  omega

theorem par_t (hn : 1 ≤ n) (x : Torus (StrothTypeIndex.t300 n).k) :
    (((StrothTypeIndex.t300 n).action.φt x) 0).val % 2 = (x 0).val % 2 := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt x
  rw [t300_φt]
  simp only [Torus.ofInt_apply, Matrix.cons_val_zero]
  have h1 := val_intCast_mod_two hn (v 0 - 4 * v 2)
  have h2 := val_intCast_mod_two hn (v 0)
  omega

theorem par_u (x : Torus (StrothTypeIndex.t300 n).k) :
    (((StrothTypeIndex.t300 n).action.φu x) 0).val % 2 = (x 0).val % 2 := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt x
  rw [t300_φu]
  simp only [Torus.ofInt_apply, Matrix.cons_val_zero]

theorem par_ρ (hn : 1 ≤ n) (x : Torus (StrothTypeIndex.t300 n).k) :
    (((StrothTypeIndex.t300 n).action.φρ x) 0).val % 2 = (x 0).val % 2 := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt x
  rw [t300_φρ]
  simp only [Torus.ofInt_apply, Matrix.cons_val_zero]
  have h1 := val_intCast_mod_two hn (v 0 - 4 * v 2)
  have h2 := val_intCast_mod_two hn (v 0)
  omega

theorem W_uv (w : Torus (StrothTypeIndex.t300 n).k) (hw : InW w) :
    (StrothTypeIndex.t300 n).action.φuv w = w := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
  obtain ⟨⟨k0, e0⟩, ⟨k1, e1⟩, ⟨k2, e2⟩⟩ := (inW_ofInt_iff x).mp hw
  rw [t300_φuv, t300_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  exact ⟨⟨4 * k0 - 2 * k1 - 2 * k2, by linear_combination 4 * e0 - 2 * e1 - 2 * e2⟩,
    ⟨k0 - k2, by linear_combination e0 - e2⟩, ⟨k0 - k1, by linear_combination e0 - e1⟩⟩

theorem W_t (w : Torus (StrothTypeIndex.t300 n).k) (hw : InW w) :
    (StrothTypeIndex.t300 n).action.φt w = w := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
  obtain ⟨⟨k0, e0⟩, ⟨k1, e1⟩, ⟨k2, e2⟩⟩ := (inW_ofInt_iff x).mp hw
  rw [t300_φt, t300_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  exact ⟨⟨2 * k2, by linear_combination 2 * e2⟩,
    ⟨-k0 + k1 + k2, by linear_combination -e0 + e1 + e2⟩, ⟨k2, by linear_combination e2⟩⟩

theorem W_u (w : Torus (StrothTypeIndex.t300 n).k) (hw : InW w) :
    ((StrothTypeIndex.t300 n).action.φu w) 0 = 0 := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
  obtain ⟨h0, -, -⟩ := (inW_ofInt_iff x).mp hw
  rw [t300_φu, ofInt_apply_zero_eq_zero_iff]
  simpa only [Matrix.cons_val_zero] using h0

theorem W_ρ (w : Torus (StrothTypeIndex.t300 n).k) (hw : InW w) :
    ((StrothTypeIndex.t300 n).action.φρ w) 0 = 0 := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
  obtain ⟨⟨k0, e0⟩, -, ⟨k2, e2⟩⟩ := (inW_ofInt_iff x).mp hw
  rw [t300_φρ, ofInt_apply_zero_eq_zero_iff]
  simp only [Matrix.cons_val_zero]
  exact ⟨k0 - 2 * k2, by linear_combination e0 - 2 * e2⟩

theorem W_fpf (w : Torus (StrothTypeIndex.t300 n).k) (hw : InW w)
    (hfix : (StrothTypeIndex.t300 n).action.φρ w = w) : w = 0 := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
  obtain ⟨⟨k0, e0⟩, -, ⟨k2, e2⟩⟩ := (inW_ofInt_iff x).mp hw
  rw [t300_φρ, t300_ofInt_eq_iff] at hfix
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hfix
  obtain ⟨-, ⟨f1, hf1⟩, ⟨f2, hf2⟩⟩ := hfix
  rw [t300_ofInt_eq_zero_iff]
  exact ⟨⟨k0, e0⟩, ⟨-f2 + k2, by linear_combination -hf2 + e2⟩,
    ⟨f1 + f2 - k2, by linear_combination hf1 + hf2 - e2⟩⟩

theorem sq_W (v : Torus (StrothTypeIndex.t300 n).k) (hv2 : v + v = 0)
    (hρ : (StrothTypeIndex.t300 n).action.φρ ((StrothTypeIndex.t300 n).action.φρ v) =
      v + (StrothTypeIndex.t300 n).action.φρ v) : v 0 = 0 := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [← Torus.ofInt_add, t300_ofInt_eq_zero_iff] at hv2
  simp only [Pi.add_apply] at hv2
  obtain ⟨-, ⟨a1, ha1⟩, ⟨a2, ha2⟩⟩ := hv2
  simp only [t300_φρ, ← Torus.ofInt_add] at hρ
  rw [t300_ofInt_eq_iff] at hρ
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hρ
  obtain ⟨⟨b0, hb0⟩, -, -⟩ := hρ
  rw [ofInt_apply_zero_eq_zero_iff]
  exact ⟨b0 - 2 * a1 + 2 * a2, by linear_combination hb0 - 2 * ha1 + 2 * ha2⟩

theorem W_orbit (hn : 1 ≤ n) (v w : Torus (StrothTypeIndex.t300 n).k) (hv : InW v) (hv0 : v ≠ 0)
    (hw : InW w) :
    w = 0 ∨ w = v ∨ w = (StrothTypeIndex.t300 n).action.φρ v ∨
      w = v + (StrothTypeIndex.t300 n).action.φρ v := by
  obtain ⟨ε, hε, rfl⟩ := eq_om300_of_add_self hn hv.2
  obtain ⟨η, hη, rfl⟩ := eq_om300_of_add_self hn hw.2
  have hε0 := (om300_apply_zero_eq_zero_iff hn ε).mp hv.1
  have hη0 := (om300_apply_zero_eq_zero_iff hn η).mp hw.1
  have h1 := hε 1
  have h2 := hε 2
  have h3 := hη 1
  have h4 := hη 2
  obtain ⟨ε1, ε2, rfl⟩ : ∃ ε1 ε2 : ℤ, ε = ![0, ε1, ε2] :=
    ⟨ε 1, ε 2, by funext i; fin_cases i <;> simp; rcases hε 0 with h | h <;> omega⟩
  obtain ⟨η1, η2, rfl⟩ : ∃ η1 η2 : ℤ, η = ![0, η1, η2] :=
    ⟨η 1, η 2, by funext i; fin_cases i <;> simp; rcases hη 0 with h | h <;> omega⟩
  simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    at h1 h2 h3 h4
  rw [← om300_zero, Ne, om300_eq_iff hn] at hv0
  rw [t300_φρ_om, om300_add, ← om300_zero, om300_eq_iff hn, om300_eq_iff hn, om300_eq_iff hn,
    om300_eq_iff hn]
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
    rcases h4 with rfl | rfl <;> revert hv0 <;> decide

theorem vFacts (hn : 2 ≤ n) : VFacts (StrothTypeIndex.t300 n) where
  two_le := by rw [t300_k]; exact hn
  classify := classify (by omega)
  even_uv := even_uv (by omega)
  even_t := even_t (by omega)
  fixed := fixed
  par_uv := par_uv (by omega)
  par_t := par_t (by omega)
  par_u := par_u
  par_ρ := par_ρ (by omega)
  W_uv := W_uv
  W_t := W_t
  W_u := W_u
  W_ρ := W_ρ
  W_fpf := W_fpf
  sq_W := sq_W
  W_orbit := W_orbit (by omega)

theorem killFact : KillFact (StrothTypeIndex.t300 n) := by
  intro ruv rt d0 h1 h2 h3 h4 h5
  obtain ⟨a, rfl⟩ := Torus.exists_ofInt ruv
  obtain ⟨b, rfl⟩ := Torus.exists_ofInt rt
  obtain ⟨c, rfl⟩ := Torus.exists_ofInt d0
  simp only [t300_φuv, t300_φt, t300_φρ, ← Torus.ofInt_add, ← Torus.ofInt_sub] at h1 h2 h3 h4 h5
  rw [t300_ofInt_eq_zero_iff] at h1 h2
  rw [t300_ofInt_eq_iff] at h3 h4 h5
  simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h1 h2 h3 h4 h5
  obtain ⟨-, ⟨k11, e11⟩, -⟩ := h1
  obtain ⟨⟨k20, e20⟩, ⟨k21, e21⟩, -⟩ := h2
  obtain ⟨⟨k30, e30⟩, -, ⟨k32, e32⟩⟩ := h3
  obtain ⟨⟨k40, e40⟩, ⟨k41, e41⟩, ⟨k42, e42⟩⟩ := h4
  obtain ⟨⟨k50, e50⟩, ⟨k51, e51⟩, ⟨k52, e52⟩⟩ := h5
  refine ⟨Torus.ofInt _ ![-b 1 + 2 * c 1, -c 0 + 2 * c 1 + c 2, -2 * c 0 + 3 * c 1 + 3 * c 2],
    ?_, ?_⟩
  · simp only [t300_φuv, ← Torus.ofInt_add, ← Torus.ofInt_sub]
    rw [inW_ofInt_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact ⟨⟨-k21 + k30 + k32 + 3 * k40 - k42 - k50 - k51 + k52,
        by linear_combination -e21 + e30 + e32 + 3 * e40 - e42 - e50 - e51 + e52⟩,
      ⟨k11 - k20 + k30 + k32 + 2 * k40 - k50,
        by linear_combination e11 - e20 + e30 + e32 + 2 * e40 - e50⟩,
      ⟨k32 + k40, by linear_combination e32 + e40⟩⟩
  · simp only [t300_φt, ← Torus.ofInt_add, ← Torus.ofInt_sub]
    rw [inW_ofInt_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact ⟨⟨-k40 + 4 * k51, by linear_combination -e40 + 4 * e51⟩,
      ⟨-k11 + k20 - k30 - k32 - 2 * k40 - k42 + k50 + 3 * k51 - k52,
        by linear_combination -e11 + e20 - e30 - e32 - 2 * e40 - e42 + e50 + 3 * e51 - e52⟩,
      ⟨-2 * k40 + 2 * k41 + k42 + 3 * k51 + k52,
        by linear_combination -2 * e40 + 2 * e41 + e42 + 3 * e51 + e52⟩⟩

end Type300

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}

theorem two_le_of_t300 {n : ℕ} {dD : StrothWeakTypeData D (StrothTypeIndex.t300 n)}
    (h : F.IsD D dD) : 2 ≤ n := by
  have hle := Subgroup.card_le_of_le h.A_le
  rw [F.dA.card, dD.card, t300_k, t300_k, t300_k] at hle
  have h5 : (StrothTypeIndex.t100 1).k 0 + (StrothTypeIndex.t100 1).k 1 +
      (StrothTypeIndex.t100 1).k 2 = 5 := rfl
  rw [h5] at hle
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  omega

theorem stroth_3_5 {n : ℕ} {dD : StrothWeakTypeData D (StrothTypeIndex.t300 n)} (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
        F.dA.L ≤ Subgroup.normalizer
          ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
        Nat.card D < Nat.card X :=
  h.stroth_form_ii (Type300.vFacts h.two_le_of_t300) Type300.killFact hns

end StrothFrame.IsD

end CFSG.CGT.Stroth77
