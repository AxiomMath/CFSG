module

public import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CFSG.KS.PK

@[expose] def enc (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => enc w f len + f len * 2 ^ (w * len)

@[expose] def itr (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => f (itr f k x)

@[expose] def fd (w x i : Nat) : Nat := x / 2 ^ (w * i) % 2 ^ w

theorem fd_lt (w x i : Nat) : fd w x i < 2 ^ w := by
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem enc_zero (w : Nat) (f : Nat → Nat) : enc w f 0 = 0 := rfl

theorem enc_succ (w : Nat) (f : Nat → Nat) (len : Nat) :
    enc w f (len + 1) = enc w f len + f len * 2 ^ (w * len) := rfl

theorem enc_congr {w len : Nat} {f g : Nat → Nat} (h : ∀ i < len, f i = g i) :
    enc w f len = enc w g len := by
  induction len with
  | zero => rfl
  | succ n ih =>
    rw [enc_succ, enc_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      h n (Nat.lt_succ_self n)]

theorem enc_lt {w len : Nat} {f : Nat → Nat} (hf : ∀ i < len, f i < 2 ^ w) :
    enc w f len < 2 ^ (w * len) := by
  induction len with
  | zero => rw [enc_zero, Nat.mul_zero, Nat.pow_zero]; exact Nat.zero_lt_one
  | succ n ih =>
    have h1 := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    have h2 := hf n (Nat.lt_succ_self n)
    rw [enc_succ]
    calc enc w f n + f n * 2 ^ (w * n) < 2 ^ (w * n) + f n * 2 ^ (w * n) :=
          Nat.add_lt_add_right h1 _
      _ = (f n + 1) * 2 ^ (w * n) := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      _ ≤ 2 ^ w * 2 ^ (w * n) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h2)
      _ = 2 ^ (w * (n + 1)) := by rw [← Nat.pow_add, Nat.mul_succ, Nat.add_comm]

theorem enc_add (w : Nat) (f : Nat → Nat) (a b : Nat) :
    enc w f (a + b) = enc w f a + enc w (fun i => f (a + i)) b * 2 ^ (w * a) := by
  induction b with
  | zero => rw [Nat.add_zero, enc_zero, Nat.zero_mul, Nat.add_zero]
  | succ n ih =>
    have h1 : enc w f (a + (n + 1)) = enc w f (a + n) + f (a + n) * 2 ^ (w * (a + n)) :=
      enc_succ w f (a + n)
    rw [h1, enc_succ w (fun i => f (a + i)) n, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.add_assoc]

private theorem fd_add_mul_of_lt {w a c j : Nat} (ha : a < 2 ^ (w * j)) :
    fd w (a + c * 2 ^ (w * j)) j = c % 2 ^ w := by
  unfold fd
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem fd_enc {w len : Nat} {f : Nat → Nat} (hf : ∀ i < len, f i < 2 ^ w) {j : Nat}
    (hj : j < len) : fd w (enc w f len) j = f j := by
  obtain ⟨r, rfl⟩ : ∃ r, len = j + 1 + r := ⟨len - (j + 1), by omega⟩
  have hfj : f j < 2 ^ w := hf j hj
  have h1 : enc w f j < 2 ^ (w * j) := enc_lt (fun i hi => hf i (by omega))
  have h2 : enc w f (j + 1 + r) =
      enc w f j + (f j + enc w (fun i => f (j + 1 + i)) r * 2 ^ w) * 2 ^ (w * j) := by
    rw [enc_add, enc_succ]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.add_assoc]
  rw [h2, fd_add_mul_of_lt h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hfj]

theorem fd_enc_of_le {w len : Nat} {f : Nat → Nat} (hf : ∀ i < len, f i < 2 ^ w) {j : Nat}
    (hj : len ≤ j) : fd w (enc w f len) j = 0 := by
  have h1 : enc w f len < 2 ^ (w * len) := enc_lt hf
  have h2 : 2 ^ (w * len) ≤ 2 ^ (w * j) :=
    Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left w hj)
  unfold fd
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h1 h2), Nat.zero_mod]

private theorem enc_fd_mod (w x len : Nat) : enc w (fd w x) len = x % 2 ^ (w * len) := by
  induction len with
  | zero => rw [enc_zero, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | succ n ih =>
    rw [enc_succ, ih, Nat.mul_succ, Nat.pow_add, Nat.mod_mul, Nat.mul_comm (fd w x n)]
    rfl

theorem enc_fd {w len x : Nat} (hx : x < 2 ^ (w * len)) : enc w (fd w x) len = x := by
  rw [enc_fd_mod, Nat.mod_eq_of_lt hx]

theorem eq_of_fd_eq {w len x y : Nat} (hx : x < 2 ^ (w * len)) (hy : y < 2 ^ (w * len))
    (h : ∀ i < len, fd w x i = fd w y i) : x = y := by
  calc x = enc w (fd w x) len := (enc_fd hx).symm
    _ = enc w (fd w y) len := enc_congr h
    _ = y := enc_fd hy

theorem enc_of_zero {w len len' : Nat} {f : Nat → Nat} (hl : len ≤ len')
    (hf : ∀ i, len ≤ i → i < len' → f i = 0) : enc w f len' = enc w f len := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl
  induction d with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, enc_succ,
      ih (Nat.le_add_right _ _) (fun i h1 h2 => hf i h1 (by omega)),
      hf (len + n) (Nat.le_add_right _ _) (by omega), Nat.zero_mul, Nat.add_zero]

theorem lor_eq_add_of_lt_of_dvd {x y k : Nat} (hx : x < 2 ^ k) (hy : 2 ^ k ∣ y) :
    x ||| y = x + y := by
  obtain ⟨z, rfl⟩ := hy
  rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hx, Nat.add_comm]

theorem lor_shiftLeft_eq_add {x y k : Nat} (hx : x < 2 ^ k) : x ||| (y <<< k) = x + y * 2 ^ k := by
  rw [Nat.shiftLeft_eq]
  exact lor_eq_add_of_lt_of_dvd hx (Nat.dvd_mul_left _ _)

private theorem div_add_mul_div (x v Q K : Nat) (hQ : 0 < Q) :
    (x + v * Q) / (Q * K) = (x / Q + v) / K := by
  rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ hQ]

private theorem div_add_lt_div (B G q v : Nat) (hB : 0 < B) (hv : v < B) :
    (B * q + v) / (B * G) = (B * q) / (B * G) := by
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_add_div hB,
    Nat.div_eq_of_lt hv, Nat.add_zero, Nat.mul_div_cancel_left _ hB]

theorem fd_add_mul {w x v i j : Nat} (hv : v < 2 ^ w) (hx : fd w x i = 0) :
    fd w (x + v * 2 ^ (w * i)) j = if j = i then v else fd w x j := by
  have hB : 0 < 2 ^ w := Nat.two_pow_pos w
  have hQ : 0 < 2 ^ (w * i) := Nat.two_pow_pos _
  rcases Nat.lt_trichotomy j i with hji | hji | hij
  · obtain ⟨d, rfl⟩ : ∃ d, i = j + d + 1 := ⟨i - j - 1, by omega⟩
    have hne : j ≠ j + d + 1 := by omega
    rw [if_neg hne]
    have e : v * 2 ^ (w * (j + d + 1)) = v * 2 ^ (w * d) * 2 ^ w * 2 ^ (w * j) := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    unfold fd
    rw [e, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_right]
  · subst hji
    rw [if_pos rfl]
    unfold fd at hx ⊢
    rw [Nat.add_mul_div_right _ _ hQ, Nat.add_mod, hx, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hv]
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + d + 1 := ⟨j - i - 1, by omega⟩
    have hne : i + d + 1 ≠ i := by omega
    rw [if_neg hne]
    unfold fd at hx ⊢
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hx
    have e : 2 ^ (w * (i + d + 1)) = 2 ^ (w * i) * (2 ^ w * 2 ^ (w * d)) := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    rw [e, div_add_mul_div _ _ _ _ hQ, ← Nat.div_div_eq_div_mul x (2 ^ (w * i)), hq,
      div_add_lt_div _ _ _ _ hB hv]

end CFSG.KS.PK

end
