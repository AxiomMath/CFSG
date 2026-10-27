module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2F2

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Matrix

variable {k : ℕ}

theorem two_dvd_two_pow (hk : 1 ≤ k) : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)

@[expose] def castTwo (hk : 1 ≤ k) : ZMod (2 ^ k) →+* ZMod 2 :=
  ZMod.castHom (two_dvd_two_pow hk) (ZMod 2)

theorem castTwo_apply (hk : 1 ≤ k) (x : ZMod (2 ^ k)) : castTwo hk x = ZMod.cast x := rfl

@[expose] def red (k : ℕ) (A : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) :
    Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  A.map fun x => ZMod.cast x

theorem red_apply (A : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) (i j : Fin 3) :
    red k A i j = ZMod.cast (A i j) := rfl

theorem red_eq_mapMatrix (hk : 1 ≤ k) (A : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) :
    red k A = (castTwo hk).mapMatrix A := rfl

theorem red_add (hk : 1 ≤ k) (A B : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) :
    red k (A + B) = red k A + red k B := by
  simp only [red_eq_mapMatrix hk, map_add]

theorem red_sub (hk : 1 ≤ k) (A B : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) :
    red k (A - B) = red k A - red k B := by
  simp only [red_eq_mapMatrix hk, map_sub]

theorem red_mul (hk : 1 ≤ k) (A B : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) :
    red k (A * B) = red k A * red k B := by
  simp only [red_eq_mapMatrix hk, map_mul]

theorem red_one (hk : 1 ≤ k) : red k (1 : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) = 1 := by
  simp only [red_eq_mapMatrix hk, map_one]

theorem red_pow (hk : 1 ≤ k) (A : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) (m : ℕ) :
    red k (A ^ m) = red k A ^ m := by
  simp only [red_eq_mapMatrix hk, map_pow]

theorem red_smul (hk : 1 ≤ k) (c : ZMod (2 ^ k)) (A : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) :
    red k (c • A) = (ZMod.cast c : ZMod 2) • red k A := by
  ext i j
  simp only [red_apply, Matrix.smul_apply, smul_eq_mul, ZMod.cast_mul (two_dvd_two_pow hk)]

theorem cast_two (hk : 1 ≤ k) : (ZMod.cast (2 : ZMod (2 ^ k)) : ZMod 2) = 0 := by
  rw [← castTwo_apply hk, map_ofNat]
  decide

theorem cast_two_pow (hk : 1 ≤ k) {i : ℕ} (hi : 1 ≤ i) :
    (ZMod.cast ((2 : ZMod (2 ^ k)) ^ i) : ZMod 2) = 0 := by
  rw [ZMod.cast_pow (two_dvd_two_pow hk), cast_two hk, zero_pow (by omega)]

theorem two_pow_self_eq_zero : (2 : ZMod (2 ^ k)) ^ k = 0 := by
  rw [show (2 : ZMod (2 ^ k)) ^ k = ((2 ^ k : ℕ) : ZMod (2 ^ k)) by push_cast; rfl,
    ZMod.natCast_self]

theorem one_le_of_red_eq_one {A : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))} (h : red k A = 1) :
    1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exfalso
    have h00 := congrFun (congrFun h 0) 0
    rw [red_apply, ZMod.cast_eq_val, Matrix.one_apply_eq] at h00
    have hv : (A 0 0).val < 1 := ZMod.val_lt (A 0 0)
    rw [show (A 0 0).val = 0 by omega, Nat.cast_zero] at h00
    exact zero_ne_one h00
  · exact hk

theorem eq_two_mul_half {x : ZMod (2 ^ k)} (hx : (ZMod.cast x : ZMod 2) = 0) :
    x = 2 * ((x.val / 2 : ℕ) : ZMod (2 ^ k)) := by
  have h2 : 2 ∣ x.val := by
    rw [ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hx
    exact hx
  calc x = ((x.val : ℕ) : ZMod (2 ^ k)) := (ZMod.natCast_zmod_val x).symm
    _ = ((2 * (x.val / 2) : ℕ) : ZMod (2 ^ k)) := by rw [Nat.mul_div_cancel' h2]
    _ = 2 * ((x.val / 2 : ℕ) : ZMod (2 ^ k)) := by push_cast; ring

theorem eq_two_smul_of_red_eq_zero {A : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))}
    (h : red k A = 0) : ∃ B : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k)), A = (2 : ZMod (2 ^ k)) • B :=
  ⟨A.map fun x => ((x.val / 2 : ℕ) : ZMod (2 ^ k)), by
    ext i j
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact eq_two_mul_half (congrFun (congrFun h i) j)⟩

theorem cast_eq_zero_of_two_pow_mul {j : ℕ} (hjk : j < k) {x : ZMod (2 ^ k)}
    (h : (2 : ZMod (2 ^ k)) ^ j * x = 0) : (ZMod.cast x : ZMod 2) = 0 := by
  rw [← ZMod.natCast_zmod_val x] at h
  have h' : ((2 ^ j * x.val : ℕ) : ZMod (2 ^ k)) = 0 := by push_cast; exact h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have h2 : 2 ^ j * 2 ∣ 2 ^ j * x.val := (pow_succ 2 j ▸ pow_dvd_pow 2 hjk).trans h'
  rw [ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h2

theorem red_eq_zero_of_two_pow_smul {j : ℕ} (hjk : j < k)
    {A : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))} (h : (2 : ZMod (2 ^ k)) ^ j • A = 0) :
    red k A = 0 := by
  ext a b
  have hab := congrFun (congrFun h a) b
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hab
  exact cast_eq_zero_of_two_pow_mul hjk hab

theorem red_eq_inv (hk : 1 ≤ k) {M N : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))}
    {g : GL (Fin 3) (ZMod 2)} (hM : red k M = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hMN : M * N = 1) :
    red k N = ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  have h := congrArg (red k) hMN
  rw [red_mul hk, red_one hk, hM] at h
  calc red k N = ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * red k N) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    _ = _ := by rw [h, mul_one]

theorem mat_add_self_F2 : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), X + X = 0 := by
  decide +kernel

theorem pow_two_pow_eq_one_of_red {A : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))}
    (hA : red k A = 1) : A ^ 2 ^ (k - 1) = 1 := by
  have hk := one_le_of_red_eq_one hA
  obtain ⟨Y, hY⟩ := eq_two_smul_of_red_eq_zero (A := A - 1)
    (by rw [red_sub hk, hA, red_one hk, sub_self])
  have key : ∀ i : ℕ, ∃ Z : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k)),
      A ^ 2 ^ i = 1 + (2 : ZMod (2 ^ k)) ^ (i + 1) • Z := by
    intro i
    induction i with
    | zero => exact ⟨Y, by rw [pow_zero, pow_one, zero_add, pow_one, ← hY]; abel⟩
    | succ i ih =>
      obtain ⟨Z, hZ⟩ := ih
      refine ⟨Z + (2 : ZMod (2 ^ k)) ^ i • (Z * Z), ?_⟩
      have e1 : (1 + (2 : ZMod (2 ^ k)) ^ (i + 1) • Z) ^ 2 =
          1 + ((2 : ZMod (2 ^ k)) ^ (i + 1) + 2 ^ (i + 1)) • Z +
            ((2 : ZMod (2 ^ k)) ^ (i + 1) * 2 ^ (i + 1)) • (Z * Z) := by
        rw [sq, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm,
          add_smul]
        abel
      have c1 : (2 : ZMod (2 ^ k)) ^ (i + 1) + 2 ^ (i + 1) = 2 ^ (i + 1 + 1) := by ring
      have c2 : (2 : ZMod (2 ^ k)) ^ (i + 1) * 2 ^ (i + 1) = 2 ^ (i + 1 + 1) * 2 ^ i := by ring
      rw [pow_succ 2 i, pow_mul A (2 ^ i) 2, hZ, e1, c1, c2, smul_add, smul_smul, add_assoc]
  obtain ⟨Z, hZ⟩ := key (k - 1)
  rw [hZ, Nat.sub_add_cancel hk, two_pow_self_eq_zero, zero_smul, add_zero]

theorem eq_one_of_red_of_odd {A : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))} (hA : red k A = 1)
    {m : ℕ} (hm : Odd m) (hAm : A ^ m = 1) : A = 1 :=
  (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_left (k - 1) (Nat.coprime_two_left.2 hm))).1
    ⟨pow_two_pow_eq_one_of_red hA, hAm⟩

theorem pow_two_pow_eq_one_of_cast (hk : 1 ≤ k) {x : ZMod (2 ^ k)}
    (hx : (ZMod.cast x : ZMod 2) = 1) : x ^ 2 ^ (k - 1) = 1 := by
  have hA : red k (x • (1 : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k)))) = 1 := by
    rw [red_smul hk, red_one hk, hx, one_smul]
  have h := pow_two_pow_eq_one_of_red hA
  rw [smul_pow, one_pow] at h
  have h00 := congrFun (congrFun h 0) 0
  simpa using h00

theorem stab_step (hk : 1 ≤ k) {j : ℕ} (hj : 1 ≤ j) (hjk : j < k) {u μ c : ZMod (2 ^ k)}
    (hμ : u - 1 = 2 * μ) (hμ1 : (ZMod.cast μ : ZMod 2) = 1) (hc : (ZMod.cast c : ZMod 2) = 1)
    {Z M N : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))} (hMN : M * N = 1)
    (h : M * (c • 1 + (2 : ZMod (2 ^ k)) ^ j • Z) * N = c • 1 + (2 : ZMod (2 ^ k)) ^ j • Z ∨
      M * (c • 1 + (2 : ZMod (2 ^ k)) ^ j • Z) * N = u • (c • 1 + (2 : ZMod (2 ^ k)) ^ j • Z)) :
    red k M * red k Z * red k N + red k Z = 0 ∨ red k M * red k Z * red k N + red k Z = 1 := by
  have hexp : M * (c • 1 + (2 : ZMod (2 ^ k)) ^ j • Z) * N =
      c • 1 + (2 : ZMod (2 ^ k)) ^ j • (M * Z * N) := by
    rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, add_mul, smul_mul_assoc, smul_mul_assoc,
      hMN]
  have hred : red k (M * Z * N) = red k M * red k Z * red k N := by rw [red_mul hk, red_mul hk]
  rw [hexp] at h
  rcases h with h | h
  · left
    have h0 : (2 : ZMod (2 ^ k)) ^ j • (M * Z * N - Z) = 0 := by
      rw [smul_sub, sub_eq_zero]
      exact add_left_cancel h
    have h1 := red_eq_zero_of_two_pow_smul hjk h0
    rw [red_sub hk, hred, sub_eq_zero] at h1
    rw [h1, mat_add_self_F2]
  · have hμc : (ZMod.cast (μ * c) : ZMod 2) = 1 := by
      rw [ZMod.cast_mul (two_dvd_two_pow hk), hμ1, hc, one_mul]
    have h' : (2 : ZMod (2 ^ k)) ^ j • (M * Z * N - u • Z) = (2 * μ * c) • 1 := by
      rw [smul_add, smul_smul, smul_smul] at h
      have h2 : (2 : ZMod (2 ^ k)) ^ j • (M * Z * N) =
          (u * c) • 1 + (u * (2 : ZMod (2 ^ k)) ^ j) • Z - c • 1 := by
        rw [← h]
        abel
      rw [smul_sub, smul_smul, mul_comm ((2 : ZMod (2 ^ k)) ^ j) u, h2,
        show 2 * μ * c = u * c - c by rw [← hμ]; ring, sub_smul]
      abel
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · obtain rfl : j = 1 := by omega
      right
      have hu1 : (ZMod.cast u : ZMod 2) = 1 := by
        rw [show u = 1 + 2 * μ by rw [← hμ]; ring, ZMod.cast_add (two_dvd_two_pow hk),
          ZMod.cast_mul (two_dvd_two_pow hk), cast_two hk, zero_mul, add_zero,
          ZMod.cast_one (two_dvd_two_pow hk)]
      have h0 : (2 : ZMod (2 ^ k)) ^ 1 • (M * Z * N - u • Z - (μ * c) • 1) = 0 := by
        rw [smul_sub, h', smul_smul, pow_one, ← mul_assoc, sub_self]
      have h1 := red_eq_zero_of_two_pow_smul hjk h0
      rw [red_sub hk, red_sub hk, red_smul hk, red_smul hk, red_one hk, hred, hu1, hμc, one_smul,
        one_smul, sub_sub, sub_eq_zero] at h1
      rw [h1, add_comm (red k Z) 1, add_assoc, mat_add_self_F2, add_zero]
    · exfalso
      have h0 : (2 : ZMod (2 ^ k)) ^ 1 •
          ((2 : ZMod (2 ^ k)) ^ (j - 1) • (M * Z * N - u • Z) - (μ * c) • 1) = 0 := by
        rw [smul_sub, smul_smul, ← pow_add, show 1 + (j - 1) = j by omega, h', smul_smul, pow_one,
          ← mul_assoc, sub_self]
      have h1 := red_eq_zero_of_two_pow_smul (by omega : 1 < k) h0
      rw [red_sub hk, red_smul hk, red_smul hk, red_one hk, cast_two_pow hk (by omega : 1 ≤ j - 1),
        hμc, zero_smul, one_smul, zero_sub, neg_eq_zero] at h1
      exact one_ne_zero h1

theorem exists_eq_smul_one_of_mu {u μ : ZMod (2 ^ k)} (hμ : u - 1 = 2 * μ)
    (hμ1 : (ZMod.cast μ : ZMod 2) = 1)
    {w M₁ N₁ M₂ N₂ : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))} (hw : red k w = 1)
    (hM₁ : red k M₁ = (h1G : Matrix (Fin 3) (Fin 3) (ZMod 2))) (hMN₁ : M₁ * N₁ = 1)
    (h₁ : M₁ * w * N₁ = w ∨ M₁ * w * N₁ = u • w)
    (hM₂ : red k M₂ = (h2G : Matrix (Fin 3) (Fin 3) (ZMod 2))) (hMN₂ : M₂ * N₂ = 1)
    (h₂ : M₂ * w * N₂ = w ∨ M₂ * w * N₂ = u • w) :
    ∃ c : ZMod (2 ^ k), w = c • (1 : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) := by
  have hk := one_le_of_red_eq_one hw
  have hN₁ := red_eq_inv hk hM₁ hMN₁
  have hN₂ := red_eq_inv hk hM₂ hMN₂
  have key : ∀ j, 1 ≤ j → j ≤ k → ∃ (c : ZMod (2 ^ k))
      (Z : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))), w = c • 1 + (2 : ZMod (2 ^ k)) ^ j • Z := by
    intro j hj1
    induction j, hj1 using Nat.le_induction with
    | base =>
      intro _
      obtain ⟨Z, hZ⟩ := eq_two_smul_of_red_eq_zero (A := w - 1)
        (by rw [red_sub hk, hw, red_one hk, sub_self])
      exact ⟨1, Z, by rw [one_smul, pow_one, ← hZ]; abel⟩
    | succ j hj1 ih =>
      intro hjk
      obtain ⟨c, Z, hcZ⟩ := ih (by omega)
      have hc : (ZMod.cast c : ZMod 2) = 1 := by
        have h := hw
        rw [hcZ, red_add hk, red_smul hk, red_smul hk, red_one hk, cast_two_pow hk hj1, zero_smul,
          add_zero] at h
        have h00 := congrFun (congrFun h 0) 0
        simpa using h00
      have h₁' := h₁
      have h₂' := h₂
      rw [hcZ] at h₁' h₂'
      have s₁ := stab_step hk hj1 (by omega) hμ hμ1 hc hMN₁ h₁'
      have s₂ := stab_step hk hj1 (by omega) hμ hμ1 hc hMN₂ h₂'
      rw [hM₁, hN₁] at s₁
      rw [hM₂, hN₂] at s₂
      rcases STAB (red k Z) s₁ s₂ with h0 | h1
      · obtain ⟨Z', hZ'⟩ := eq_two_smul_of_red_eq_zero h0
        exact ⟨c, Z', by rw [hcZ, hZ', smul_smul, ← pow_succ]⟩
      · obtain ⟨Z', hZ'⟩ := eq_two_smul_of_red_eq_zero (A := Z - 1)
          (by rw [red_sub hk, h1, red_one hk, sub_self])
        have hZ : Z = 1 + (2 : ZMod (2 ^ k)) • Z' := by rw [← hZ']; abel
        refine ⟨c + 2 ^ j, Z', ?_⟩
        rw [hcZ, hZ, smul_add, smul_smul, ← pow_succ, add_smul]
        abel
  obtain ⟨c, Z, h⟩ := key k hk le_rfl
  exact ⟨c, by rw [h, two_pow_self_eq_zero, zero_smul, add_zero]⟩

theorem exists_mu_of_u (hk : 1 ≤ k) {u : ZMod (2 ^ k)}
    (hu : u = -1 ∨ (3 ≤ k ∧ u = -1 + 2 ^ (k - 1))) :
    ∃ μ : ZMod (2 ^ k), u - 1 = 2 * μ ∧ (ZMod.cast μ : ZMod 2) = 1 := by
  rcases hu with rfl | ⟨hk3, rfl⟩
  · refine ⟨-1, by ring, ?_⟩
    rw [ZMod.cast_neg (two_dvd_two_pow hk), ZMod.cast_one (two_dvd_two_pow hk)]
    decide
  · refine ⟨-1 + 2 ^ (k - 2), ?_, ?_⟩
    · have h : (2 : ZMod (2 ^ k)) ^ (k - 1) = 2 * 2 ^ (k - 2) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h]
      ring
    · rw [ZMod.cast_add (two_dvd_two_pow hk), ZMod.cast_neg (two_dvd_two_pow hk),
        ZMod.cast_one (two_dvd_two_pow hk), cast_two_pow hk (by omega : 1 ≤ k - 2), add_zero]
      decide

theorem exists_eq_smul_one {u : ZMod (2 ^ k)} (hu : u = -1 ∨ (3 ≤ k ∧ u = -1 + 2 ^ (k - 1)))
    {w M₁ N₁ M₂ N₂ : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))} (hw : red k w = 1)
    (hM₁ : red k M₁ = (h1G : Matrix (Fin 3) (Fin 3) (ZMod 2))) (hMN₁ : M₁ * N₁ = 1)
    (h₁ : M₁ * w * N₁ = w ∨ M₁ * w * N₁ = u • w)
    (hM₂ : red k M₂ = (h2G : Matrix (Fin 3) (Fin 3) (ZMod 2))) (hMN₂ : M₂ * N₂ = 1)
    (h₂ : M₂ * w * N₂ = w ∨ M₂ * w * N₂ = u • w) :
    ∃ c : ZMod (2 ^ k), w = c • (1 : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) := by
  obtain ⟨μ, hμ, hμ1⟩ := exists_mu_of_u (one_le_of_red_eq_one hw) hu
  exact exists_eq_smul_one_of_mu hμ hμ1 hw hM₁ hMN₁ h₁ hM₂ hMN₂ h₂

theorem sq_eq_one_of_u {u : ZMod (2 ^ k)} (hu : u = -1 ∨ (3 ≤ k ∧ u = -1 + 2 ^ (k - 1))) :
    u ^ 2 = 1 := by
  rcases hu with rfl | ⟨hk3, rfl⟩
  · exact neg_one_sq
  · have h1 : (2 : ZMod (2 ^ k)) * 2 ^ (k - 1) = 0 := by
      rw [← pow_succ', show k - 1 + 1 = k by omega, two_pow_self_eq_zero]
    have h2 : (2 : ZMod (2 ^ k)) ^ (k - 1) * 2 ^ (k - 1) = 0 := by
      rw [← pow_add, show k - 1 + (k - 1) = k + (k - 2) by omega, pow_add, two_pow_self_eq_zero,
        zero_mul]
    calc (-1 + 2 ^ (k - 1) : ZMod (2 ^ k)) ^ 2 =
        1 - 2 * 2 ^ (k - 1) + 2 ^ (k - 1) * 2 ^ (k - 1) := by ring
      _ = 1 := by rw [h1, h2]; ring

theorem cube_eq_one_F2 : ∀ y : ZMod 2, y ^ 3 = 1 → y = 1 := by decide

theorem eq_of_cube {u c : ZMod (2 ^ k)} (hu : u ^ 2 = 1) (hc : c ^ 3 = 1 ∨ c ^ 3 = u) :
    c = 1 ∨ c = u := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · haveI : Subsingleton (ZMod (2 ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero 2)
    exact Or.inl (Subsingleton.elim _ _)
  have hk : 1 ≤ k := hk0
  obtain ⟨v, hv, hv2, hcv⟩ : ∃ v : ZMod (2 ^ k), (v = 1 ∨ v = u) ∧ v * v = 1 ∧ c ^ 3 = v ^ 3 := by
    rcases hc with h | h
    · exact ⟨1, Or.inl rfl, mul_one 1, by rw [h, one_pow]⟩
    · exact ⟨u, Or.inr rfl, by rw [← sq, hu], by rw [h, pow_succ, hu, one_mul]⟩
  have hx3 : (c * v) ^ 3 = 1 := by
    rw [mul_pow, hcv, ← mul_pow, hv2, one_pow]
  have hxc : (ZMod.cast (c * v) : ZMod 2) = 1 := by
    have h := congrArg (castTwo hk) hx3
    rw [map_pow, map_one] at h
    exact cube_eq_one_F2 _ h
  have hx : c * v = 1 :=
    (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_right (k - 1) (by norm_num : Nat.Coprime 3 2))).1
      ⟨hx3, pow_two_pow_eq_one_of_cast hk hxc⟩
  have hcv' : c = v := by
    calc c = c * (v * v) := by rw [hv2, mul_one]
      _ = (c * v) * v := by rw [mul_assoc]
      _ = v := by rw [hx, one_mul]
  rcases hv with rfl | rfl
  · exact Or.inl hcv'
  · exact Or.inr hcv'

theorem two_pow_mul_mod_two (hk : 1 ≤ k) (n : ℕ) :
    (2 : ZMod (2 ^ k)) ^ (k - 1) * ((n % 2 : ℕ) : ZMod (2 ^ k)) =
      2 ^ (k - 1) * (n : ZMod (2 ^ k)) := by
  conv_rhs => rw [← Nat.mod_add_div n 2]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_add, ← mul_assoc, ← pow_succ,
    Nat.sub_add_cancel hk, two_pow_self_eq_zero, zero_mul, add_zero]

theorem two_pow_mul_eq_cast (hk : 1 ≤ k) (y : ZMod (2 ^ k)) :
    (2 : ZMod (2 ^ k)) ^ (k - 1) * y =
      2 ^ (k - 1) * (((ZMod.cast y : ZMod 2)).val : ZMod (2 ^ k)) := by
  rw [ZMod.cast_eq_val, ZMod.val_natCast, two_pow_mul_mod_two hk, ZMod.natCast_zmod_val]

theorem two_pow_mul_val_add (hk : 1 ≤ k) (a b : ZMod 2) :
    (2 : ZMod (2 ^ k)) ^ (k - 1) * ((a + b).val : ZMod (2 ^ k)) =
      2 ^ (k - 1) * (a.val : ZMod (2 ^ k)) + 2 ^ (k - 1) * (b.val : ZMod (2 ^ k)) := by
  rw [ZMod.val_add, two_pow_mul_mod_two hk, Nat.cast_add, mul_add]

theorem mulVec_two_pow_val (hk : 1 ≤ k) (A : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k)))
    (v : Fin 3 → ZMod 2) :
    A *ᵥ (fun i => 2 ^ (k - 1) * ((v i).val : ZMod (2 ^ k))) =
      fun i => 2 ^ (k - 1) * (((red k A *ᵥ v) i).val : ZMod (2 ^ k)) := by
  funext i
  have hterm : ∀ j, A i j * (2 ^ (k - 1) * ((v j).val : ZMod (2 ^ k))) =
      2 ^ (k - 1) * ((red k A i j * v j).val : ZMod (2 ^ k)) := by
    intro j
    rw [mul_left_comm, two_pow_mul_eq_cast hk, ZMod.cast_mul (two_dvd_two_pow hk),
      ZMod.cast_natCast (two_dvd_two_pow hk), ZMod.natCast_zmod_val]
    rfl
  simp only [mulVec, dotProduct, Fin.sum_univ_three]
  rw [two_pow_mul_val_add hk, two_pow_mul_val_add hk, hterm, hterm, hterm]

end CFSG.OddStandard.AltStdSmall4.G2
