module

public import CFSG.LinearAlgebra.F2NatMat

public section

namespace CFSG.F2NatMat

@[expose] def conj3Tab : List (ℕ × ℕ × ℕ) := [
  (85, 85, 340), (87, 215, 342), (93, 117, 380), (98, 247, 379), (110, 239, 351),
  (117, 125, 348), (123, 207, 370), (125, 93, 372), (140, 254, 443), (159, 249, 425),
  (174, 253, 415), (177, 106, 396), (179, 110, 444), (181, 111, 412), (183, 107, 428),
  (185, 250, 397), (206, 115, 492), (213, 87, 468), (215, 213, 470), (230, 241, 489),
  (234, 94, 500), (236, 206, 498), (241, 122, 460), (249, 234, 461), (267, 141, 226),
  (271, 159, 230), (282, 140, 98), (286, 156, 102), (299, 143, 482), (303, 157, 486),
  (314, 158, 358), (318, 142, 354), (331, 236, 123), (340, 84, 84), (342, 212, 86),
  (346, 204, 114), (348, 92, 116), (359, 244, 95), (372, 124, 124), (380, 116, 92),
  (395, 225, 169), (410, 229, 187), (417, 98, 140), (419, 99, 172), (421, 103, 188),
  (423, 102, 156), (425, 226, 141), (444, 230, 159), (459, 205, 242), (461, 95, 244),
  (468, 214, 214), (470, 86, 212), (474, 233, 233), (481, 242, 205), (489, 114, 204),
  (498, 123, 236)]

@[expose] def conj3OK (w : ℕ) (T : List (ℕ × ℕ × ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ acc =>
    (Nat.beq x.1 w && eqK 3 (mulK 3 x.2.1 x.2.2) 273 &&
      eqK 3 (mulK 3 x.2.1 85) (mulK 3 w x.2.1)) || acc) T

theorem conj3OK_spec {w : ℕ} : ∀ {T : List (ℕ × ℕ × ℕ)}, conj3OK w T = true →
    ∃ g h, eqK 3 (mulK 3 g h) 273 = true ∧ eqK 3 (mulK 3 g 85) (mulK 3 w g) = true
  | [], h => by simp [conj3OK] at h
  | x :: T, h => by
    change ((Nat.beq x.1 w && eqK 3 (mulK 3 x.2.1 x.2.2) 273 &&
      eqK 3 (mulK 3 x.2.1 85) (mulK 3 w x.2.1)) || conj3OK w T) = true at h
    rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨⟨-, h1⟩, h2⟩ | h
    · exact ⟨_, _, h1, h2⟩
    · exact conj3OK_spec h

@[expose] def conj3Chk (w : ℕ) : Bool :=
  !eqK 3 (mulK 3 (mulK 3 w w) w) 273 || eqK 3 w 273 || conj3OK w conj3Tab

@[expose] def cent3Chk (u : ℕ) : Bool :=
  !det3K u || !eqK 3 (mulK 3 85 u) (mulK 3 u 85) || eqK 3 u 273 || eqK 3 u 85 ||
    eqK 3 u (mulK 3 85 85)

theorem conj3_check : allBelow 512 conj3Chk = true := by decide +kernel

theorem cent3_check : allBelow 512 cent3Chk = true := by decide +kernel

theorem oneK_three : oneK 3 = 273 := by decide

theorem dec_273 : dec 3 273 = 1 := by rw [← oneK_three, dec_oneK]

private theorem conj3_mat (W : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h3 : W * W * W = 1)
    (h1 : W ≠ 1) : ∃ G H : Matrix (Fin 3) (Fin 3) (ZMod 2), G * H = 1 ∧ G * dec 3 85 = W * G := by
  obtain ⟨w, hw, rfl⟩ := exists_dec 3 W
  have key := allBelow_spec conj3_check w hw
  rw [← dec_mulK, ← dec_mulK, ← dec_273, dec_eq_iff_eqK] at h3
  rw [← dec_273, Ne, dec_eq_iff_eqK] at h1
  simp only [conj3Chk, h3, h1, Bool.not_true, Bool.false_or] at key
  obtain ⟨g, h, hgh, hc⟩ := conj3OK_spec key
  refine ⟨dec 3 g, dec 3 h, ?_, ?_⟩
  · rw [← dec_mulK, ← dec_273, dec_eq_iff_eqK]; exact hgh
  · rw [← dec_mulK, ← dec_mulK, dec_eq_iff_eqK]; exact hc

private theorem cent3_mat (U : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hd : U.det = 1)
    (hc : dec 3 85 * U = U * dec 3 85) :
    U = 1 ∨ U = dec 3 85 ∨ U = dec 3 85 * dec 3 85 := by
  obtain ⟨u, hu, rfl⟩ := exists_dec 3 U
  have key := allBelow_spec cent3_check u hu
  rw [det_dec3, ent_eq_one] at hd
  rw [← dec_mulK, ← dec_mulK, dec_eq_iff_eqK] at hc
  simp only [cent3Chk, hd, hc, Bool.not_true, Bool.false_or] at key
  rw [← dec_273, ← dec_mulK, dec_eq_iff_eqK, dec_eq_iff_eqK, dec_eq_iff_eqK]
  simpa only [Bool.or_eq_true, or_assoc] using key

theorem cent3 (W U : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h3 : W * W * W = 1) (h1 : W ≠ 1)
    (hd : U.det = 1) (hc : W * U = U * W) : U = 1 ∨ U = W ∨ U = W * W := by
  obtain ⟨G, H, hGH, hG⟩ := conj3_mat W h3 h1
  have hHG : H * G = 1 := mul_eq_one_comm.1 hGH
  set W₀ := dec 3 85
  have hW₀ : W₀ = H * W * G := by
    rw [mul_assoc, ← hG, ← mul_assoc, hHG, one_mul]
  have hU : U = G * (H * U * G) * H := by
    simp only [mul_assoc, hGH, mul_one]
    rw [← mul_assoc, hGH, one_mul]
  have hd' : (H * U * G).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hd, mul_one, ← Matrix.det_mul, hHG, Matrix.det_one]
  have hc' : W₀ * (H * U * G) = (H * U * G) * W₀ := by
    rw [hW₀]
    calc H * W * G * (H * U * G) = H * W * (G * H) * U * G := by simp only [mul_assoc]
      _ = H * (W * U) * G := by rw [hGH, mul_one]; simp only [mul_assoc]
      _ = H * (U * W) * G := by rw [hc]
      _ = H * U * (G * H) * W * G := by rw [hGH, mul_one]; simp only [mul_assoc]
      _ = H * U * G * (H * W * G) := by simp only [mul_assoc]
  rcases cent3_mat _ hd' hc' with h | h | h
  · left
    rw [hU, h, mul_one, hGH]
  · right; left
    rw [hU, h]
    change G * W₀ * H = W
    rw [hG, mul_assoc, hGH, mul_one]
  · right; right
    rw [hU, h]
    change G * (W₀ * W₀) * H = W * W
    rw [← mul_assoc, hG, mul_assoc W G, hG, ← mul_assoc, mul_assoc (W * W), hGH, mul_one]

end CFSG.F2NatMat
