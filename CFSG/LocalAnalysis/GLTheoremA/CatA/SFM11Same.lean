module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM11Arith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM11

theorem cancel_same {M g d K X Y : ℕ} (hK : 0 < K) (E1 : M * g = K * X) (E2 : M * d = K * Y) :
    X * d = Y * g := by
  apply Nat.eq_of_mul_eq_mul_left hK
  calc K * (X * d) = (K * X) * d := by ring
    _ = (M * g) * d := by rw [E1]
    _ = (M * d) * g := by ring
    _ = (K * Y) * g := by rw [E2]
    _ = K * (Y * g) := by ring

theorem key_contra {A B d g : ℕ} (hd : 1 ≤ d) (hg : g ≤ 4) (hAB : 4 * B < A)
    (h : A * d = B * g) : False := by
  have h1 : A ≤ A * d := Nat.le_mul_of_pos_right A hd
  have h2 : B * g ≤ B * 4 := Nat.mul_le_mul_left B hg
  omega

theorem ineq_B_A3 {t : ℕ} (ht : 2 ≤ t) :
    4 * ((t ^ 4 - 1) * (t ^ 8 - 1)) < (t ^ 6 - 1) * (t ^ 9 - 1) := by
  have h4 : 2 ≤ t ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left ht 4)
  have h8 : 1 ≤ t ^ 8 := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 ≤ t ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left ht 2)
  have h6a : 2 * t ^ 4 ≤ t ^ 6 := by
    rw [show t ^ 6 = t ^ 2 * t ^ 4 by ring]
    exact Nat.mul_le_mul_right _ h2
  have h9a : 2 * t ^ 8 ≤ t ^ 9 := by
    rw [show t ^ 9 = t * t ^ 8 by ring]
    exact Nat.mul_le_mul_right _ ht
  have hA : 2 * (t ^ 4 - 1) ≤ t ^ 6 - 1 := by omega
  have hB : 2 * (t ^ 8 - 1) < t ^ 9 - 1 := by omega
  have hpos : 0 < 2 * (t ^ 4 - 1) := by omega
  calc 4 * ((t ^ 4 - 1) * (t ^ 8 - 1)) = (2 * (t ^ 4 - 1)) * (2 * (t ^ 8 - 1)) := by ring
    _ < (2 * (t ^ 4 - 1)) * (t ^ 9 - 1) := Nat.mul_lt_mul_of_pos_left hB hpos
    _ ≤ (t ^ 6 - 1) * (t ^ 9 - 1) := Nat.mul_le_mul_right _ hA

theorem same_B_A3_t {M t g d : ℕ} (ht : 2 ≤ t) (hd1 : 1 ≤ d) (hg : g ≤ 4)
    (E1 : M * g = t ^ 18 * ((t ^ 6 - 1) * ((t ^ 9 - 1) * (t ^ 12 - 1))))
    (E2 : M * d = t ^ 18 * ((t ^ 4 - 1) * ((t ^ 8 - 1) * (t ^ 12 - 1)))) : False := by
  have hK : 0 < t ^ 18 := pow_pos (by omega) 18
  have hW : 0 < t ^ 12 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have h1 := cancel_same hK E1 E2
  have h2 : ((t ^ 6 - 1) * (t ^ 9 - 1)) * d * (t ^ 12 - 1) =
      ((t ^ 4 - 1) * (t ^ 8 - 1)) * g * (t ^ 12 - 1) := by
    calc ((t ^ 6 - 1) * (t ^ 9 - 1)) * d * (t ^ 12 - 1)
        = ((t ^ 6 - 1) * ((t ^ 9 - 1) * (t ^ 12 - 1))) * d := by ring
      _ = ((t ^ 4 - 1) * ((t ^ 8 - 1) * (t ^ 12 - 1))) * g := h1
      _ = ((t ^ 4 - 1) * (t ^ 8 - 1)) * g * (t ^ 12 - 1) := by ring
  exact key_contra hd1 hg (ineq_B_A3 ht) (Nat.eq_of_mul_eq_mul_right hW h2)

theorem ineq_B_U4 {t : ℕ} (ht : 2 ≤ t) :
    4 * ((t ^ 4 - 1) * (t ^ 8 - 1)) < (t ^ 6 - 1) * (t ^ 9 + 1) :=
  lt_of_lt_of_le (ineq_B_A3 ht) (Nat.mul_le_mul_left _ (by omega))

theorem same_B_U4_t {M t g d : ℕ} (ht : 2 ≤ t) (hd1 : 1 ≤ d) (hg : g ≤ 4)
    (E1 : M * g = t ^ 18 * ((t ^ 6 - 1) * ((t ^ 9 + 1) * (t ^ 12 - 1))))
    (E2 : M * d = t ^ 18 * ((t ^ 4 - 1) * ((t ^ 8 - 1) * (t ^ 12 - 1)))) : False := by
  have hK : 0 < t ^ 18 := pow_pos (by omega) 18
  have hW : 0 < t ^ 12 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have h1 := cancel_same hK E1 E2
  have h2 : ((t ^ 6 - 1) * (t ^ 9 + 1)) * d * (t ^ 12 - 1) =
      ((t ^ 4 - 1) * (t ^ 8 - 1)) * g * (t ^ 12 - 1) := by
    calc ((t ^ 6 - 1) * (t ^ 9 + 1)) * d * (t ^ 12 - 1)
        = ((t ^ 6 - 1) * ((t ^ 9 + 1) * (t ^ 12 - 1))) * d := by ring
      _ = ((t ^ 4 - 1) * ((t ^ 8 - 1) * (t ^ 12 - 1))) * g := h1
      _ = ((t ^ 4 - 1) * (t ^ 8 - 1)) * g * (t ^ 12 - 1) := by ring
  exact key_contra hd1 hg (ineq_B_U4 ht) (Nat.eq_of_mul_eq_mul_right hW h2)

theorem sq8_facts {s x : ℕ} (hx : s ^ 2 = x + 1) : s ^ 8 - 1 = x * (x + 2) * (x ^ 2 + 2 * x + 2) := by
  have h4 : s ^ 4 = x * (x + 2) + 1 := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hx]
    ring
  rw [show s ^ 8 = (s ^ 4) ^ 2 by ring, h4]
  rw [show (x * (x + 2) + 1) ^ 2 = x * (x + 2) * (x ^ 2 + 2 * x + 2) + 1 by ring, Nat.add_sub_cancel]

theorem sq6_facts {s x : ℕ} (hx : s ^ 2 = x + 1) : s ^ 6 = x * (x ^ 2 + 3 * x + 3) + 1 := by
  rw [show s ^ 6 = (s ^ 2) ^ 3 by ring, hx]
  ring

theorem same_D_A3 {M s g d : ℕ} (hs : 2 ≤ s) (hd1 : 1 ≤ d) (hg : g ≤ 4)
    (E1 : M * g = s ^ 12 * ((s ^ 4 - 1) * ((s ^ 6 - 1) * (s ^ 8 - 1))))
    (E2 : M * d = s ^ 12 * ((s ^ 4 - 1) * ((s ^ 2 - 1) * ((s ^ 4 - 1) * (s ^ 6 - 1))))) :
    False := by
  obtain ⟨x, hx⟩ : ∃ x, s ^ 2 = x + 1 :=
    ⟨s ^ 2 - 1, by have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  obtain ⟨hx2, hx4, hx6, -, -⟩ := sq_facts hx
  have hx8 := sq8_facts hx
  have hx1 : 1 ≤ x := by nlinarith
  have E1' : M * g = s ^ 12 * ((x * (x + 2)) * ((x * (x ^ 2 + 3 * x + 3)) *
      (x * (x + 2) * (x ^ 2 + 2 * x + 2)))) := by
    rw [E1, hx4, hx6, hx8]
  have E2' : M * d = s ^ 12 * ((x * (x + 2)) * (x * ((x * (x + 2)) * (x * (x ^ 2 + 3 * x + 3))))) := by
    rw [E2, hx2, hx4, hx6]
  have hK : 0 < s ^ 12 := pow_pos (by omega) 12
  have h1 := cancel_same hK E1' E2'
  have hK2 : 0 < x ^ 3 * ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3)) := by positivity
  have h2 : (x ^ 2 + 2 * x + 2) * d * (x ^ 3 * ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3))) =
      x * g * (x ^ 3 * ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3))) := by
    calc (x ^ 2 + 2 * x + 2) * d * (x ^ 3 * ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3)))
        = (x * (x + 2)) * ((x * (x ^ 2 + 3 * x + 3)) * (x * (x + 2) * (x ^ 2 + 2 * x + 2))) * d := by
          ring
      _ = (x * (x + 2)) * (x * ((x * (x + 2)) * (x * (x ^ 2 + 3 * x + 3)))) * g := h1
      _ = x * g * (x ^ 3 * ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3))) := by ring
  have h3 := Nat.eq_of_mul_eq_mul_right hK2 h2
  have h4x : 4 * x < x ^ 2 + 2 * x + 2 := by nlinarith
  exact key_contra hd1 hg h4x h3

theorem same_D_U4 {M s g d : ℕ} (hs : 2 ≤ s) (hd1 : 1 ≤ d) (hg : g ≤ 4)
    (E1 : M * g = s ^ 12 * ((s ^ 4 - 1) * ((s ^ 6 + 1) * (s ^ 8 - 1))))
    (E2 : M * d = s ^ 12 * ((s ^ 4 - 1) * ((s ^ 2 - 1) * ((s ^ 4 - 1) * (s ^ 6 - 1))))) :
    False := by
  obtain ⟨x, hx⟩ : ∃ x, s ^ 2 = x + 1 :=
    ⟨s ^ 2 - 1, by have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  obtain ⟨hx2, hx4, hx6, -, -⟩ := sq_facts hx
  have hx8 := sq8_facts hx
  have h6 := sq6_facts hx
  have h61 : s ^ 6 + 1 = x * (x ^ 2 + 3 * x + 3) + 2 := by
    rw [h6]
  have hx1 : 1 ≤ x := by nlinarith
  have E1' : M * g = s ^ 12 * ((x * (x + 2)) * ((x * (x ^ 2 + 3 * x + 3) + 2) *
      (x * (x + 2) * (x ^ 2 + 2 * x + 2)))) := by
    rw [E1, hx4, h61, hx8]
  have E2' : M * d = s ^ 12 * ((x * (x + 2)) * (x * ((x * (x + 2)) * (x * (x ^ 2 + 3 * x + 3))))) := by
    rw [E2, hx2, hx4, hx6]
  have hK : 0 < s ^ 12 := pow_pos (by omega) 12
  have h1 := cancel_same hK E1' E2'
  have hK2 : 0 < x ^ 2 * (x + 2) ^ 2 := by positivity
  have h2 : (x * (x ^ 2 + 3 * x + 3) + 2) * (x ^ 2 + 2 * x + 2) * d * (x ^ 2 * (x + 2) ^ 2) =
      x ^ 2 * (x ^ 2 + 3 * x + 3) * g * (x ^ 2 * (x + 2) ^ 2) := by
    calc (x * (x ^ 2 + 3 * x + 3) + 2) * (x ^ 2 + 2 * x + 2) * d * (x ^ 2 * (x + 2) ^ 2)
        = (x * (x + 2)) * ((x * (x ^ 2 + 3 * x + 3) + 2) *
            (x * (x + 2) * (x ^ 2 + 2 * x + 2))) * d := by ring
      _ = (x * (x + 2)) * (x * ((x * (x + 2)) * (x * (x ^ 2 + 3 * x + 3)))) * g := h1
      _ = x ^ 2 * (x ^ 2 + 3 * x + 3) * g * (x ^ 2 * (x + 2) ^ 2) := by ring
  have h3 := Nat.eq_of_mul_eq_mul_right hK2 h2
  have hxa : 4 * x + 1 ≤ x ^ 2 + 2 * x + 2 := by nlinarith
  have hP : x ^ 2 * (x ^ 2 + 3 * x + 3) = x * (x * (x ^ 2 + 3 * x + 3)) := by ring
  have hb : (x * (x ^ 2 + 3 * x + 3) + 2) * (4 * x + 1) ≤
      (x * (x ^ 2 + 3 * x + 3) + 2) * (x ^ 2 + 2 * x + 2) :=
    Nat.mul_le_mul_left _ hxa
  have hc : (x * (x ^ 2 + 3 * x + 3) + 2) * (4 * x + 1) =
      4 * (x * (x * (x ^ 2 + 3 * x + 3))) + (x * (x ^ 2 + 3 * x + 3) + 8 * x + 2) := by ring
  have hlt : 4 * (x ^ 2 * (x ^ 2 + 3 * x + 3)) < (x * (x ^ 2 + 3 * x + 3) + 2) * (x ^ 2 + 2 * x + 2) := by
    rw [hP]
    omega
  exact key_contra hd1 hg hlt h3

theorem same_D2_A3 {M s g d : ℕ} (hs : 2 ≤ s) (hd1 : 1 ≤ d) (hg : g ≤ 4)
    (E1 : M * g = s ^ 12 * ((s ^ 4 - 1) * ((s ^ 6 - 1) * (s ^ 8 - 1))))
    (E2 : M * d = s ^ 12 * ((s ^ 4 + 1) * ((s ^ 2 - 1) * ((s ^ 4 - 1) * (s ^ 6 - 1))))) :
    False := by
  obtain ⟨x, hx⟩ : ∃ x, s ^ 2 = x + 1 :=
    ⟨s ^ 2 - 1, by have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  obtain ⟨hx2, hx4, hx6, hx41, -⟩ := sq_facts hx
  have hx8 := sq8_facts hx
  have hx3 : 3 ≤ x := by nlinarith
  have E1' : M * g = s ^ 12 * ((x * (x + 2)) * ((x * (x ^ 2 + 3 * x + 3)) *
      (x * (x + 2) * (x ^ 2 + 2 * x + 2)))) := by
    rw [E1, hx4, hx6, hx8]
  have E2' : M * d = s ^ 12 * ((x * (x + 2) + 2) * (x * ((x * (x + 2)) * (x * (x ^ 2 + 3 * x + 3))))) := by
    rw [E2, hx41, hx2, hx4, hx6]
  have hK : 0 < s ^ 12 := pow_pos (by omega) 12
  have h1 := cancel_same hK E1' E2'
  have hK2 : 0 < x ^ 3 * (x + 2) * (x ^ 2 + 2 * x + 2) * (x ^ 2 + 3 * x + 3) := by positivity
  have h2 : (x + 2) * d * (x ^ 3 * (x + 2) * (x ^ 2 + 2 * x + 2) * (x ^ 2 + 3 * x + 3)) =
      g * (x ^ 3 * (x + 2) * (x ^ 2 + 2 * x + 2) * (x ^ 2 + 3 * x + 3)) := by
    calc (x + 2) * d * (x ^ 3 * (x + 2) * (x ^ 2 + 2 * x + 2) * (x ^ 2 + 3 * x + 3))
        = (x * (x + 2)) * ((x * (x ^ 2 + 3 * x + 3)) * (x * (x + 2) * (x ^ 2 + 2 * x + 2))) * d := by
          ring
      _ = (x * (x + 2) + 2) * (x * ((x * (x + 2)) * (x * (x ^ 2 + 3 * x + 3)))) * g := h1
      _ = g * (x ^ 3 * (x + 2) * (x ^ 2 + 2 * x + 2) * (x ^ 2 + 3 * x + 3)) := by ring
  have h3 := Nat.eq_of_mul_eq_mul_right hK2 h2
  have h4 : x + 2 ≤ (x + 2) * d := Nat.le_mul_of_pos_right _ hd1
  omega

theorem same_D2_U4 {M s g d : ℕ} (hs : 2 ≤ s) (hd1 : 1 ≤ d) (hg : g ≤ 4)
    (E1 : M * g = s ^ 12 * ((s ^ 4 - 1) * ((s ^ 6 + 1) * (s ^ 8 - 1))))
    (E2 : M * d = s ^ 12 * ((s ^ 4 + 1) * ((s ^ 2 - 1) * ((s ^ 4 - 1) * (s ^ 6 - 1))))) :
    False := by
  obtain ⟨x, hx⟩ : ∃ x, s ^ 2 = x + 1 :=
    ⟨s ^ 2 - 1, by have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  obtain ⟨hx2, hx4, hx6, hx41, -⟩ := sq_facts hx
  have hx8 := sq8_facts hx
  have h6 := sq6_facts hx
  have h61 : s ^ 6 + 1 = x * (x ^ 2 + 3 * x + 3) + 2 := by
    rw [h6]
  have hx3 : 3 ≤ x := by nlinarith
  have E1' : M * g = s ^ 12 * ((x * (x + 2)) * ((x * (x ^ 2 + 3 * x + 3) + 2) *
      (x * (x + 2) * (x ^ 2 + 2 * x + 2)))) := by
    rw [E1, hx4, h61, hx8]
  have E2' : M * d = s ^ 12 * ((x * (x + 2) + 2) * (x * ((x * (x + 2)) * (x * (x ^ 2 + 3 * x + 3))))) := by
    rw [E2, hx41, hx2, hx4, hx6]
  have hK : 0 < s ^ 12 := pow_pos (by omega) 12
  have h1 := cancel_same hK E1' E2'
  have hK2 : 0 < x ^ 2 * (x + 2) * (x ^ 2 + 2 * x + 2) := by positivity
  have h2 : (x + 2) * (x * (x ^ 2 + 3 * x + 3) + 2) * d * (x ^ 2 * (x + 2) * (x ^ 2 + 2 * x + 2)) =
      x * (x ^ 2 + 3 * x + 3) * g * (x ^ 2 * (x + 2) * (x ^ 2 + 2 * x + 2)) := by
    calc (x + 2) * (x * (x ^ 2 + 3 * x + 3) + 2) * d * (x ^ 2 * (x + 2) * (x ^ 2 + 2 * x + 2))
        = (x * (x + 2)) * ((x * (x ^ 2 + 3 * x + 3) + 2) *
            (x * (x + 2) * (x ^ 2 + 2 * x + 2))) * d := by ring
      _ = (x * (x + 2) + 2) * (x * ((x * (x + 2)) * (x * (x ^ 2 + 3 * x + 3)))) * g := h1
      _ = x * (x ^ 2 + 3 * x + 3) * g * (x ^ 2 * (x + 2) * (x ^ 2 + 2 * x + 2)) := by ring
  have h3 := Nat.eq_of_mul_eq_mul_right hK2 h2
  have h5 : 5 * (x * (x ^ 2 + 3 * x + 3) + 2) ≤ (x + 2) * (x * (x ^ 2 + 3 * x + 3) + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  exact key_contra (A := (x + 2) * (x * (x ^ 2 + 3 * x + 3) + 2))
    (B := x * (x ^ 2 + 3 * x + 3)) hd1 hg (by omega) h3


theorem same_B_A3_pab {M p a b g d : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : 6 * a = 9 * b) (hg : g ≤ 4) (hd1 : 1 ≤ d)
    (E1 : M * g = (p ^ a) ^ 6 * (((p ^ a) ^ 2 - 1) * (((p ^ a) ^ 3 - 1) * ((p ^ a) ^ 4 - 1))))
    (E2 : M * d = (p ^ b) ^ 9 * (((p ^ b) ^ 2 - 1) * (((p ^ b) ^ 4 - 1) * ((p ^ b) ^ 6 - 1)))) :
    False := by
  obtain ⟨c, rfl⟩ : ∃ c, b = 2 * c := ⟨b / 2, by omega⟩
  obtain rfl : a = 3 * c := by omega
  have hc : 1 ≤ c := by omega
  have ht : 2 ≤ p ^ c := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  rw [show p ^ (3 * c) = (p ^ c) ^ 3 by ring] at E1
  rw [show p ^ (2 * c) = (p ^ c) ^ 2 by ring] at E2
  rw [show ((p ^ c) ^ 3) ^ 6 = (p ^ c) ^ 18 by ring, show ((p ^ c) ^ 3) ^ 2 = (p ^ c) ^ 6 by ring,
    show ((p ^ c) ^ 3) ^ 3 = (p ^ c) ^ 9 by ring, show ((p ^ c) ^ 3) ^ 4 = (p ^ c) ^ 12 by ring] at E1
  rw [show ((p ^ c) ^ 2) ^ 9 = (p ^ c) ^ 18 by ring, show ((p ^ c) ^ 2) ^ 2 = (p ^ c) ^ 4 by ring,
    show ((p ^ c) ^ 2) ^ 4 = (p ^ c) ^ 8 by ring, show ((p ^ c) ^ 2) ^ 6 = (p ^ c) ^ 12 by ring] at E2
  exact same_B_A3_t ht hd1 hg E1 E2

theorem same_B_U4_pab {M p a b g d : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : 6 * a = 9 * b) (hg : g ≤ 4) (hd1 : 1 ≤ d)
    (E1 : M * g = (p ^ a) ^ 6 * (((p ^ a) ^ 2 - 1) * (((p ^ a) ^ 3 + 1) * ((p ^ a) ^ 4 - 1))))
    (E2 : M * d = (p ^ b) ^ 9 * (((p ^ b) ^ 2 - 1) * (((p ^ b) ^ 4 - 1) * ((p ^ b) ^ 6 - 1)))) :
    False := by
  obtain ⟨c, rfl⟩ : ∃ c, b = 2 * c := ⟨b / 2, by omega⟩
  obtain rfl : a = 3 * c := by omega
  have hc : 1 ≤ c := by omega
  have ht : 2 ≤ p ^ c := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  rw [show p ^ (3 * c) = (p ^ c) ^ 3 by ring] at E1
  rw [show p ^ (2 * c) = (p ^ c) ^ 2 by ring] at E2
  rw [show ((p ^ c) ^ 3) ^ 6 = (p ^ c) ^ 18 by ring, show ((p ^ c) ^ 3) ^ 2 = (p ^ c) ^ 6 by ring,
    show ((p ^ c) ^ 3) ^ 3 = (p ^ c) ^ 9 by ring, show ((p ^ c) ^ 3) ^ 4 = (p ^ c) ^ 12 by ring] at E1
  rw [show ((p ^ c) ^ 2) ^ 9 = (p ^ c) ^ 18 by ring, show ((p ^ c) ^ 2) ^ 2 = (p ^ c) ^ 4 by ring,
    show ((p ^ c) ^ 2) ^ 4 = (p ^ c) ^ 8 by ring, show ((p ^ c) ^ 2) ^ 6 = (p ^ c) ^ 12 by ring] at E2
  exact same_B_U4_t ht hd1 hg E1 E2

theorem same_D_A3_pab {M p a b g d : ℕ} (hp : p.Prime) (hb : 1 ≤ b)
    (hab : 6 * a = 12 * b) (hg : g ≤ 4) (hd1 : 1 ≤ d)
    (E1 : M * g = (p ^ a) ^ 6 * (((p ^ a) ^ 2 - 1) * (((p ^ a) ^ 3 - 1) * ((p ^ a) ^ 4 - 1))))
    (E2 : M * d = (p ^ b) ^ 12 * (((p ^ b) ^ 4 - 1) * (((p ^ b) ^ 2 - 1) * (((p ^ b) ^ 4 - 1) * ((p ^ b) ^ 6 - 1))))) :
    False := by
  obtain rfl : a = 2 * b := by omega
  have hs : 2 ≤ p ^ b := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  rw [show p ^ (2 * b) = (p ^ b) ^ 2 by ring] at E1
  rw [show ((p ^ b) ^ 2) ^ 6 = (p ^ b) ^ 12 by ring, show ((p ^ b) ^ 2) ^ 2 = (p ^ b) ^ 4 by ring,
    show ((p ^ b) ^ 2) ^ 3 = (p ^ b) ^ 6 by ring, show ((p ^ b) ^ 2) ^ 4 = (p ^ b) ^ 8 by ring] at E1
  exact same_D_A3 hs hd1 hg E1 E2

theorem same_D_U4_pab {M p a b g d : ℕ} (hp : p.Prime) (hb : 1 ≤ b)
    (hab : 6 * a = 12 * b) (hg : g ≤ 4) (hd1 : 1 ≤ d)
    (E1 : M * g = (p ^ a) ^ 6 * (((p ^ a) ^ 2 - 1) * (((p ^ a) ^ 3 + 1) * ((p ^ a) ^ 4 - 1))))
    (E2 : M * d = (p ^ b) ^ 12 * (((p ^ b) ^ 4 - 1) * (((p ^ b) ^ 2 - 1) * (((p ^ b) ^ 4 - 1) * ((p ^ b) ^ 6 - 1))))) :
    False := by
  obtain rfl : a = 2 * b := by omega
  have hs : 2 ≤ p ^ b := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  rw [show p ^ (2 * b) = (p ^ b) ^ 2 by ring] at E1
  rw [show ((p ^ b) ^ 2) ^ 6 = (p ^ b) ^ 12 by ring, show ((p ^ b) ^ 2) ^ 2 = (p ^ b) ^ 4 by ring,
    show ((p ^ b) ^ 2) ^ 3 = (p ^ b) ^ 6 by ring, show ((p ^ b) ^ 2) ^ 4 = (p ^ b) ^ 8 by ring] at E1
  exact same_D_U4 hs hd1 hg E1 E2

theorem same_D2_A3_pab {M p a b g d : ℕ} (hp : p.Prime) (hb : 1 ≤ b)
    (hab : 6 * a = 12 * b) (hg : g ≤ 4) (hd1 : 1 ≤ d)
    (E1 : M * g = (p ^ a) ^ 6 * (((p ^ a) ^ 2 - 1) * (((p ^ a) ^ 3 - 1) * ((p ^ a) ^ 4 - 1))))
    (E2 : M * d = (p ^ b) ^ 12 * (((p ^ b) ^ 4 + 1) * (((p ^ b) ^ 2 - 1) * (((p ^ b) ^ 4 - 1) * ((p ^ b) ^ 6 - 1))))) :
    False := by
  obtain rfl : a = 2 * b := by omega
  have hs : 2 ≤ p ^ b := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  rw [show p ^ (2 * b) = (p ^ b) ^ 2 by ring] at E1
  rw [show ((p ^ b) ^ 2) ^ 6 = (p ^ b) ^ 12 by ring, show ((p ^ b) ^ 2) ^ 2 = (p ^ b) ^ 4 by ring,
    show ((p ^ b) ^ 2) ^ 3 = (p ^ b) ^ 6 by ring, show ((p ^ b) ^ 2) ^ 4 = (p ^ b) ^ 8 by ring] at E1
  exact same_D2_A3 hs hd1 hg E1 E2

theorem same_D2_U4_pab {M p a b g d : ℕ} (hp : p.Prime) (hb : 1 ≤ b)
    (hab : 6 * a = 12 * b) (hg : g ≤ 4) (hd1 : 1 ≤ d)
    (E1 : M * g = (p ^ a) ^ 6 * (((p ^ a) ^ 2 - 1) * (((p ^ a) ^ 3 + 1) * ((p ^ a) ^ 4 - 1))))
    (E2 : M * d = (p ^ b) ^ 12 * (((p ^ b) ^ 4 + 1) * (((p ^ b) ^ 2 - 1) * (((p ^ b) ^ 4 - 1) * ((p ^ b) ^ 6 - 1))))) :
    False := by
  obtain rfl : a = 2 * b := by omega
  have hs : 2 ≤ p ^ b := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  rw [show p ^ (2 * b) = (p ^ b) ^ 2 by ring] at E1
  rw [show ((p ^ b) ^ 2) ^ 6 = (p ^ b) ^ 12 by ring, show ((p ^ b) ^ 2) ^ 2 = (p ^ b) ^ 4 by ring,
    show ((p ^ b) ^ 2) ^ 3 = (p ^ b) ^ 6 by ring, show ((p ^ b) ^ 2) ^ 4 = (p ^ b) ^ 8 by ring] at E1
  exact same_D2_U4 hs hd1 hg E1 E2

end CFSG.LocalAnalysis.GLTheoremA.SFM11
