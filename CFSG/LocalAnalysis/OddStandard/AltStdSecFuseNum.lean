module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseFb

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

@[expose] def piB (a : ℕ) : ℕ := 2 ^ (2 ^ a - 1)

@[expose] def phiB : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (a + 2) => phiB (a + 1) ^ 2 + piB (a + 1)

@[expose] def tauB : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (a + 2) => tauB (a + 1) ^ 2 + 3 * piB (a + 1) * phiB (a + 1)

@[expose] def upsB : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (a + 2) => upsB (a + 1) ^ 2 + 3 * piB (a + 1) * phiB (a + 1)

theorem piB_succ (a : ℕ) : piB (a + 1) = 2 * piB a ^ 2 := by
  unfold piB
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h2 : 2 ^ (a + 1) - 1 = 1 + (2 ^ a - 1) * 2 := by
    rw [pow_succ]
    omega
  rw [h2, pow_add, pow_mul, pow_one]

theorem piB_pos (a : ℕ) : 1 ≤ piB a := Nat.one_le_two_pow

theorem phiB_succ (a : ℕ) (ha : 1 ≤ a) : phiB (a + 1) = phiB a ^ 2 + piB a := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rfl

theorem tauB_succ (a : ℕ) (ha : 1 ≤ a) :
    tauB (a + 1) = tauB a ^ 2 + 3 * piB a * phiB a := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rfl

theorem upsB_succ (a : ℕ) (ha : 1 ≤ a) :
    upsB (a + 1) = upsB a ^ 2 + 3 * piB a * phiB a := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rfl

theorem phiB_pos (a : ℕ) (ha : 1 ≤ a) : 1 ≤ phiB a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    rw [phiB_succ a ha]
    have := piB_pos a
    omega

theorem phiB_le_upsB (a : ℕ) (ha : 1 ≤ a) : phiB a ≤ upsB a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    rw [phiB_succ a ha, upsB_succ a ha]
    have h1 : phiB a ^ 2 ≤ upsB a ^ 2 := Nat.pow_le_pow_left ih 2
    have h2 : piB a ≤ 3 * piB a * phiB a := by
      have := phiB_pos a ha
      nlinarith [piB_pos a]
    omega

theorem tauB_le_upsB (a : ℕ) (ha : 1 ≤ a) : tauB a ≤ upsB a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    rw [tauB_succ a ha, upsB_succ a ha]
    have h1 : tauB a ^ 2 ≤ upsB a ^ 2 := Nat.pow_le_pow_left ih 2
    omega

theorem piB_le_two_mul_phiB_sq (a : ℕ) (ha : 1 ≤ a) : piB a ≤ 2 * phiB a ^ 2 := by
  rcases Nat.lt_or_ge a 2 with h | h
  · obtain rfl : a = 1 := by omega
    decide
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hb : 1 ≤ b := by omega
    rw [piB_succ, phiB_succ b hb]
    have h1 : piB b ^ 2 ≤ (phiB b ^ 2 + piB b) ^ 2 :=
      Nat.pow_le_pow_left (Nat.le_add_left _ _) 2
    omega

theorem tau_phi_ups_big (a : ℕ) (ha : 4 ≤ a) : tauB a + 3 * phiB a ≤ upsB a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    have ha1 : 1 ≤ a := by omega
    rw [tauB_succ a ha1, phiB_succ a ha1, upsB_succ a ha1]
    have h1 : (tauB a + 3 * phiB a) ^ 2 ≤ upsB a ^ 2 := Nat.pow_le_pow_left ih 2
    have h2 := piB_le_two_mul_phiB_sq a ha1
    nlinarith [h1, h2, Nat.zero_le (tauB a * phiB a)]

theorem tau_phi_ups_two_three :
    tauB 2 * tauB 3 + 3 * (phiB 2 * phiB 3) ≤ upsB 2 * upsB 3 := by
  decide

theorem prod_map_le_of_le {f g : ℕ → ℕ} (m : List ℕ) (h : ∀ a ∈ m, f a ≤ g a) :
    (m.map f).prod ≤ (m.map g).prod := by
  induction m with
  | nil => simp
  | cons b m ih =>
    simp only [List.map_cons, List.prod_cons]
    exact Nat.mul_le_mul (h b (by simp)) (ih fun a ha => h a (by simp [ha]))

theorem prod_ineq_cons (b : ℕ) (hb : 1 ≤ b) (m : List ℕ)
    (h : (m.map tauB).prod + 3 * (m.map phiB).prod ≤ (m.map upsB).prod) :
    ((b :: m).map tauB).prod + 3 * ((b :: m).map phiB).prod ≤ ((b :: m).map upsB).prod := by
  simp only [List.map_cons, List.prod_cons]
  have h1 := tauB_le_upsB b hb
  have h2 := phiB_le_upsB b hb
  calc tauB b * (m.map tauB).prod + 3 * (phiB b * (m.map phiB).prod)
      ≤ upsB b * (m.map tauB).prod + 3 * (upsB b * (m.map phiB).prod) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ h1)
          (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right _ h2))
    _ = upsB b * ((m.map tauB).prod + 3 * (m.map phiB).prod) := by ring
    _ ≤ upsB b * (m.map upsB).prod := Nat.mul_le_mul_left _ h

theorem prod_ineq_big_cons (b : ℕ) (hb : 4 ≤ b) (m : List ℕ) (hm : ∀ a ∈ m, 1 ≤ a) :
    ((b :: m).map tauB).prod + 3 * ((b :: m).map phiB).prod ≤ ((b :: m).map upsB).prod := by
  simp only [List.map_cons, List.prod_cons]
  have h0 := tau_phi_ups_big b hb
  have h1 : (m.map tauB).prod ≤ (m.map upsB).prod :=
    prod_map_le_of_le m fun a ha => tauB_le_upsB a (hm a ha)
  have h2 : (m.map phiB).prod ≤ (m.map upsB).prod :=
    prod_map_le_of_le m fun a ha => phiB_le_upsB a (hm a ha)
  calc tauB b * (m.map tauB).prod + 3 * (phiB b * (m.map phiB).prod)
      ≤ tauB b * (m.map upsB).prod + 3 * (phiB b * (m.map upsB).prod) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h1)
          (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left _ h2))
    _ = (tauB b + 3 * phiB b) * (m.map upsB).prod := by ring
    _ ≤ upsB b * (m.map upsB).prod := Nat.mul_le_mul_right _ h0

theorem prod_ineq (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) (hbig : (∃ a ∈ l, 4 ≤ a) ∨ l = [2, 3]) :
    (l.map tauB).prod + 3 * (l.map phiB).prod ≤ (l.map upsB).prod := by
  induction l with
  | nil => simp at hbig
  | cons b m ih =>
    have hb : 1 ≤ b := hl b (by simp)
    have hm : ∀ a ∈ m, 1 ≤ a := fun a ha => hl a (by simp [ha])
    by_cases hbm : (∃ a ∈ m, 4 ≤ a) ∨ m = [2, 3]
    · exact prod_ineq_cons b hb m (ih hm hbm)
    · rcases hbig with ⟨a, ha, h4⟩ | h23
      · rcases List.mem_cons.1 ha with rfl | ham
        · exact prod_ineq_big_cons a h4 m hm
        · exact absurd (Or.inl ⟨a, ham, h4⟩) hbm
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h23
        simpa using tau_phi_ups_two_three

theorem card_W_eq (a : ℕ) : Nat.card (W a) = piB a := card_W a

theorem card_Fb_eq (a : ℕ) (ha : 1 ≤ a) : Nat.card (Fb a) = phiB a := by
  induction a, ha using Nat.le_induction with
  | base =>
    rw [Fb_one, Nat.card_coe_set_eq, Set.ncard_singleton]
    rfl
  | succ a ha ih =>
    rw [card_Fb_succ, ih, card_W_eq, phiB_succ a ha]

theorem prodCnt_Fb_one_eq (a : ℕ) (ha : 1 ≤ a) : prodCnt (Fb a) 1 = tauB a := by
  induction a, ha using Nat.le_induction with
  | base => exact prodCnt_Fb_one_one
  | succ a ha ih =>
    have h := prodCnt_Fb_succ a 1 (one_mul 1) (fun d => by rw [mul_one, one_mul])
    rw [ih, card_W_eq, card_Fb_eq a ha] at h
    rw [tauB_succ a ha, mul_assoc]
    exact h

theorem prodCnt_Fb_cc_eq (a : ℕ) (ha : 1 ≤ a) : prodCnt (Fb a) (cc a) = upsB a := by
  induction a, ha using Nat.le_induction with
  | base => exact prodCnt_Fb_one_cc
  | succ a ha ih =>
    have h := prodCnt_Fb_succ a (cc a) (cc_sq a ha) (cc_central a ha)
    rw [ih, card_W_eq, card_Fb_eq a ha] at h
    rw [upsB_succ a ha, mul_assoc, cc_succ a ha]
    exact h

end CFSG.OddStandard.AltStdSec.SylowSn
