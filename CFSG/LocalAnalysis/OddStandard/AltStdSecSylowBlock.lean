module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecSylowIter

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

def tau (n : ℕ) : ℤˣ := (-1) ^ (2 ^ n)

theorem tau_zero : tau 0 = -1 := by simp [tau]

theorem tau_succ (n : ℕ) : tau (n + 1) = 1 := by
  simp [tau, pow_succ, pow_mul]

@[expose] noncomputable def ev (n : ℕ) (d : W n) : ℕ := rootCount (sgW n) 1 d

@[expose] noncomputable def od (n : ℕ) (d : W n) : ℕ := rootCount (sgW n) (-1) d

theorem one_le_ev_one (a : ℕ) : 1 ≤ ev a 1 := by
  unfold ev rootCount
  have : Nonempty {x : W a // sgW a x = 1 ∧ x * x = 1} := ⟨⟨1, map_one _, one_mul _⟩⟩
  exact Nat.card_pos

theorem ev_diag (n : ℕ) (d : W n) (hd : ∀ a : W n, a * d = d * a) :
    ev (n + 1) (diag d : W n ≀ᵣ Z2) = ev n d * ev n d + od n d * od n d +
      (if sgW n d * tau n = 1 then 2 ^ (2 ^ n - 1) else 0) := by
  have h := card_wreath_roots (sgW n) (tau n) (fun x => sgW (n + 1) x) (sgW_succ n) d hd 1
  rw [sum_units, card_W n] at h
  simp only [mul_one, one_mul] at h
  exact h

theorem od_diag (n : ℕ) (d : W n) (hd : ∀ a : W n, a * d = d * a) :
    od (n + 1) (diag d : W n ≀ᵣ Z2) = 2 * (ev n d * od n d) +
      (if sgW n d * tau n = -1 then 2 ^ (2 ^ n - 1) else 0) := by
  have h := card_wreath_roots (sgW n) (tau n) (fun x => sgW (n + 1) x) (sgW_succ n) d hd (-1)
  rw [sum_units, card_W n] at h
  simp only [mul_one, one_mul, neg_mul, neg_neg] at h
  have h2 : od (n + 1) (diag d : W n ≀ᵣ Z2) = _ := h
  rw [h2]
  unfold ev od
  rw [two_mul, mul_comm (rootCount (sgW n) (-1) d)]

theorem ev_zero : ev 0 (1 : W 0) = 1 := by
  unfold ev rootCount
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩,
    ⟨⟨1, sgW_zero 1, Subsingleton.elim _ _⟩⟩⟩

theorem od_zero : od 0 (1 : W 0) = 0 := by
  unfold od rootCount
  rw [Nat.card_eq_zero]
  left
  exact ⟨fun a => by
    have h := a.2.1
    rw [sgW_zero] at h
    exact absurd h (by decide)⟩

theorem W_one_sq (x : W 1) : x * x = 1 := by
  rcases x with ⟨f, q⟩
  show (⟨f, q⟩ : W 0 ≀ᵣ Z2) * ⟨f, q⟩ = 1
  rw [RegularWreathProduct.mul_def]
  refine RegularWreathProduct.ext (funext fun _ => Subsingleton.elim _ _) ?_
  rcases z2_cases q with rfl | rfl
  · simp
  · exact z2_mul_self

theorem ev_one_one : ev 1 (1 : W 1) = 1 := by
  have h : ev 1 (1 : W 1) = _ := ev_diag 0 (1 : W 0) (fun a => by rw [mul_one, one_mul])
  rw [h, ev_zero, od_zero, map_one, tau_zero]
  simp

theorem od_one_one : od 1 (1 : W 1) = 1 := by
  have h : od 1 (1 : W 1) = _ := od_diag 0 (1 : W 0) (fun a => by rw [mul_one, one_mul])
  rw [h, ev_zero, od_zero, map_one, tau_zero]
  simp

theorem ev_cc_one : ev 1 (cc 1) = 0 := by
  unfold ev rootCount
  rw [Nat.card_eq_zero]
  left
  exact ⟨fun a => cc_ne_one 1 le_rfl (((W_one_sq a.1).symm.trans a.2.2).symm)⟩

theorem od_cc_one : od 1 (cc 1) = 0 := by
  unfold od rootCount
  rw [Nat.card_eq_zero]
  left
  exact ⟨fun a => cc_ne_one 1 le_rfl (((W_one_sq a.1).symm.trans a.2.2).symm)⟩

theorem ev_one_succ (n : ℕ) (hn : 1 ≤ n) :
    ev (n + 1) (1 : W (n + 1)) = ev n 1 * ev n 1 + od n 1 * od n 1 + 2 ^ (2 ^ n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : ev (m + 1 + 1) (1 : W (m + 1 + 1)) = _ :=
    ev_diag (m + 1) (1 : W (m + 1)) (fun a => by rw [mul_one, one_mul])
  rw [h, map_one, tau_succ]
  simp

theorem od_one_succ (n : ℕ) (hn : 1 ≤ n) :
    od (n + 1) (1 : W (n + 1)) = 2 * (ev n 1 * od n 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : od (m + 1 + 1) (1 : W (m + 1 + 1)) = _ :=
    od_diag (m + 1) (1 : W (m + 1)) (fun a => by rw [mul_one, one_mul])
  rw [h, map_one, tau_succ]
  simp

theorem ev_cc_succ (n : ℕ) (hn : 2 ≤ n) :
    ev (n + 1) (cc (n + 1)) =
      ev n (cc n) * ev n (cc n) + od n (cc n) * od n (cc n) + 2 ^ (2 ^ n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := ev_diag (m + 1) (cc (m + 1)) (cc_central (m + 1) (by omega))
  rw [← cc_succ (m + 1) (by omega)] at h
  rw [h, sgW_cc_succ m (by omega), tau_succ]
  simp

theorem od_cc_succ (n : ℕ) (hn : 2 ≤ n) :
    od (n + 1) (cc (n + 1)) = 2 * (ev n (cc n) * od n (cc n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := od_diag (m + 1) (cc (m + 1)) (cc_central (m + 1) (by omega))
  rw [← cc_succ (m + 1) (by omega)] at h
  rw [h, sgW_cc_succ m (by omega), tau_succ]
  simp

theorem ev_two : ev 2 (1 : W 2) = 4 := by
  rw [ev_one_succ 1 le_rfl, ev_one_one, od_one_one]
  norm_num

theorem od_two : od 2 (1 : W 2) = 2 := by
  rw [od_one_succ 1 le_rfl, ev_one_one, od_one_one]

theorem ev_cc_two : ev 2 (cc 2) = 0 := by
  have h := ev_diag 1 (cc 1) (cc_central 1 le_rfl)
  rw [← cc_succ 1 le_rfl] at h
  rw [h, ev_cc_one, od_cc_one, sgW_cc_one, tau_succ]
  norm_num

theorem od_cc_two : od 2 (cc 2) = 2 := by
  have h := od_diag 1 (cc 1) (cc_central 1 le_rfl)
  rw [← cc_succ 1 le_rfl] at h
  rw [h, ev_cc_one, od_cc_one, sgW_cc_one, tau_succ]
  norm_num

theorem block_aux (n : ℕ) (hn : 2 ≤ n) :
    ev n (cc n) < ev n 1 ∧ od n (cc n) ≤ od n 1 ∧ 1 ≤ od n 1 ∧
      ev n (cc n) * od n (cc n) = 0 := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [ev_cc_two, od_cc_two, ev_two, od_two]
    omega
  | succ n hn ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [ev_cc_succ n hn, od_cc_succ n hn, ev_one_succ n (by omega), od_one_succ n (by omega),
      h4]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := Nat.mul_lt_mul'' h1 h1
      have := Nat.mul_le_mul h2 h2
      omega
    · omega
    · have : 1 ≤ ev n 1 := by omega
      have := Nat.mul_le_mul this h3
      omega
    · simp

theorem block_facts (n : ℕ) (hn : 1 ≤ n) :
    ev n (cc n) < ev n 1 ∧ od n (cc n) ≤ od n 1 ∧ 1 ≤ od n 1 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [ev_cc_one, od_cc_one, ev_one_one, od_one_one]
    omega
  · exact ⟨(block_aux n h).1, (block_aux n h).2.1, (block_aux n h).2.2.1⟩

theorem od_cc_eq_zero (n : ℕ) (hn : 3 ≤ n) : od n (cc n) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [od_cc_succ m (by omega), (block_aux m (by omega)).2.2.2]

end CFSG.OddStandard.AltStdSec.SylowSn
