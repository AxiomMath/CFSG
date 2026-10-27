module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseNum

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

@[expose] def psiB : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (a + 2) => 2 * phiB (a + 1) * psiB (a + 1)

@[expose] def tau2B : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | (a + 3) => 2 * tauB (a + 2) * tau2B (a + 2)

@[expose] def ups2B : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | (a + 3) => 2 * upsB (a + 2) * ups2B (a + 2)

@[expose] def dprod (f f' : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => f' a * (l.map f).prod + f a * dprod f f' l

theorem psiB_succ (a : ℕ) (ha : 1 ≤ a) : psiB (a + 1) = 2 * phiB a * psiB a := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rfl

theorem tau2B_succ (a : ℕ) (ha : 2 ≤ a) : tau2B (a + 1) = 2 * tauB a * tau2B a := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  rfl

theorem ups2B_succ (a : ℕ) (ha : 2 ≤ a) : ups2B (a + 1) = 2 * upsB a * ups2B a := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  rfl

theorem phiB_add_psiB_le_tauB (a : ℕ) (ha : 2 ≤ a) : phiB a + psiB a ≤ tauB a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    have ha1 : 1 ≤ a := by omega
    rw [phiB_succ a ha1, psiB_succ a ha1, tauB_succ a ha1]
    have h1 : (phiB a + psiB a) ^ 2 ≤ tauB a ^ 2 := Nat.pow_le_pow_left ih 2
    have h2 : piB a ≤ 3 * piB a * phiB a := by
      have := phiB_pos a ha1
      nlinarith [piB_pos a]
    nlinarith [h1, h2, Nat.zero_le (psiB a ^ 2)]

theorem tau2B_le_ups2B (a : ℕ) (ha : 2 ≤ a) : tau2B a ≤ ups2B a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    rw [tau2B_succ a ha, ups2B_succ a ha]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (tauB_le_upsB a (by omega))) ih

theorem psiB_le_three_mul_ups2B (a : ℕ) (ha : 2 ≤ a) : psiB a ≤ 3 * ups2B a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    have ha1 : 1 ≤ a := by omega
    rw [psiB_succ a ha1, ups2B_succ a ha]
    have h1 : phiB a * psiB a ≤ upsB a * (3 * ups2B a) :=
      Nat.mul_le_mul (phiB_le_upsB a ha1) ih
    nlinarith [h1]

def ineqG (l : List ℕ) : Prop :=
  (l.map tauB).prod + 3 * dprod tauB tau2B l + 3 * ((l.map phiB).prod + dprod phiB psiB l) ≤
    (l.map upsB).prod + 3 * dprod upsB ups2B l

theorem prod_map_perm (f : ℕ → ℕ) {l l' : List ℕ} (h : l.Perm l') :
    (l.map f).prod = (l'.map f).prod :=
  (h.map f).prod_eq

theorem dprod_perm (f f' : ℕ → ℕ) {l l' : List ℕ} (h : l.Perm l') :
    dprod f f' l = dprod f f' l' := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [dprod, ih, prod_map_perm f h]
  | swap a b l =>
    simp only [dprod, List.map_cons, List.prod_cons]
    ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem ineqG_perm {l l' : List ℕ} (h : l.Perm l') (hl : ineqG l) : ineqG l' := by
  unfold ineqG at hl ⊢
  rwa [prod_map_perm tauB h, prod_map_perm phiB h, prod_map_perm upsB h,
    dprod_perm tauB tau2B h, dprod_perm phiB psiB h, dprod_perm upsB ups2B h] at hl

theorem ineqG_step_arith (tb tb' ub ub' pb qb T T' U U' P Q : ℕ) (h1 : tb ≤ ub)
    (h2 : tb' ≤ ub') (h3 : pb + qb ≤ tb) (hTU : T ≤ U)
    (h : T + 3 * T' + 3 * (P + Q) ≤ U + 3 * U') :
    tb * T + 3 * (tb' * T + tb * T') + 3 * (pb * P + (qb * P + pb * Q)) ≤
      ub * U + 3 * (ub' * U + ub * U') := by
  have ha : tb * (T + 3 * T' + 3 * (P + Q)) ≤ tb * (U + 3 * U') := Nat.mul_le_mul_left _ h
  have hb : tb * U ≤ ub * U := Nat.mul_le_mul_right _ h1
  have hc : tb * U' ≤ ub * U' := Nat.mul_le_mul_right _ h1
  have hd : tb' * T ≤ ub' * U := Nat.mul_le_mul h2 hTU
  have he : (pb + qb) * (P + Q) ≤ tb * (P + Q) := Nat.mul_le_mul_right _ h3
  nlinarith [ha, hb, hc, hd, he, Nat.zero_le (qb * Q)]

theorem ineqG_cons (b : ℕ) (hb : 2 ≤ b) (m : List ℕ) (hm : ∀ a ∈ m, 2 ≤ a) (h : ineqG m) :
    ineqG (b :: m) := by
  have hTU : (m.map tauB).prod ≤ (m.map upsB).prod :=
    prod_map_le_of_le m fun a ha => tauB_le_upsB a (by have := hm a ha; omega)
  unfold ineqG at h ⊢
  simp only [dprod, List.map_cons, List.prod_cons]
  exact ineqG_step_arith _ _ _ _ _ _ _ _ _ _ _ _ (tauB_le_upsB b (by omega))
    (tau2B_le_ups2B b hb) (phiB_add_psiB_le_tauB b hb) hTU h

theorem ineqG_single_succ (a : ℕ) (ha : 4 ≤ a) : ineqG [a + 1] := by
  have ha1 : 1 ≤ a := by omega
  have ha2 : 2 ≤ a := by omega
  unfold ineqG
  simp only [dprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_zero, add_zero]
  rw [tauB_succ a ha1, tau2B_succ a ha2, phiB_succ a ha1, psiB_succ a ha1, upsB_succ a ha1,
    ups2B_succ a ha2]
  have h0 := tau_phi_ups_big a ha
  have h1 : (tauB a + 3 * phiB a) ^ 2 ≤ upsB a ^ 2 := Nat.pow_le_pow_left h0 2
  have h2 := piB_le_two_mul_phiB_sq a ha1
  have h3 := psiB_le_three_mul_ups2B a ha2
  have h4 := tau2B_le_ups2B a ha2
  have hi : tauB a ^ 2 + 3 * phiB a ^ 2 + 3 * piB a ≤ upsB a ^ 2 := by
    nlinarith [h1, h2, Nat.zero_le (tauB a * phiB a)]
  have hii : tauB a * tau2B a + phiB a * psiB a ≤ upsB a * ups2B a := by
    have e1 : (tauB a + 3 * phiB a) * ups2B a ≤ upsB a * ups2B a := Nat.mul_le_mul_right _ h0
    have e2 : tauB a * tau2B a ≤ tauB a * ups2B a := Nat.mul_le_mul_left _ h4
    have e3 : phiB a * psiB a ≤ phiB a * (3 * ups2B a) := Nat.mul_le_mul_left _ h3
    nlinarith [e1, e2, e3]
  nlinarith [hi, hii]

theorem ineqG_single (a : ℕ) (ha : 4 ≤ a) : ineqG [a] := by
  rcases Nat.eq_or_lt_of_le ha with rfl | h
  · unfold ineqG
    decide
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    exact ineqG_single_succ b (by omega)

theorem ineqG_two_three : ineqG [2, 3] := by
  unfold ineqG
  decide

theorem ineqG_big_cons (a : ℕ) (ha : 4 ≤ a) (m : List ℕ) (hm : ∀ b ∈ m, 2 ≤ b) :
    ineqG (a :: m) := by
  induction m with
  | nil => exact ineqG_single a ha
  | cons b m ih =>
    have hb : 2 ≤ b := hm b (by simp)
    have hm' : ∀ c ∈ m, 2 ≤ c := fun c hc => hm c (by simp [hc])
    have h1 : ineqG (a :: m) := ih hm'
    have h2 : ineqG (b :: a :: m) := by
      refine ineqG_cons b hb (a :: m) ?_ h1
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hcm
      · omega
      · exact hm' c hcm
    exact ineqG_perm (List.Perm.swap a b m) h2

theorem prod_ineqG (l : List ℕ) (hl : ∀ a ∈ l, 2 ≤ a) (hbig : (∃ a ∈ l, 4 ≤ a) ∨ l = [2, 3]) :
    (l.map tauB).prod + 3 * dprod tauB tau2B l + 3 * ((l.map phiB).prod + dprod phiB psiB l) ≤
      (l.map upsB).prod + 3 * dprod upsB ups2B l := by
  rcases hbig with ⟨a, ha, h4⟩ | h23
  · have hm : ∀ b ∈ l.erase a, 2 ≤ b := fun b hb => hl b (List.mem_of_mem_erase hb)
    exact ineqG_perm (List.perm_cons_erase ha).symm (ineqG_big_cons a h4 (l.erase a) hm)
  · subst h23
    exact ineqG_two_three

end CFSG.OddStandard.AltStdSec.SylowSn
