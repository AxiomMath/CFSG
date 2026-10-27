module

public import CFSG.Certificates.Kernel.Stroth77.SplitSound

public section

namespace CFSG.KC.Stroth77SP

open Equiv Equiv.Perm CFSG.CGT.Stroth77

@[expose] def elS (c : ℕ) : Msp := ePhi (c % 16) * pPhi (c / 16 % 16)

theorem mem_l16 {i : ℕ} (h : i < 16) : i ∈ l16 := by
  simp only [l16, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem mem_l256 {c : ℕ} (h : c < 256) : c ∈ l256 :=
  List.mem_flatMap.2 ⟨c / 16, mem_l16 (by omega), List.mem_map.2 ⟨c % 16, mem_l16 (by omega),
    by omega⟩⟩

theorem rd4_lt (T k : ℕ) : rd 4 T k < 16 := Nat.mod_lt _ (by norm_num)

theorem xor_lt16 : ∀ i < 16, ∀ k < 16, i ^^^ k < 16 := by decide

theorem ePhi_zero : ePhi 0 = 1 := by simp [ePhi]

theorem pPhi_zero : pPhi 0 = 1 := by simp [pPhi]

variable {D : Tabs}

theorem tab_facts (h : tabOK D = true) {i k : ℕ} (hi : i < 16) (hk : k < 16) :
    (rd 44 D.EF i = eK i ∧ rd 44 D.PF i = pK i ∧ permOf (rd 44 D.EF i) = permOf oneK ∧
      rd 4 D.MT (16 * i + rd 4 D.IT i) = 0) ∧
    (mulK (rd 44 D.EF i) (rd 44 D.EF k) = rd 44 D.EF (i ^^^ k) ∧
      mulK (rd 44 D.PF i) (rd 44 D.PF k) = rd 44 D.PF (rd 4 D.MT (16 * i + k)) ∧
      mulK (rd 44 D.PF i) (rd 44 D.EF k) =
        mulK (rd 44 D.EF (rd 4 D.AT (16 * i + k))) (rd 44 D.PF i) ∧
      (permOf (rd 44 D.PF i) ≠ permOf (rd 44 D.PF k) ∨ i = k) ∧
      (rd 44 D.EF i ≠ rd 44 D.EF k ∨ i = k)) := by
  rw [tabOK, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  have h1 := h.1 i (mem_l16 hi)
  have h2 := List.all_eq_true.1 (h.2 i (mem_l16 hi)) k (mem_l16 hk)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne] at h1 h2
  exact ⟨⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩, h2.1.1.1.1, h2.1.1.1.2, h2.1.1.2, h2.1.2, h2.2⟩

theorem enc_ePhi_rd (h : tabOK D = true) {i : ℕ} (hi : i < 16) : enc (ePhi i) = rd 44 D.EF i := by
  rw [enc_ePhi, (tab_facts h hi hi).1.1]

theorem enc_pPhi_rd (h : tabOK D = true) {i : ℕ} (hi : i < 16) : enc (pPhi i) = rd 44 D.PF i := by
  rw [enc_pPhi, (tab_facts h hi hi).1.2.1]

theorem ePhi_mul (h : tabOK D = true) {i k : ℕ} (hi : i < 16) (hk : k < 16) :
    ePhi i * ePhi k = ePhi (i ^^^ k) := by
  refine enc_injective ?_
  rw [enc_mul, enc_ePhi_rd h hi, enc_ePhi_rd h hk, enc_ePhi_rd h (xor_lt16 i hi k hk),
    (tab_facts h hi hk).2.1]

theorem pPhi_mul (h : tabOK D = true) {i k : ℕ} (hi : i < 16) (hk : k < 16) :
    pPhi i * pPhi k = pPhi (rd 4 D.MT (16 * i + k)) := by
  refine enc_injective ?_
  rw [enc_mul, enc_pPhi_rd h hi, enc_pPhi_rd h hk, enc_pPhi_rd h (rd4_lt _ _),
    (tab_facts h hi hk).2.2.1]

theorem pPhi_mul_ePhi (h : tabOK D = true) {i k : ℕ} (hi : i < 16) (hk : k < 16) :
    pPhi i * ePhi k = ePhi (rd 4 D.AT (16 * i + k)) * pPhi i := by
  refine enc_injective ?_
  rw [enc_mul, enc_mul, enc_pPhi_rd h hi, enc_ePhi_rd h hk, enc_ePhi_rd h (rd4_lt _ _),
    (tab_facts h hi hk).2.2.2.1]

theorem pPhi_mul_inv (h : tabOK D = true) {i : ℕ} (hi : i < 16) :
    pPhi i * pPhi (rd 4 D.IT i) = 1 := by
  rw [pPhi_mul h hi (rd4_lt _ _), (tab_facts h hi hi).1.2.2.2, pPhi_zero]

theorem ePhi_mul_self (h : tabOK D = true) {i : ℕ} (hi : i < 16) : ePhi i * ePhi i = 1 := by
  rw [ePhi_mul h hi hi, Nat.xor_self, ePhi_zero]

theorem ePhi_perm (h : tabOK D = true) {i : ℕ} (hi : i < 16) : (ePhi i).perm = 1 := by
  have h1 : permOf (enc (ePhi i)) = permOf (enc 1) := by
    rw [enc_ePhi_rd h hi, enc_one, (tab_facts h hi hi).1.2.2.1]
  exact perm_eq_of_permOf h1

theorem mulS_mod (c d : ℕ) :
    mulS D c d % 16 = c % 16 ^^^ rd 4 D.AT (16 * (c / 16 % 16) + d % 16) ∧
      mulS D c d / 16 % 16 = rd 4 D.MT (16 * (c / 16 % 16) + d / 16 % 16) := by
  have h1 := xor_lt16 _ (Nat.mod_lt c (by norm_num)) _ (rd4_lt D.AT (16 * (c / 16 % 16) + d % 16))
  have h2 := rd4_lt D.MT (16 * (c / 16 % 16) + d / 16 % 16)
  unfold mulS
  generalize c % 16 ^^^ rd 4 D.AT (16 * (c / 16 % 16) + d % 16) = x at h1 ⊢
  generalize rd 4 D.MT (16 * (c / 16 % 16) + d / 16 % 16) = y at h2 ⊢
  omega

theorem mulS_lt (c d : ℕ) : mulS D c d < 256 := by
  have h1 := xor_lt16 _ (Nat.mod_lt c (by norm_num)) _ (rd4_lt D.AT (16 * (c / 16 % 16) + d % 16))
  have h2 := rd4_lt D.MT (16 * (c / 16 % 16) + d / 16 % 16)
  unfold mulS
  generalize c % 16 ^^^ rd 4 D.AT (16 * (c / 16 % 16) + d % 16) = x at h1 ⊢
  generalize rd 4 D.MT (16 * (c / 16 % 16) + d / 16 % 16) = y at h2 ⊢
  omega

theorem invS_mod (c : ℕ) :
    invS D c % 16 = rd 4 D.AT (16 * rd 4 D.IT (c / 16 % 16) + c % 16) ∧
      invS D c / 16 % 16 = rd 4 D.IT (c / 16 % 16) ∧ invS D c < 256 := by
  have h1 := rd4_lt D.AT (16 * rd 4 D.IT (c / 16 % 16) + c % 16)
  have h2 := rd4_lt D.IT (c / 16 % 16)
  unfold invS
  generalize rd 4 D.AT (16 * rd 4 D.IT (c / 16 % 16) + c % 16) = x at h1 ⊢
  generalize rd 4 D.IT (c / 16 % 16) = y at h2 ⊢
  omega

theorem elS_mulS (h : tabOK D = true) (c d : ℕ) : elS (mulS D c d) = elS c * elS d := by
  have hi : c % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hj : c / 16 % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hk : d % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hl : d / 16 % 16 < 16 := Nat.mod_lt _ (by norm_num)
  obtain ⟨m1, m2⟩ := mulS_mod (D := D) c d
  rw [elS, elS, elS, m1, m2, mul_assoc, ← mul_assoc (pPhi _), pPhi_mul_ePhi h hj hk, mul_assoc,
    pPhi_mul h hj hl, ← mul_assoc, ePhi_mul h hi (rd4_lt _ _)]

theorem elS_invS_mul (h : tabOK D = true) (c : ℕ) : elS c * elS (invS D c) = 1 := by
  have hi : c % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hj : c / 16 % 16 < 16 := Nat.mod_lt _ (by norm_num)
  obtain ⟨m1, m2, -⟩ := invS_mod (D := D) c
  rw [elS, elS, m1, m2, ← pPhi_mul_ePhi h (rd4_lt _ _) hi, mul_assoc, ← mul_assoc (pPhi _),
    pPhi_mul_inv h hj, one_mul, ePhi_mul_self h hi]

theorem elS_invS (h : tabOK D = true) (c : ℕ) : elS (invS D c) = (elS c)⁻¹ :=
  (inv_eq_of_mul_eq_one_right (elS_invS_mul h c)).symm

theorem elS_zero : elS 0 = 1 := by
  simp only [elS, Nat.zero_mod, Nat.zero_div, ePhi_zero, pPhi_zero, one_mul]

theorem elS_injective (h : tabOK D = true) {c d : ℕ} (hc : c < 256) (hd : d < 256)
    (he : elS c = elS d) : c = d := by
  have hi : c % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hj : c / 16 % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hk : d % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hl : d / 16 % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hp := congrArg Msp.perm he
  rw [elS, elS, Msp.perm_mul, Msp.perm_mul, ePhi_perm h hi, ePhi_perm h hk, one_mul,
    one_mul] at hp
  have hjl : c / 16 % 16 = d / 16 % 16 := by
    have h1 := permOf_eq_of_perm hp
    rw [enc_pPhi_rd h hj, enc_pPhi_rd h hl] at h1
    exact ((tab_facts h hj hl).2.2.2.2.1).resolve_left (not_not.2 h1)
  rw [elS, elS, hjl] at he
  have hik : c % 16 = d % 16 := by
    have h1 := congrArg enc (mul_right_cancel he)
    rw [enc_ePhi_rd h hi, enc_ePhi_rd h hk] at h1
    exact ((tab_facts h hi hk).2.2.2.2.2).resolve_left (not_not.2 h1)
  omega

@[expose] def ClosedP (D : Tabs) (M : ℕ → Bool) : Prop :=
  M 0 = true ∧ ∀ c < 256, M c = true → M (invS D c) = true ∧
    ∀ d < 256, M d = true → M (mulS D c d) = true

theorem closed_facts {M : ℕ → Bool} (h : closedB D M = true) : ClosedP D M := by
  rw [closedB, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨h.1, fun c hc hm => ?_⟩
  have h1 := h.2 c (mem_l256 hc)
  simp only [hm, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true] at h1
  refine ⟨h1.1, fun d hd hmd => ?_⟩
  have h2 := h1.2 d (mem_l256 hd)
  simp only [hmd, Bool.not_true, Bool.false_or] at h2
  exact h2

@[expose] def subS (D : Tabs) (M : ℕ → Bool) (ht : tabOK D = true) (h : ClosedP D M) :
    Subgroup Msp where
  carrier := {g | ∃ c < 256, M c = true ∧ elS c = g}
  mul_mem' := by
    rintro _ _ ⟨c, hc, hm, rfl⟩ ⟨d, hd, hn, rfl⟩
    exact ⟨mulS D c d, mulS_lt c d, (h.2 c hc hm).2 d hd hn, elS_mulS ht c d⟩
  one_mem' := ⟨0, by norm_num, h.1, elS_zero⟩
  inv_mem' := by
    rintro _ ⟨c, hc, hm, rfl⟩
    exact ⟨invS D c, (invS_mod c).2.2, (h.2 c hc hm).1, elS_invS ht c⟩

end CFSG.KC.Stroth77SP
