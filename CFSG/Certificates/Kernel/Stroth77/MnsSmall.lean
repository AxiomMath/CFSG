module

public import CFSG.Certificates.Kernel.Stroth77.MnsSound
public import CFSG.Certificates.Kernel.Stroth77.SplitSmall

public section

namespace CFSG.KC.Stroth77MN

open Equiv Equiv.Perm CFSG.CGT.Stroth77
open CFSG.KC.Stroth77SP (rd mulK permOf memB selK l16 l32 l256 mem_l16 mem_l256 xor_lt16 rd4_lt)

@[expose] def elS (c : ℕ) : Mns := ePhiN (c % 16) * pPhiN (c / 16 % 16)

theorem elS_def (c : ℕ) : elS c = ePhiN (c % 16) * pPhiN (c / 16 % 16) := rfl

theorem ePhiN_zero : ePhiN 0 = 1 := by simp [ePhiN]

theorem pPhiN_zero : pPhiN 0 = 1 := by simp [pPhiN]

theorem encN_elS' (c : ℕ) : encN (elS c) = mulK (eK (c % 16)) (pK (c / 16 % 16)) := by
  rw [elS_def, encN_mul, encN_ePhiN, encN_pPhiN]

theorem elS_1 : elS 1 = mnsX1 := encN_injective (by rw [encN_elS', encN_mnsX1]; decide +kernel)
theorem elS_2 : elS 2 = mnsY1 := encN_injective (by rw [encN_elS', encN_mnsY1]; decide +kernel)
theorem elS_4 : elS 4 = mnsUV := encN_injective (by rw [encN_elS', encN_mnsUV]; decide +kernel)
theorem elS_8 : elS 8 = mnsT := encN_injective (by rw [encN_elS', encN_mnsT]; decide +kernel)
theorem elS_16 : elS 16 = mnsX := encN_injective (by rw [encN_elS', encN_mnsX]; decide +kernel)
theorem elS_32 : elS 32 = mnsY := encN_injective (by rw [encN_elS', encN_mnsY]; decide +kernel)
theorem elS_64 : elS 64 = mnsU := encN_injective (by rw [encN_elS', encN_mnsU]; decide +kernel)
theorem elS_128 : elS 128 = mnsW := encN_injective (by rw [encN_elS', encN_mnsW]; decide +kernel)

variable {D : Tabs}

theorem tab_facts (h : tabOK D = true) {i k : ℕ} (hi : i < 16) (hk : k < 16) :
    (rd 44 D.EF i = eK i ∧ rd 44 D.PF i = pK i ∧ permOf (rd 44 D.EF i) = permOf oneK ∧
      mulK (rd 44 D.PF i) (fullOf D (rd 8 D.ITC i)) = oneK) ∧
    (mulK (rd 44 D.EF i) (rd 44 D.EF k) = rd 44 D.EF (i ^^^ k) ∧
      mulK (rd 44 D.PF i) (rd 44 D.PF k) = fullOf D (rd 8 D.MTC (16 * i + k)) ∧
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

theorem encN_ePhiN_rd (h : tabOK D = true) {i : ℕ} (hi : i < 16) :
    encN (ePhiN i) = rd 44 D.EF i := by
  rw [encN_ePhiN, (tab_facts h hi hi).1.1]

theorem encN_pPhiN_rd (h : tabOK D = true) {i : ℕ} (hi : i < 16) :
    encN (pPhiN i) = rd 44 D.PF i := by
  rw [encN_pPhiN, (tab_facts h hi hi).1.2.1]

theorem encN_elS (h : tabOK D = true) (c : ℕ) : encN (elS c) = fullOf D c := by
  rw [elS_def, encN_mul, encN_ePhiN_rd h (Nat.mod_lt _ (by norm_num)),
    encN_pPhiN_rd h (Nat.mod_lt _ (by norm_num)), fullOf]

theorem ePhiN_mul (h : tabOK D = true) {i k : ℕ} (hi : i < 16) (hk : k < 16) :
    ePhiN i * ePhiN k = ePhiN (i ^^^ k) := by
  refine encN_injective ?_
  rw [encN_mul, encN_ePhiN_rd h hi, encN_ePhiN_rd h hk, encN_ePhiN_rd h (xor_lt16 i hi k hk),
    (tab_facts h hi hk).2.1]

theorem pPhiN_mul (h : tabOK D = true) {i k : ℕ} (hi : i < 16) (hk : k < 16) :
    pPhiN i * pPhiN k = elS (rd 8 D.MTC (16 * i + k)) := by
  refine encN_injective ?_
  rw [encN_mul, encN_pPhiN_rd h hi, encN_pPhiN_rd h hk, encN_elS h, (tab_facts h hi hk).2.2.1]

theorem pPhiN_mul_ePhiN (h : tabOK D = true) {i k : ℕ} (hi : i < 16) (hk : k < 16) :
    pPhiN i * ePhiN k = ePhiN (rd 4 D.AT (16 * i + k)) * pPhiN i := by
  refine encN_injective ?_
  rw [encN_mul, encN_mul, encN_pPhiN_rd h hi, encN_ePhiN_rd h hk, encN_ePhiN_rd h (rd4_lt _ _),
    (tab_facts h hi hk).2.2.2.1]

theorem pPhiN_mul_inv (h : tabOK D = true) {i : ℕ} (hi : i < 16) :
    pPhiN i * elS (rd 8 D.ITC i) = 1 := by
  refine encN_injective ?_
  rw [encN_mul, encN_pPhiN_rd h hi, encN_elS h, encN_one, (tab_facts h hi hi).1.2.2.2]

theorem ePhiN_mul_self (h : tabOK D = true) {i : ℕ} (hi : i < 16) : ePhiN i * ePhiN i = 1 := by
  rw [ePhiN_mul h hi hi, Nat.xor_self, ePhiN_zero]

theorem ePhiN_perm (h : tabOK D = true) {i : ℕ} (hi : i < 16) : (ePhiN i).perm = 1 := by
  have h1 : permOf (encN (ePhiN i)) = permOf (encN 1) := by
    rw [encN_ePhiN_rd h hi, encN_one, (tab_facts h hi hi).1.2.2.1]
  exact perm_eq_of_permOf h1

theorem xor3_lt16 {a b c : ℕ} (ha : a < 16) (hb : b < 16) (hc : c < 16) : a ^^^ b ^^^ c < 16 :=
  xor_lt16 _ (xor_lt16 a ha b hb) c hc

theorem mulS_mod (c d : ℕ) :
    mulS D c d % 16 = c % 16 ^^^ rd 4 D.AT (16 * (c / 16 % 16) + d % 16) ^^^
        rd 8 D.MTC (16 * (c / 16 % 16) + d / 16 % 16) % 16 ∧
      mulS D c d / 16 % 16 = rd 8 D.MTC (16 * (c / 16 % 16) + d / 16 % 16) / 16 % 16 ∧
      mulS D c d < 256 := by
  simp only [mulS]
  have h1 := xor3_lt16 (Nat.mod_lt c (by norm_num)) (rd4_lt D.AT (16 * (c / 16 % 16) + d % 16))
    (Nat.mod_lt (rd 8 D.MTC (16 * (c / 16 % 16) + d / 16 % 16)) (by norm_num : 0 < 16))
  have h2 := Nat.mod_lt (rd 8 D.MTC (16 * (c / 16 % 16) + d / 16 % 16) / 16) (by norm_num : 0 < 16)
  generalize c % 16 ^^^ rd 4 D.AT (16 * (c / 16 % 16) + d % 16) ^^^
    rd 8 D.MTC (16 * (c / 16 % 16) + d / 16 % 16) % 16 = x at h1 ⊢
  generalize rd 8 D.MTC (16 * (c / 16 % 16) + d / 16 % 16) / 16 % 16 = y at h2 ⊢
  omega

theorem mulS_lt (c d : ℕ) : mulS D c d < 256 := (mulS_mod c d).2.2

theorem invS_mod (c : ℕ) :
    invS D c % 16 = rd 4 D.AT (16 * (rd 8 D.ITC (c / 16 % 16) / 16 % 16) + c % 16) ^^^
        rd 8 D.ITC (c / 16 % 16) % 16 ∧
      invS D c / 16 % 16 = rd 8 D.ITC (c / 16 % 16) / 16 % 16 ∧ invS D c < 256 := by
  simp only [invS]
  have h1 := xor_lt16 _ (rd4_lt D.AT (16 * (rd 8 D.ITC (c / 16 % 16) / 16 % 16) + c % 16)) _
    (Nat.mod_lt (rd 8 D.ITC (c / 16 % 16)) (by norm_num : 0 < 16))
  have h2 := Nat.mod_lt (rd 8 D.ITC (c / 16 % 16) / 16) (by norm_num : 0 < 16)
  generalize rd 4 D.AT (16 * (rd 8 D.ITC (c / 16 % 16) / 16 % 16) + c % 16) ^^^
    rd 8 D.ITC (c / 16 % 16) % 16 = x at h1 ⊢
  generalize rd 8 D.ITC (c / 16 % 16) / 16 % 16 = y at h2 ⊢
  omega

theorem mod16_lt (c : ℕ) : c % 16 < 16 := Nat.mod_lt _ (by norm_num)

theorem elS_mulS (h : tabOK D = true) (c d : ℕ) : elS (mulS D c d) = elS c * elS d := by
  obtain ⟨m1, m2, -⟩ := mulS_mod (D := D) c d
  have ha := rd4_lt D.AT (16 * (c / 16 % 16) + d % 16)
  have P1 := pPhiN_mul_ePhiN h (mod16_lt (c / 16)) (mod16_lt d)
  have P2 := pPhiN_mul h (mod16_lt (c / 16)) (mod16_lt (d / 16))
  have E1 := ePhiN_mul h (mod16_lt c) ha
  have E2 := ePhiN_mul h (xor_lt16 _ (mod16_lt c) _ ha)
    (mod16_lt (rd 8 D.MTC (16 * (c / 16 % 16) + d / 16 % 16)))
  rw [elS_def (mulS D c d), m1, m2, elS_def c, elS_def d, mul_assoc, ← mul_assoc (pPhiN _), P1,
    mul_assoc, P2, elS_def (rd 8 D.MTC _), ← mul_assoc (ePhiN (c % 16)), E1, ← mul_assoc, E2]

theorem elS_invS_eq (h : tabOK D = true) (c : ℕ) :
    elS (invS D c) = elS (rd 8 D.ITC (c / 16 % 16)) * ePhiN (c % 16) := by
  obtain ⟨m1, m2, -⟩ := invS_mod (D := D) c
  have P := pPhiN_mul_ePhiN h (mod16_lt (rd 8 D.ITC (c / 16 % 16) / 16)) (mod16_lt c)
  have E := ePhiN_mul h (mod16_lt (rd 8 D.ITC (c / 16 % 16)))
    (rd4_lt D.AT (16 * (rd 8 D.ITC (c / 16 % 16) / 16 % 16) + c % 16))
  rw [elS_def (invS D c), m1, m2, elS_def (rd 8 D.ITC _), mul_assoc, P, ← mul_assoc, E,
    Nat.xor_comm (rd 4 D.AT _)]

theorem elS_invS (h : tabOK D = true) (c : ℕ) : elS (invS D c) = (elS c)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [elS_invS_eq h, elS_def c, mul_assoc, ← mul_assoc (pPhiN _), pPhiN_mul_inv h (mod16_lt _),
    one_mul, ePhiN_mul_self h (mod16_lt _)]

theorem elS_zero : elS 0 = 1 := by
  simp only [elS, Nat.zero_mod, Nat.zero_div, ePhiN_zero, pPhiN_zero, one_mul]

theorem elS_injective (h : tabOK D = true) {c d : ℕ} (hc : c < 256) (hd : d < 256)
    (he : elS c = elS d) : c = d := by
  have hi : c % 16 < 16 := mod16_lt _
  have hj : c / 16 % 16 < 16 := mod16_lt _
  have hk : d % 16 < 16 := mod16_lt _
  have hl : d / 16 % 16 < 16 := mod16_lt _
  have hp := congrArg Mns.perm he
  rw [elS_def c, elS_def d, Mns.perm_mul, Mns.perm_mul, ePhiN_perm h hi, ePhiN_perm h hk, one_mul,
    one_mul] at hp
  have hjl : c / 16 % 16 = d / 16 % 16 := by
    have h1 := permOf_eq_of_perm hp
    rw [encN_pPhiN_rd h hj, encN_pPhiN_rd h hl] at h1
    exact ((tab_facts h hj hl).2.2.2.2.1).resolve_left (not_not.2 h1)
  rw [elS_def c, elS_def d, hjl] at he
  have hik : c % 16 = d % 16 := by
    have h1 := congrArg encN (mul_right_cancel he)
    rw [encN_ePhiN_rd h hi, encN_ePhiN_rd h hk] at h1
    exact ((tab_facts h hi hk).2.2.2.2.2).resolve_left (not_not.2 h1)
  omega

theorem elS_conjS (h : tabOK D = true) (c d : ℕ) :
    elS (conjS D c d) = elS c * elS d * (elS c)⁻¹ := by
  rw [conjS, elS_mulS h, elS_mulS h, elS_invS h]

theorem commS_iff (h : tabOK D = true) {c d : ℕ} :
    commS D c d = true ↔ elS c * elS d = elS d * elS c := by
  rw [commS, beq_iff_eq, ← elS_mulS h, ← elS_mulS h]
  exact ⟨congrArg elS, elS_injective h (mulS_lt c d) (mulS_lt d c)⟩

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
    Subgroup Mns where
  carrier := {g | ∃ c < 256, M c = true ∧ elS c = g}
  mul_mem' := by
    rintro _ _ ⟨c, hc, hm, rfl⟩ ⟨d, hd, hn, rfl⟩
    exact ⟨mulS D c d, mulS_lt c d, (h.2 c hc hm).2 d hd hn, elS_mulS ht c d⟩
  one_mem' := ⟨0, by norm_num, h.1, elS_zero⟩
  inv_mem' := by
    rintro _ ⟨c, hc, hm, rfl⟩
    exact ⟨invS D c, (invS_mod c).2.2, (h.2 c hc hm).1, elS_invS ht c⟩

theorem ite_one_mem {H : Subgroup Mns} (p : Prop) [Decidable p] {m : Mns} (hm : m ∈ H) :
    (if p then m else 1) ∈ H := by
  split_ifs
  · exact hm
  · exact one_mem _

theorem card_of_param {H : Subgroup Mns} {n : ℕ} (F : ℕ → Mns)
    (hH : ∀ g, g ∈ H ↔ ∃ k < n, F k = g) (hinj : ∀ k < n, ∀ l < n, F k = F l → k = l) :
    Nat.card H = n := by
  have hset : (H : Set Mns) = F '' ↑(Finset.range n) := by
    ext g
    simp only [SetLike.mem_coe, hH, Set.mem_image, Finset.coe_range, Set.mem_Iio]
  have h1 : (H : Set Mns).ncard = n := by
    have hinj' : Set.InjOn F ↑(Finset.range n) := fun k hk l hl h =>
      hinj k (by simpa using hk) l (by simpa using hl) h
    rw [hset, hinj'.ncard_image, Set.ncard_coe_finset, Finset.card_range]
  rw [← Nat.card_coe_set_eq] at h1
  exact h1

theorem gensT_mem {g : Mns} (h : g ∈ gensT) : g ∈ Tg := Subgroup.subset_closure h

theorem elS_mem_Tg (c : ℕ) : elS c ∈ Tg := by
  have hT : ∀ g ∈ gensT, g ∈ Tg := fun g hg => gensT_mem hg
  rw [elS_def]
  refine mul_mem ?_ ?_
  · unfold ePhiN
    exact mul_mem (mul_mem (mul_mem (ite_one_mem _ (hT _ (by simp [gensT])))
      (ite_one_mem _ (hT _ (by simp [gensT])))) (ite_one_mem _ (hT _ (by simp [gensT]))))
      (ite_one_mem _ (hT _ (by simp [gensT])))
  · unfold pPhiN
    exact mul_mem (mul_mem (mul_mem (ite_one_mem _ (hT _ (by simp [gensT])))
      (ite_one_mem _ (hT _ (by simp [gensT])))) (ite_one_mem _ (hT _ (by simp [gensT]))))
      (ite_one_mem _ (hT _ (by simp [gensT])))

theorem closedP_true : ClosedP D fun _ => true := ⟨rfl, fun _ _ _ => ⟨rfl, fun _ _ _ => rfl⟩⟩

theorem mem_Tg_iff (ht : tabOK D = true) {g : Mns} : g ∈ Tg ↔ ∃ c < 256, elS c = g := by
  constructor
  · intro hg
    have hle : Tg ≤ subS D (fun _ => true) ht closedP_true := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      simp only [Set.mem_setOf_eq, gensT, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, by norm_num, rfl, elS_1⟩
      · exact ⟨2, by norm_num, rfl, elS_2⟩
      · exact ⟨4, by norm_num, rfl, elS_4⟩
      · exact ⟨8, by norm_num, rfl, elS_8⟩
      · exact ⟨16, by norm_num, rfl, elS_16⟩
      · exact ⟨32, by norm_num, rfl, elS_32⟩
      · exact ⟨64, by norm_num, rfl, elS_64⟩
      · exact ⟨128, by norm_num, rfl, elS_128⟩
    obtain ⟨c, hc, -, h⟩ := hle hg
    exact ⟨c, hc, h⟩
  · rintro ⟨c, -, rfl⟩
    exact elS_mem_Tg c

theorem card_Tg (ht : tabOK D = true) : Nat.card Tg = 256 :=
  card_of_param elS (fun _ => mem_Tg_iff ht) fun _ hk _ hl h => elS_injective ht hk hl h

theorem lt_of_mem_l32 {r : ℕ} (h : r ∈ l32) : r < 32 := by
  simp only [l32, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem mem_l32 {r : ℕ} (h : r < 32) : r ∈ l32 := by
  simp only [l32, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem cl_facts (h : clOK D = true) :
    ClosedP D (memA D) ∧ ∀ a ∈ [1, 2, 16, 32, 128], memA D a = true := by
  simp only [clOK, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨closed_facts h.1.1, h.2⟩

theorem a_facts (h : aOK D = true) :
    (∀ c < 256, memA D c = true → ∃ r < 32, phiS D r = c) ∧
      (∀ r < 32, memA D (phiS D r) = true) ∧
      (∀ r < 32, ∀ s < 32, phiS D r = phiS D s → r = s) := by
  rw [aOK] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  refine ⟨fun c hc hm => ?_, fun r hr => ?_, fun r hr s hs he => ?_⟩
  · have := List.all_eq_true.1 h1 c (mem_l256 hc)
    rw [hm, beq_iff_eq, eq_comm, List.any_eq_true] at this
    obtain ⟨r, hr, he⟩ := this
    exact ⟨r, lt_of_mem_l32 hr, beq_iff_eq.1 he⟩
  · have := List.all_eq_true.1 h1 (phiS D r) (mem_l256 (mulS_lt _ _))
    rw [beq_iff_eq] at this
    rw [this, List.any_eq_true]
    exact ⟨r, mem_l32 hr, beq_self_eq_true _⟩
  · have := List.all_eq_true.1 (List.all_eq_true.1 h2 r (mem_l32 hr)) s (mem_l32 hs)
    simp only [he, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    exact this

theorem elS_selK (r b g : ℕ) : elS (selK 0 r b g) = if r.testBit b then elS g else 1 := by
  by_cases h : r.testBit b <;> simp [selK, h, elS_zero]

theorem gensA_mem {g : Mns} (h : g ∈ gensA) : g ∈ Ag := Subgroup.subset_closure h

theorem elS_phiS_mem (ht : tabOK D = true) (r : ℕ) : elS (phiS D r) ∈ Ag := by
  have hA : ∀ g ∈ gensA, g ∈ Ag := fun g hg => gensA_mem hg
  simp only [phiS, elS_mulS ht, elS_selK, elS_1, elS_2, elS_16, elS_32, elS_128]
  exact mul_mem (mul_mem (mul_mem (mul_mem (ite_one_mem _ (hA _ (by simp [gensA])))
    (ite_one_mem _ (hA _ (by simp [gensA])))) (ite_one_mem _ (hA _ (by simp [gensA]))))
    (ite_one_mem _ (hA _ (by simp [gensA])))) (ite_one_mem _ (hA _ (by simp [gensA])))

theorem mem_Ag_iff (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true) {g : Mns} :
    g ∈ Ag ↔ ∃ c < 256, memA D c = true ∧ elS c = g := by
  constructor
  · intro hg
    have hg4 := (cl_facts hc).2
    have hle : Ag ≤ subS D (memA D) ht (cl_facts hc).1 := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      simp only [Set.mem_setOf_eq, gensA, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, by norm_num, hg4 1 (by simp), elS_1⟩
      · exact ⟨2, by norm_num, hg4 2 (by simp), elS_2⟩
      · exact ⟨16, by norm_num, hg4 16 (by simp), elS_16⟩
      · exact ⟨32, by norm_num, hg4 32 (by simp), elS_32⟩
      · exact ⟨128, by norm_num, hg4 128 (by simp), elS_128⟩
    exact hle hg
  · rintro ⟨c, hc', hm, rfl⟩
    obtain ⟨r, -, rfl⟩ := (a_facts ha).1 c hc' hm
    exact elS_phiS_mem ht r

theorem elS_mem_Ag_iff (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true) {c : ℕ}
    (hc' : c < 256) : elS c ∈ Ag ↔ memA D c = true := by
  rw [mem_Ag_iff ht hc ha]
  constructor
  · rintro ⟨d, hd, hm, he⟩
    rwa [elS_injective ht hc' hd he.symm]
  · exact fun hm => ⟨c, hc', hm, rfl⟩

theorem card_Ag (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true) :
    Nat.card Ag = 32 := by
  refine card_of_param (fun r => elS (phiS D r)) (fun g => ?_) fun r hr s hs h =>
    (a_facts ha).2.2 r hr s hs (elS_injective ht (mulS_lt _ _) (mulS_lt _ _) h)
  rw [mem_Ag_iff ht hc ha]
  constructor
  · rintro ⟨c, hc', hm, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (a_facts ha).1 c hc' hm
    exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨phiS D r, mulS_lt _ _, (a_facts ha).2.1 r hr, rfl⟩

end CFSG.KC.Stroth77MN
