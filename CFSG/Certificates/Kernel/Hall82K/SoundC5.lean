module

public import CFSG.Certificates.Kernel.Hall82K.SoundBase

public section

namespace CFSG.KC.Hall82K

open CFSG.ComponentClassification.AS81.Hexa CFSG.CGT.Hall82

theorem testBit_fld (c s i : ℕ) : (fld c s).testBit i = (decide (i < 6) && c.testBit (s + i)) := by
  have h63 : (63 : ℕ) = 2 ^ 6 - 1 := rfl
  change ((c >>> s) &&& 63).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, h63, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem apL_congr {c c' v : ℕ} (h : ∀ j < 6, v.testBit j = true → fld c (6 * j) = fld c' (6 * j)) :
    apL c v = apL c' v := by
  unfold apL
  simp only [bitN_mul]
  have e : ∀ j < 6, (if v.testBit j = true then fld c (6 * j) else 0) =
      (if v.testBit j = true then fld c' (6 * j) else 0) := fun j hj => by
    by_cases hv : v.testBit j = true
    · rw [if_pos hv, if_pos hv, h j hj hv]
    · rw [if_neg hv, if_neg hv]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num),
    e 4 (by norm_num), e 5 (by norm_num)]

theorem fld_mod {c k j : ℕ} (hj : j < k) : fld (c % 2 ^ (6 * k)) (6 * j) = fld c (6 * j) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_fld, testBit_fld, Nat.testBit_mod_two_pow]
  by_cases hi : i < 6
  · have : 6 * j + i < 6 * k := by omega
    simp [hi, this]
  · simp [hi]

theorem mod_succ_eq {c k : ℕ} :
    c % 2 ^ (6 * (k + 1)) = Nat.lor (c % 2 ^ (6 * k)) (Nat.shiftLeft (fld c (6 * k)) (6 * k)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change _ = ((c % 2 ^ (6 * k)) ||| (fld c (6 * k) <<< (6 * k))).testBit i
  rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    testBit_fld]
  by_cases h1 : i < 6 * k
  · have h2 : i < 6 * (k + 1) := by omega
    simp [h1, h2]
  · by_cases h2 : i < 6 * (k + 1)
    · have h3 : i - 6 * k < 6 := by omega
      have h4 : 6 * k + (i - 6 * k) = i := by omega
      simp [h1, h2, h3, h4]
      omega
    · have h3 : ¬ i - 6 * k < 6 := by omega
      simp [h1, h2, h3]

theorem lt_two_pow_six_mul {v k : ℕ} (hv : v < 2 ^ k) {j : ℕ} (hj : v.testBit j = true) : j < k := by
  by_contra hjk
  have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num)
    (by omega : k ≤ j)))
  rw [hj] at this
  exact absurd this (by simp)

theorem apL_mod {f : Fin 64 → Fin 64} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w)) {k : ℕ}
    {v : Fin 64} (hv : v.val < 2 ^ k) : apL (codeL f % 2 ^ (6 * k)) v.val = (f v).val := by
  rw [← apL_codeL hf v]
  exact apL_congr fun j _ hj => fld_mod (lt_two_pow_six_mul hv hj)

theorem fld_codeL_pow {f : Fin 64 → Fin 64} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w))
    {k : ℕ} (hk : k < 6) : fld (codeL f) (6 * k) = (f (bitF k)).val := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ :=
    fld_enc6 (f 1).2 (f 2).2 (f 4).2 (f 8).2 (f 16).2 (f 32).2
  interval_cases k
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5

theorem kMaskK_lt : kMaskK < 2 ^ 64 := by decide +kernel

theorem bitF_oval : ∀ k < 6, IsOvalVec (bitF k) := by
  unfold IsOvalVec
  decide +kernel

theorem bitF_val : ∀ k < 6, (bitF k).val = Nat.shiftLeft 1 k := by decide +kernel

theorem inKK_iff (hkm : allN (fun v => beqB (memL v hallKList) (inKK v)) 64 = true) (v : Fin 64) :
    inKK v.val = true ↔ IsOvalVec v := by
  have h := allN_iff.1 hkm v.val v.2
  rw [beqB_eq_true, memL_iff] at h
  exact h.symm

theorem inKK_bit (hkm : allN (fun v => beqB (memL v hallKList) (inKK v)) 64 = true) {v : Fin 64}
    (hv : IsOvalVec v) : bitN kMaskK v.val = 1 := by
  have h := (inKK_iff hkm v).2 hv
  rw [bitN_eq_one_iff]
  unfold inKK at h
  rw [Nat.blt_eq] at h
  change 0 < kMaskK &&& 1 <<< v.val at h
  rw [Nat.one_shiftLeft] at h
  by_contra hne
  · have hf : kMaskK.testBit v.val = false := Bool.eq_false_iff.2 hne
    have : kMaskK &&& 2 ^ v.val = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hi : v.val = i
      · rw [← hi, hf]
        simp
      · simp [hi]
    omega

section Search

variable (hidx : idxBridgeK = true)
  (hkm : allN (fun v => beqB (memL v hallKList) (inKK v)) 64 = true)
  {L : List ℕ} {f : Fin 64 → Fin 64} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w))
  (hK : ∀ v, IsOvalVec v → IsOvalVec (f v)) (h5 : f 5 = 5)

include hkm hf hK h5 in
theorem c5LvlK_mod {k : ℕ} (hk : k < 6) : c5LvlK k (codeL f % 2 ^ (6 * (k + 1))) = true := by
  unfold c5LvlK
  rw [allN_iff]
  intro d hd
  have hd' : d < 2 ^ k := by
    change d < 1 <<< k at hd
    rwa [Nat.one_shiftLeft] at hd
  have hv : Nat.lor (Nat.shiftLeft 1 k) d < 2 ^ (k + 1) := by
    change 1 <<< k ||| d < _
    rw [Nat.one_shiftLeft]
    exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k))
      (lt_trans hd' (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)))
  have hv64 : Nat.lor (Nat.shiftLeft 1 k) d < 64 :=
    lt_of_lt_of_le hv (by
      calc 2 ^ (k + 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 64 := by norm_num)
  set v : Fin 64 := ⟨_, hv64⟩ with hvdef
  have ha := apL_mod hf (v := v) hv
  change band (bor (Bool.rec true false (inKK v.val)) (inKK (apL _ v.val)))
    (bor (Bool.rec true false (Nat.beq v.val 5)) (Nat.beq (apL _ 5) 5)) = true
  rw [ha, band_eq_true, bor_eq_true, bor_eq_true, bnot_eq_true, bnot_eq_true]
  constructor
  · by_cases hkv : inKK v.val = true
    · exact Or.inr ((inKK_iff hkm _).2 (hK v ((inKK_iff hkm v).1 hkv)))
    · exact Or.inl (Bool.eq_false_iff.2 hkv)
  · by_cases h5v : Nat.beq v.val 5 = true
    · right
      have hv5 : v = 5 := Fin.ext (nbeq_iff.1 h5v)
      have h5' : apL (codeL f % 2 ^ (6 * (k + 1))) (5 : Fin 64).val = (f 5).val :=
        apL_mod hf (by rw [← hv5]; exact hv)
      rw [nbeq_iff]
      change apL (codeL f % 2 ^ (6 * (k + 1))) (5 : Fin 64).val = 5
      rw [h5', h5]
      rfl
    · exact Or.inl (Bool.eq_false_iff.2 h5v)

include hidx hkm hf hK h5 in
theorem c5SrchK_step {n : ℕ} (hn : n < 6)
    (h : c5SrchK L (n + 1) (codeL f % 2 ^ (6 * (5 - n))) = true) :
    c5SrchK L n (codeL f % 2 ^ (6 * (5 - n + 1))) = true := by
  have hk : 5 - n < 6 := by omega
  have hx := inKK_bit hkm (hK _ (bitF_oval (5 - n) hk))
  change forBitsK (fun x => bor (Bool.rec true false (c5LvlK (Nat.sub 5 n)
      (Nat.lor (codeL f % 2 ^ (6 * (5 - n))) (Nat.shiftLeft x (Nat.mul 6 (Nat.sub 5 n))))))
      (c5SrchK L n (Nat.lor (codeL f % 2 ^ (6 * (5 - n)))
        (Nat.shiftLeft x (Nat.mul 6 (Nat.sub 5 n)))))) 64 kMaskK = true at h
  have hb := forBitsK_sound hidx kMaskK_lt h _ (f (bitF (5 - n))).2 hx
  have he : Nat.lor (codeL f % 2 ^ (6 * (5 - n)))
      (Nat.shiftLeft (f (bitF (5 - n))).val (Nat.mul 6 (Nat.sub 5 n))) =
      codeL f % 2 ^ (6 * (5 - n + 1)) := by
    rw [mod_succ_eq, fld_codeL_pow hf hk]
    rfl
  rw [he, bor_eq_true, bnot_eq_true] at hb
  have hl : c5LvlK (Nat.sub 5 n) (codeL f % 2 ^ (6 * (5 - n + 1))) = true :=
    c5LvlK_mod hkm hf hK h5 hk
  rcases hb with hb | hb
  · rw [hl] at hb
    exact absurd hb (by simp)
  · exact hb

include hidx hkm hf hK h5 in
theorem c5SrchK_sound (h : c5SrchK L 6 0 = true) (hinj : Function.Injective f) : codeL f ∈ L := by
  have h0 : codeL f % 2 ^ (6 * (5 - 5)) = 0 := Nat.mod_one _
  have s5 := c5SrchK_step hidx hkm hf hK h5 (n := 5) (by norm_num) (h0 ▸ h)
  have s4 := c5SrchK_step hidx hkm hf hK h5 (n := 4) (by norm_num) s5
  have s3 := c5SrchK_step hidx hkm hf hK h5 (n := 3) (by norm_num) s4
  have s2 := c5SrchK_step hidx hkm hf hK h5 (n := 2) (by norm_num) s3
  have s1 := c5SrchK_step hidx hkm hf hK h5 (n := 1) (by norm_num) s2
  have s0 := c5SrchK_step hidx hkm hf hK h5 (n := 0) (by norm_num) s1
  have e6 : codeL f % 2 ^ (6 * (5 - 0 + 1)) = codeL f := Nat.mod_eq_of_lt (codeL_lt f)
  rw [e6] at s0
  change bor (Bool.rec true false (allN (fun v => bor (Nat.beq v 0)
    (Bool.rec true false (Nat.beq (apL (codeL f) v) 0))) 64)) (memL (codeL f) L) = true at s0
  rw [bor_eq_true, bnot_eq_true] at s0
  rcases s0 with s0 | s0
  · exfalso
    have hall : allN (fun v => bor (Nat.beq v 0)
        (Bool.rec true false (Nat.beq (apL (codeL f) v) 0))) 64 = true := by
      rw [allN_iff]
      intro v hv
      rw [bor_eq_true, bnot_eq_true]
      by_cases hv0 : v = 0
      · exact Or.inl (nbeq_iff.2 hv0)
      · right
        have hf0 : f 0 = 0 := map_zero_of_add hf
        rw [apL_codeL hf ⟨v, hv⟩]
        cases hb : Nat.beq (f ⟨v, hv⟩).val 0
        · rfl
        · exfalso
          have : f ⟨v, hv⟩ = f 0 := by rw [hf0]; exact Fin.ext (nbeq_iff.1 hb)
          exact hv0 (congrArg Fin.val (hinj this))
    rw [hall] at s0
    exact absurd s0 (by simp)
  · exact memL_iff.1 s0

end Search

end CFSG.KC.Hall82K
