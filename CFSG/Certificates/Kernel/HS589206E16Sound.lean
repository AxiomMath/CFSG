module

public import Certificates.Data.Kernel.HS589206E16
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.HS589206E16

open CFSG.KC.DcHSOutK CFSG.KC.Enum

private theorem ksHS_eqF_true {f g : Nat → Nat} (h : eqF f g = true) :
    ∀ q < 100, f q = g q := by
  intro q hq
  unfold eqF at h
  exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h q hq)

private theorem ksHS_eqF_false {f g : Nat → Nat} (h : eqF f g = false) :
    ∃ q < 100, f q ≠ g q := by
  by_contra hc
  have hc' : ∀ q, q < 100 → f q = g q := by
    intro q hq
    by_contra hne
    exact hc ⟨q, hq, hne⟩
  have ht : eqF f g = true := by
    unfold eqF
    rw [CFSG.KS.Raw.Orb.allN_iff]
    intro q hq
    rw [Nat.beq_eq]
    exact hc' q hq
  rw [ht] at h
  exact Bool.noConfusion h

private theorem ksHS_isInvF_invol {f : Nat → Nat} (h : isInvF f = true) :
    ∀ q < 100, f (f q) = q := by
  unfold isInvF at h
  rw [Bool.and_eq_true] at h
  exact ksHS_eqF_true h.1

private theorem ksHS_isInvF_ne {f : Nat → Nat} (h : isInvF f = true) :
    ∃ q < 100, f q ≠ q := by
  unfold isInvF at h
  rw [Bool.and_eq_true] at h
  have hnot : (!eqF f (fun q => q)) = true := h.2
  rw [Bool.not_eq_true'] at hnot
  exact ksHS_eqF_false hnot

private theorem ksHS_anyN_spec {n : Nat} {f : Nat → Bool} (h : anyN n f = true) :
    ∃ i < n, f i = true := by
  by_contra hc
  have hc' : ∀ i, i < n → f i = false := by
    intro i hi
    cases hb : f i
    · rfl
    · exact absurd ⟨i, hi, hb⟩ hc
  unfold anyN at h
  have ht : allN n (fun i => !f i) = true := by
    rw [CFSG.KS.Raw.Orb.allN_iff]
    intro i hi
    rw [hc' i hi]
    rfl
  rw [ht] at h
  exact Bool.noConfusion h

private theorem ksHS_ix_lt {ix : Nat → Nat} {n : Nat}
    (h : ∀ i < n - 1, ix i < ix (i + 1)) :
    ∀ i j, i < j → j < n → ix i < ix j := by
  intro i j
  induction j generalizing i with
  | zero => intro hij; omega
  | succ j ih =>
    intro hij hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | heq
    · exact Nat.lt_trans (ih i hlt (by omega)) (h j (by omega))
    · subst i
      exact h j (by omega)

private theorem ksHS_pairC_zero {I : Nat → Nat → Nat} {n a b : Nat}
    (h : pairC I n a b 0 = true) : a = b := by
  unfold pairC at h
  rw [Nat.beq_refl, Bool.cond_true] at h
  exact Nat.eq_of_beq_eq_true h

private theorem ksHS_pairC_cm {I : Nat → Nat → Nat} {n a b c : Nat}
    (h : pairC I n a b c = true) (hc0 : c ≠ 0) (hc128 : c < 128) :
    a ≠ b ∧ Nat.sub c 1 < n ∧
      (∀ q < 100, I a (I b q) = I (Nat.sub c 1) q) ∧
      (∀ q < 100, I b (I a q) = I (Nat.sub c 1) q) := by
  have hb0 : Nat.beq c 0 = false := by
    cases hh : Nat.beq c 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hh) hc0
  have hb128 : Nat.blt c 128 = true := Nat.blt_eq.mpr hc128
  unfold pairC at h
  rw [hb0, hb128] at h
  simp only [Bool.cond_false, Bool.cond_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hne, hlt⟩, h1⟩, h2⟩ := h
  refine ⟨?_, Nat.blt_eq.mp hlt, ksHS_eqF_true h1, ksHS_eqF_true h2⟩
  intro hab
  rw [hab, Nat.beq_refl] at hne
  exact Bool.noConfusion hne

private theorem ksHS_pairC_ne {I : Nat → Nat → Nat} {n a b c : Nat}
    (h : pairC I n a b c = true) (hc0 : c ≠ 0) (hc128 : 128 ≤ c) :
    ∃ q < 100, I a (I b q) ≠ I b (I a q) := by
  have hb0 : Nat.beq c 0 = false := by
    cases hh : Nat.beq c 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hh) hc0
  have hb128 : Nat.blt c 128 = false := by
    cases hh : Nat.blt c 128
    · rfl
    · exact absurd (Nat.blt_eq.mp hh) (by omega)
  unfold pairC at h
  rw [hb0, hb128] at h
  simp only [Bool.cond_false, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hlt, hne⟩ := h
  refine ⟨Nat.sub c 128, Nat.blt_eq.mp hlt, ?_⟩
  intro heq
  have htrue : Nat.beq (I a (I b (Nat.sub c 128))) (I b (I a (Nat.sub c 128))) = true := by
    rwa [Nat.beq_eq]
  rw [htrue] at hne
  exact Bool.noConfusion hne

private theorem ksHS_maskS_cons (x : Nat) (xs : List Nat) :
    maskS (x :: xs) = 2 ^ x + maskS xs := by
  unfold maskS
  rw [List.foldr_cons]
  simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul]
  rfl

private theorem ksHS_maskO_cons (x : Nat) (xs : List Nat) :
    maskO (x :: xs) = 2 ^ x ||| maskO xs := by
  unfold maskO
  rw [List.foldr_cons]
  simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul]
  rfl

private theorem ksHS_maskO_testBit (xs : List Nat) (i : Nat) :
    (maskO xs).testBit i = true ↔ i ∈ xs := by
  induction xs with
  | nil => simp [maskO]
  | cons x xs ih =>
    rw [ksHS_maskO_cons, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, ih, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

private theorem ksHS_two_pow_add_or {x m : Nat} (h : m.testBit x = false) :
    2 ^ x + m = 2 ^ x ||| m := by
  have h0 : 2 ^ x &&& m = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
    by_cases hi : x = i
    · subst i
      simp [h]
    · simp [hi]
  have hab : 2 ^ x + m < 2 ^ (2 ^ x + m) := Nat.lt_two_pow_self
  have ha : 2 ^ x < 2 ^ (2 ^ x + m) :=
    Nat.lt_of_le_of_lt (Nat.le_add_right (2 ^ x) m) hab
  have hb : m < 2 ^ (2 ^ x + m) :=
    Nat.lt_of_le_of_lt (Nat.le_add_left m (2 ^ x)) hab
  have hbv : BitVec.ofNat (2 ^ x + m) (2 ^ x) &&& BitVec.ofNat (2 ^ x + m) m =
      0#(2 ^ x + m) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb, h0, BitVec.toNat_zero]
  have key := congrArg BitVec.toNat (BitVec.add_eq_or_of_and_eq_zero
    (BitVec.ofNat (2 ^ x + m) (2 ^ x)) (BitVec.ofNat (2 ^ x + m) m) hbv)
  rw [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab] at key
  exact key

private theorem ksHS_maskS_eq_maskO {xs : List Nat} (h : xs.Nodup) :
    maskS xs = maskO xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    obtain ⟨hx, hxs⟩ := h
    have ih' := ih hxs
    have hm : (maskO xs).testBit x = false := by
      cases hb : (maskO xs).testBit x
      · rfl
      · exact absurd ((ksHS_maskO_testBit xs x).1 hb) hx
    rw [ksHS_maskS_cons, ksHS_maskO_cons, ih', ksHS_two_pow_add_or hm]

private theorem ksHS_quadBlk_i {PT MK : Nat → Nat} {nm n lo len i j : Nat}
    (h : quadBlk PT MK nm n lo len = true)
    (hi0 : lo ≤ i) (hi1 : i < lo + len) (hij : i < j) (hjN : j < n)
    (hcij : cm PT i j = true) :
    allBlk (j + 1)
      (fun k => !(cm PT i k && cm PT j k) || allBlk (k + 1)
        (fun l => !(cm PT i l && cm PT j l && cm PT k l) || quadT PT MK nm i j k l)
        (n - 1 - k))
      (n - 1 - j) = true := by
  unfold quadBlk at h
  have h1 := CFSG.KS.allBlk_spec h (i - lo) (by omega)
  have e1 : Nat.add lo (i - lo) = i := by
    have h : lo + (i - lo) = i := by omega
    exact h
  simp only [e1] at h1
  have b2 : j - (i + 1) < Nat.sub (Nat.sub n 1) i := by
    have h : j - (i + 1) < n - 1 - i := by omega
    exact h
  have h2 := CFSG.KS.allBlk_spec h1 (j - (i + 1)) (by simpa only [e1] using b2)
  have e2 : Nat.add (Nat.add i 1) (j - (i + 1)) = j := by
    have h : i + 1 + (j - (i + 1)) = j := by omega
    exact h
  simp only [e2] at h2
  rw [hcij] at h2
  simpa using h2

private theorem ksHS_quadT_get {PT MK : Nat → Nat} {nm n lo len i j k l : Nat}
    (h : quadBlk PT MK nm n lo len = true)
    (hi0 : lo ≤ i) (hi1 : i < lo + len)
    (hij : i < j) (hjk : j < k) (hkl : k < l) (hln : l < n)
    (hcij : cm PT i j = true) (hcik : cm PT i k = true) (hcjk : cm PT j k = true)
    (hcil : cm PT i l = true) (hcjl : cm PT j l = true) (hckl : cm PT k l = true) :
    quadT PT MK nm i j k l = true := by
  have h3 := ksHS_quadBlk_i h hi0 hi1 hij (by omega) hcij
  have b4 : k - (j + 1) < n - 1 - j := by omega
  have h4 := CFSG.KS.allBlk_spec h3 (k - (j + 1)) b4
  have e3 : Nat.add (j + 1) (k - (j + 1)) = k := by
    have h : j + 1 + (k - (j + 1)) = k := by omega
    exact h
  simp only [e3] at h4
  have h5 : allBlk (k + 1)
      (fun l => !(cm PT i l && cm PT j l && cm PT k l) || quadT PT MK nm i j k l)
      (n - 1 - k) = true := by
    have hc : (cm PT i k && cm PT j k) = true := by
      rw [Bool.and_eq_true]
      exact ⟨hcik, hcjk⟩
    rw [hc] at h4
    simpa using h4
  have b6 : l - (k + 1) < n - 1 - k := by omega
  have h6 := CFSG.KS.allBlk_spec h5 (l - (k + 1)) b6
  have e4 : Nat.add (k + 1) (l - (k + 1)) = l := by
    have h : k + 1 + (l - (k + 1)) = l := by omega
    exact h
  simp only [e4] at h6
  have hc : (cm PT i l && cm PT j l && cm PT k l) = true := by
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨hcil, hcjl⟩, hckl⟩
  rw [hc] at h6
  simpa using h6

theorem invsK_spec {F : Nat → Nat → Nat} {N : Nat} {ix : Nat → Nat} {n : Nat}
    (h : invsK F N ix n = true) :
    (∀ i < n, ix i < N ∧ (∀ q < 100, F (ix i) (F (ix i) q) = q) ∧ ∃ q < 100, F (ix i) q ≠ q) ∧
    (∀ i j, i < j → j < n → ix i < ix j) ∧
    ∀ k < N, (∀ q < 100, F k (F k q) = q) → (∃ q < 100, F k q ≠ q) → ∃ i < n, ix i = k := by
  unfold invsK at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hinc : ∀ i < n - 1, ix i < ix (i + 1) := fun i hi =>
    Nat.blt_eq.mp (CFSG.KS.allN_spec h2 i hi)
  have hcomp : ∀ k < N, isInvF (F k) = true → ∃ i < n, ix i = k := by
    intro k hk hinv
    have hk' := CFSG.KS.allN_spec h3 k hk
    have hany : anyN n (fun i => Nat.beq (ix i) k) = true := by
      rw [hinv] at hk'
      simpa using hk'
    obtain ⟨i, hi, hb⟩ := ksHS_anyN_spec hany
    exact ⟨i, hi, Nat.eq_of_beq_eq_true hb⟩
  refine ⟨fun i hi => ?_, ksHS_ix_lt hinc, fun k hk hinv hne => ?_⟩
  · have hi' := CFSG.KS.allN_spec h1 i hi
    rw [Bool.and_eq_true] at hi'
    exact ⟨Nat.blt_eq.mp hi'.1, ksHS_isInvF_invol hi'.2, ksHS_isInvF_ne hi'.2⟩
  · apply hcomp k hk
    unfold isInvF
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [eqF, CFSG.KS.Raw.Orb.allN_iff]
      intro q hq
      rw [Nat.beq_eq]
      exact hinv q hq
    · have hf : eqF (F k) (fun q => q) = false := by
        cases hh : eqF (F k) (fun q => q)
        · rfl
        · obtain ⟨q, hq, hneq⟩ := hne
          exact absurd (ksHS_eqF_true hh q hq) hneq
      rw [hf]
      rfl

theorem pairsK_spec {I : Nat → Nat → Nat} {PT : Nat → Nat} {n lo len : Nat}
    (h : pairsK I PT n lo len = true) : ∀ a, lo ≤ a → a < lo + len → ∀ b < n,
      (pe PT a b = 0 → a = b) ∧
      (cm PT a b = true → a ≠ b ∧ mul PT a b < n ∧
        ∀ q < 100, I a (I b q) = I (mul PT a b) q ∧ I b (I a q) = I (mul PT a b) q) ∧
      (128 ≤ pe PT a b → ∃ q < 100, I a (I b q) ≠ I b (I a q)) := by
  intro a ha ha' b hb
  have e : Nat.add lo (a - lo) = a := by
    have h : lo + (a - lo) = a := by omega
    exact h
  have hf := CFSG.KS.allBlk_spec h (a - lo) (by omega)
  simp only [e] at hf
  have hpc : pairC I n a b (pe PT a b) = true := by
    have := CFSG.KS.allN_spec hf b hb
    simpa [pairT] using this
  refine ⟨?_, ?_, ?_⟩
  · intro hp
    exact ksHS_pairC_zero (by rwa [hp] at hpc)
  · intro hcm
    unfold cm at hcm
    rw [Bool.and_eq_true] at hcm
    obtain ⟨hpos, hlt⟩ := hcm
    have hp0 : pe PT a b ≠ 0 := by
      have hpos' := Nat.blt_eq.mp hpos
      omega
    have hp128 : pe PT a b < 128 := Nat.blt_eq.mp hlt
    obtain ⟨hne, hltn, hq1, hq2⟩ := ksHS_pairC_cm hpc hp0 hp128
    refine ⟨hne, ?_, ?_⟩
    · simpa [mul] using hltn
    · intro q hq
      exact ⟨by simpa [mul] using hq1 q hq, by simpa [mul] using hq2 q hq⟩
  · intro hp128
    exact ksHS_pairC_ne hpc (by omega) hp128

theorem quadBlk_spec {PT MK : Nat → Nat} {nm n lo len : Nat} (h : quadBlk PT MK nm n lo len = true) :
    ∀ i j k l, lo ≤ i → i < lo + len → i < j → j < k → k < l → l < n →
      cm PT i j = true → cm PT i k = true → cm PT j k = true → cm PT i l = true →
      cm PT j l = true → cm PT k l = true → qDef PT i j k l = true → (qEl PT i j k l).Nodup →
      ∃ t < nm, MK t = maskS (qEl PT i j k l) := by
  intro i j k l hi0 hi1 hij hjk hkl hln hcij hcik hcjk hcil hcjl hckl hq hnd
  have hqt := ksHS_quadT_get h hi0 hi1 hij hjk hkl hln hcij hcik hcjk hcil hcjl hckl
  unfold quadT at hqt
  rw [hq] at hqt
  have hmask : maskT MK nm (qEl PT i j k l) = true := by simpa using hqt
  unfold maskT at hmask
  have hmeq := ksHS_maskS_eq_maskO hnd
  rw [← hmeq, Nat.beq_refl] at hmask
  have hany : anyN nm (fun t => Nat.beq (MK t) (maskS (qEl PT i j k l))) = true := by
    simpa using hmask
  obtain ⟨t, ht, hb⟩ := ksHS_anyN_spec hany
  exact ⟨t, ht, Nat.eq_of_beq_eq_true hb⟩

end CFSG.KC.HS589206E16

end
