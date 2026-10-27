module

public import Certificates.Data.Kernel.HS589206E16B
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.HS589206E16

open CFSG.KC.DcHSOutK CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

theorem bit_iff (m i : Nat) : bit m i = true ↔ m.testBit i = true := by
  change Nat.beq ((m >>> i) &&& 1) 1 = true ↔ m.testBit i = true
  rw [Nat.testBit, Nat.and_one_is_mod, Nat.one_and_eq_mod_two, Nat.beq_eq, bne_iff_ne]
  omega

private theorem ksHB_anyN_spec {n : Nat} {f : Nat → Bool} (h : anyN n f = true) :
    ∃ i < n, f i = true := by
  unfold anyN at h
  by_contra hc
  have hc' : ∀ i < n, (!f i) = true := by
    intro i hi
    cases hfi : f i with
    | false => rfl
    | true => exact absurd ⟨i, hi, hfi⟩ hc
  have hall : allN n (fun i => !f i) = true := allN_iff.2 hc'
  rw [hall] at h
  exact Bool.false_ne_true h

private theorem ksHB_fixM_spec {I : Nat → Nat → Nat} {n m q : Nat} :
    fixM I n m q = true ↔ ∀ i < n, bit m i = true → I i q = q := by
  unfold fixM
  rw [allN_iff]
  constructor
  · intro h i hi hbit
    have h' := h i hi
    rw [hbit] at h'
    simp only [Bool.not_true, Bool.false_or] at h'
    rwa [Nat.beq_eq] at h'
  · intro h i hi
    cases hb : bit m i with
    | false => simp
    | true =>
      simp only [Bool.not_true, Bool.false_or]
      rw [Nat.beq_eq]
      exact h i hi hb

private theorem ksHB_goodK_spec {I : Nat → Nat → Nat} {n m : Nat} {l : List Nat}
    (h : goodK I n m l = true) {q : Nat} (hq : q < 100) :
    (∀ i < n, bit m i = true → I i q = q) ↔ q ∈ l := by
  unfold goodK at h
  have h' := allN_spec h q hq
  have hany : fixM I n m q = l.any (fun x => Nat.beq x q) := by
    cases hb : l.any (fun x => Nat.beq x q) <;>
      cases hm : fixM I n m q <;> simp [Bool.beq, hb, hm] at h' ⊢
  rw [← ksHB_fixM_spec, hany, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hb⟩
    rw [Nat.beq_eq] at hb
    simpa [hb] using hx
  · intro hq'
    exact ⟨q, hq', Nat.beq_refl q⟩

theorem eT_good {I A : Nat → Nat → Nat} {F0 : List Nat} {n m : Nat} {R : Nat → Nat}
    (h : eT I A F0 n m R = true) (h0 : R 0 = 0) :
    (∀ l ∈ wdR R, l < 4) ∧ ∀ q < 100,
      ((∀ i < n, bit m i = true → I i q = q) ↔ q ∈ F0.map (CFSG.KC.E64F.wordF A (wdR R))) := by
  unfold eT at h
  have hb : Nat.beq (R 0) 0 = true := by
    rw [Nat.beq_eq]
    exact h0
  rw [hb, Bool.cond_true, Bool.and_eq_true_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro l hl
    unfold wdR at hl
    rw [List.mem_map] at hl
    obtain ⟨j, hj, rfl⟩ := hl
    have hj' := List.mem_range.mp hj
    have hlt := allN_spec h1 j hj'
    rw [Nat.blt_eq] at hlt
    exact hlt
  · intro q hq
    exact ksHB_goodK_spec h2 hq

private theorem ksHB_blkT_spec {I : Nat → Nat → Nat} {n m b : Nat} {R : Nat → Nat}
    (h : blkT I n m (fun s => R (s + 1)) b = true) :
    R (2 * b + 1) < 100 ∧ R (2 * b + 2) < 100 ∧
      (∀ i < n, bit m i = true →
        I i (R (2 * b + 1)) = R (2 * b + 1) ∨
          I i (R (2 * b + 1)) = R (2 * b + 2)) ∧
      ∃ i < n, bit m i = true ∧ I i (R (2 * b + 1)) = R (2 * b + 2) := by
  unfold blkT at h
  simp only [Bool.and_eq_true_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.blt_eq] at h1
    simpa using h1
  · rw [Nat.blt_eq] at h2
    simpa using h2
  · intro i hi hbit
    have hi' := allN_spec h3 i hi
    change (!bit m i || Nat.beq (I i (R (2 * b + 1))) (R (2 * b + 1)) ||
      Nat.beq (I i (R (2 * b + 1))) (R (2 * b + 2))) = true at hi'
    rw [hbit] at hi'
    simp only [Bool.not_true, Bool.false_or] at hi'
    rw [Bool.or_eq_true_iff] at hi'
    rcases hi' with h | h
    · left
      rw [Nat.beq_eq] at h
      exact h
    · right
      rw [Nat.beq_eq] at h
      exact h
  · obtain ⟨i, hi, hi'⟩ := ksHB_anyN_spec h4
    obtain ⟨hbit, hbeq⟩ := Bool.and_eq_true_iff.mp hi'
    exact ⟨i, hi, hbit, Nat.eq_of_beq_eq_true hbeq⟩

private theorem ksHB_outT_spec {I : Nat → Nat → Nat} {n m q : Nat} {R : Nat → Nat}
    (h : outT I n m (fun s => R (s + 1)) q = true) :
    (∃ s < 8, R (s + 1) = q) ∨
      ∃ a < n, ∃ c < n, bit m a = true ∧ bit m c = true ∧
        I a q ≠ q ∧ I c q ≠ q ∧ I a q ≠ I c q := by
  unfold outT at h
  rw [Bool.or_eq_true_iff] at h
  rcases h with hin | hout
  · left
    unfold inBlk at hin
    obtain ⟨s, hs, hb⟩ := ksHB_anyN_spec hin
    exact ⟨s, hs, Nat.eq_of_beq_eq_true hb⟩
  · right
    simp only [Bool.and_eq_true_iff] at hout
    obtain ⟨⟨⟨⟨⟨⟨ha, hc⟩, hba⟩, hbc⟩, hIa⟩, hIc⟩, hIac⟩ := hout
    refine ⟨R (8 + 2 * q + 1), ?_, R (9 + 2 * q + 1), ?_, hba, hbc, ?_, ?_, ?_⟩
    · rw [Nat.blt_eq] at ha
      simpa using ha
    · rw [Nat.blt_eq] at hc
      simpa using hc
    · change (!Nat.beq (I (R (8 + 2 * q + 1)) q) q) = true at hIa
      intro heq
      rw [heq, Nat.beq_refl, Bool.not_true] at hIa
      exact Bool.false_ne_true hIa
    · change (!Nat.beq (I (R (9 + 2 * q + 1)) q) q) = true at hIc
      intro heq
      rw [heq, Nat.beq_refl, Bool.not_true] at hIc
      exact Bool.false_ne_true hIc
    · change (!Nat.beq (I (R (8 + 2 * q + 1)) q) (I (R (9 + 2 * q + 1)) q)) = true
        at hIac
      intro heq
      rw [heq, Nat.beq_refl, Bool.not_true] at hIac
      exact Bool.false_ne_true hIac

theorem eT_bad {I A : Nat → Nat → Nat} {F0 : List Nat} {n m : Nat} {R : Nat → Nat}
    (h : eT I A F0 n m R = true) (h0 : R 0 ≠ 0) :
    (∀ s < 8, ∀ s' < 8, R (s + 1) = R (s' + 1) → s = s') ∧
    (∀ b < 4, R (2 * b + 1) < 100 ∧ R (2 * b + 2) < 100 ∧
      (∀ i < n, bit m i = true → I i (R (2 * b + 1)) = R (2 * b + 1) ∨
        I i (R (2 * b + 1)) = R (2 * b + 2)) ∧
      ∃ i < n, bit m i = true ∧ I i (R (2 * b + 1)) = R (2 * b + 2)) ∧
    ∀ q < 100, (∃ s < 8, R (s + 1) = q) ∨
      ∃ a < n, ∃ c < n, bit m a = true ∧ bit m c = true ∧ I a q ≠ q ∧ I c q ≠ q ∧ I a q ≠ I c q := by
  unfold eT at h
  have hb : Nat.beq (R 0) 0 = false := by
    by_cases hbe : Nat.beq (R 0) 0 = true
    · rw [Nat.beq_eq] at hbe
      exact absurd hbe h0
    · exact Bool.eq_false_of_ne_true hbe
  rw [hb, Bool.cond_false] at h
  unfold badK at h
  simp only [Bool.and_eq_true_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro s hs s' hs' he
    have hss := allN_spec h1 s hs
    have hss' := allN_spec hss s' hs'
    change (Nat.beq s s' || !Nat.beq (R (s + 1)) (R (s' + 1))) = true at hss'
    rw [he] at hss'
    simpa using hss'
  · intro b hb'
    exact ksHB_blkT_spec (by simpa using allN_spec h2 b hb')
  · intro q hq
    exact ksHB_outT_spec (by simpa using allN_spec h3 q hq)

private theorem ksHB_cntF_eq (f : Nat → Nat) :
    cntF f = ((List.range 100).filter fun q => f q == q).length := by
  unfold cntF
  rw [foldN_eq]
  induction (List.range 100) with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    have hb : (f x == x) = Nat.beq (f x) x := rfl
    rw [hb]
    cases Nat.beq (f x) x <;> simp

theorem fix5K_spec {F : Nat → Nat → Nat} {N b : Nat} (h : fix5K F N b = true) :
    ∀ k < N, (∀ q < 100, F k q = q) ∨ ((List.range 100).filter fun q => F k q == q).length ≤ b := by
  intro k hk
  unfold fix5K at h
  have hk' := allN_spec h k hk
  rw [Bool.or_eq_true_iff] at hk'
  rcases hk' with heq | hcnt
  · left
    unfold eqF at heq
    rw [allN_iff] at heq
    intro q hq
    have hq' := heq q hq
    rw [Nat.beq_eq] at hq'
    exact hq'
  · right
    rw [Nat.ble_eq] at hcnt
    exact ksHB_cntF_eq (F k) ▸ hcnt

end CFSG.KC.HS589206E16

end
