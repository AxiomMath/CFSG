module

public import CFSG.Certificates.Kernel.BenesSound
import Mathlib.Data.Nat.Init

public section

namespace CFSG.KC.YModel.Sch

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.YModel

theorem blt_false' {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false :=
  Bool.eq_false_iff.mpr fun h' => h (Nat.blt_eq.mp h')

theorem testBit_ones' (W q : Nat) : (ones W).testBit q = decide (q < W) := by
  rw [ones_eq, Nat.testBit_two_pow_sub_one]

theorem stBit_eq (k i : Nat) : KDense.stBit k i = if i < k then k - 1 - i else i + 1 - k := by
  unfold KDense.stBit
  by_cases h : i < k
  · rw [Nat.blt_eq.mpr h, if_pos h]
    rfl
  · rw [blt_false' h, if_neg h]
    rfl

theorem stBit_rev {k i : Nat} (hi : i < 2 * k - 1) :
    KDense.stBit k i = KDense.stBit k (2 * k - 1 - 1 - i) := by
  rw [stBit_eq, stBit_eq]
  split <;> split <;> omega

theorem stageShift_rev {k i : Nat} (hi : i < 2 * k - 1) :
    stageShift k i = stageShift k (2 * k - 1 - 1 - i) := by
  rw [stageShift_eq, stageShift_eq, stBit_rev hi]

theorem testBit_orRec (f : Nat → Nat) (q : Nat) : ∀ c,
    (Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (f i)) c).testBit q = true ↔
      ∃ i < c, (f i).testBit q = true
  | 0 => by
    change Nat.testBit 0 q = true ↔ _
    simp
  | c + 1 => by
    change (Nat.lor (Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (f i)) c)
      (f c)).testBit q = true ↔ _
    rw [nlor, Nat.testBit_or, Bool.or_eq_true, testBit_orRec f q c]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨c, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

theorem testBit_benesMask {k N i r : Nat} :
    (benesMask k N i).testBit r = (decide (r < 2 ^ k) && N.testBit (i * 2 ^ k + r)) := by
  unfold benesMask
  rw [nland, nshr, nmul, Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones', Bool.and_comm]

theorem block_eq {W i j r : Nat} (h1 : j * W ≤ i * W + r) (h2 : i * W + r - j * W < W)
    (hr : r < W) : j = i := by
  rcases Nat.lt_trichotomy j i with h | h | h
  · have : (j + 1) * W ≤ i * W := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    omega
  · exact h
  · have : (i + 1) * W ≤ j * W := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    omega

theorem orRec_horner (f : Nat → Nat) (W n : Nat) : ∀ m ≤ n + 1,
    Nat.rec (motive := fun _ => Nat) 0 (fun i acc => acc ||| f i <<< ((n - i) * W)) m =
      Nat.rec (motive := fun _ => Nat) 0 (fun i acc => acc <<< W ||| f i) m <<< ((n + 1 - m) * W)
  | 0, _ => by simp
  | m + 1, hm => by
    simp only [Nat.rec_add_one]
    rw [orRec_horner f W n m (by omega), Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add]
    have e1 : n + 1 - (m + 1) = n - m := by omega
    have e2 : n + 1 - m = n - m + 1 := by omega
    rw [e1, e2, Nat.add_mul, Nat.one_mul, Nat.add_comm W]

theorem netRev_eq (k N : Nat) : netRev k N = Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight N (Nat.mul i (wid k))) (ones (wid k)))
      (Nat.mul (Nat.sub (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 2)) i) (wid k))))
    (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rfl
  have h := orRec_horner (fun i => Nat.land (Nat.shiftRight N (Nat.mul i (wid k))) (ones (wid k)))
    (wid k) (2 * k - 2) (2 * k - 1) (by omega)
  have h1 : 2 * k - 2 + 1 - (2 * k - 1) = 0 := by omega
  rw [h1, Nat.zero_mul, Nat.shiftLeft_zero] at h
  exact h.symm

theorem benesMask_netRev {k N i : Nat} (hi : i < 2 * k - 1) :
    benesMask k (netRev k N) i = benesMask k N (2 * k - 1 - 1 - i) := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_benesMask, testBit_benesMask]
  by_cases hr : r < 2 ^ k
  · rw [decide_eq_true hr, Bool.true_and, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    have hw : wid k = 2 ^ k := Nat.one_shiftLeft k
    rw [netRev_eq, hw, testBit_orRec]
    simp only [nshl, nland, nshr, nmul, nsub, Nat.testBit_shiftLeft, Bool.and_eq_true,
      decide_eq_true_eq, Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones']
    constructor
    · rintro ⟨i', hi', h1, h3, h2⟩
      have e := block_eq h1 h2 hr
      have hi'' : i' = 2 * k - 1 - 1 - i := by omega
      subst hi''
      rw [e, show i * 2 ^ k + r - i * 2 ^ k = r by omega, Nat.add_comm] at h3
      rwa [Nat.add_comm]
    · intro h
      refine ⟨2 * k - 1 - 1 - i, by omega, ?_⟩
      rw [show 2 * k - 2 - (2 * k - 1 - 1 - i) = i by omega,
        show i * 2 ^ k + r - i * 2 ^ k = r by omega]
      exact ⟨by omega, by simpa only [Nat.add_comm] using h, hr⟩
  · rw [decide_eq_false hr, Bool.false_and, Bool.false_and]

theorem stagesValid_netRev {k N : Nat} (h : StagesValid k N) : StagesValid k (netRev k N) := by
  intro i hi
  rw [stageShift_rev hi, benesMask_netRev hi]
  exact h _ (by omega)

theorem benesPerm_netRev {k N : Nat} (r : Nat) : benesPerm k (netRev k N) r = benesInv k N r := by
  unfold benesPerm benesInv
  apply compF_congr 0 (2 * k - 1)
  intro i _ hi
  rw [stageShift_rev (by omega : i < 2 * k - 1), benesMask_netRev (by omega : i < 2 * k - 1)]

theorem recAll_intro {P : Nat → Bool} : ∀ n, (∀ i < n, P i = true) →
    (Nat.rec (motive := fun _ => Bool) true (fun i ih => (Bool.rec false ih (P i) : Bool)) n) = true
  | 0, _ => rfl
  | n + 1, h => by
    change (Bool.rec false (Nat.rec (motive := fun _ => Bool) true
      (fun i ih => (Bool.rec false ih (P i) : Bool)) n) (P n) : Bool) = true
    rw [h n (by omega), recAll_intro n fun i hi => h i (by omega)]

theorem bandB_intro {a b : Bool} (ha : a = true) (hb : b = true) : (Bool.rec false b a : Bool) = true := by
  subst ha
  subst hb
  rfl

theorem netRev_lt {k N : Nat} : netRev k N < 2 ^ ((2 * k - 1) * 2 ^ k) := by
  apply Nat.lt_pow_two_of_testBit
  intro q hq
  cases hc : (netRev k N).testBit q with
  | false => rfl
  | true =>
  exfalso
  have hw : wid k = 2 ^ k := Nat.one_shiftLeft k
  rw [netRev_eq, hw, testBit_orRec] at hc
  obtain ⟨i, hi, hb⟩ := hc
  simp only [nshl, nland, nshr, nmul, nsub, Nat.testBit_shiftLeft, Bool.and_eq_true,
    decide_eq_true_eq, Nat.testBit_and, testBit_ones'] at hb hi
  have e1 : (2 * k - 2 - i + 1) * 2 ^ k ≤ (2 * k - 1) * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at e1
  omega

theorem netOK_netRev {k N : Nat} (h : KDense.netOK k N = true) : KDense.netOK k (netRev k N) = true := by
  obtain ⟨-, h2⟩ := andB_true h
  have h3 := recAll_left _ h2
  unfold KDense.netOK
  refine bandB_intro ?_ (recAll_intro _ fun i hi => ?_)
  · rw [Nat.blt_eq]
    simp only [KDense.wK, nshl, nmul, nsub, Nat.one_shiftLeft]
    exact netRev_lt
  · replace hi : i < 2 * k - 1 := hi
    have hi' : 2 * k - 1 - 1 - i < 2 * k - 1 := by omega
    have h4 := h3 (2 * k - 1 - 1 - i) hi'
    simp only [Nat.beq_eq, KDense.wK, nshl, Nat.one_shiftLeft] at h4 ⊢
    change Nat.land (benesMask k N (2 * k - 1 - 1 - i)) (idPlane (2 ^ k) (KDense.stBit k (2 * k - 1 - 1 - i))) = 0
      at h4
    change Nat.land (benesMask k (netRev k N) i) (idPlane (2 ^ k) (KDense.stBit k i)) = 0
    rw [benesMask_netRev hi, stBit_rev hi]
    exact h4

end CFSG.KC.YModel.Sch

end
