module

public import CFSG.Certificates.Kernel.O8UnitSound
public import CFSG.Certificates.Kernel.O8CentOrbSound
import CFSG.Certificates.Kernel.O8ColFixSound

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.UnitarySix.YamadaPar
  CFSG.EvenSmallLie.OmegaEight.N3Split

@[expose] def parFold (s x : ℕ) : ℕ := x ^^^ x >>> s

@[expose] noncomputable def parRow12 (x : ℕ) : ℕ :=
  (parFold 1 (parFold 3 (parFold 6 x)) ^^^ parFold 3 (parFold 6 x) >>> 2) &&& low12

@[expose] def idDiagK : ℕ := 11151733894906779683522195341810241573494785

@[expose] def rowRepK : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 2 ^ 12 * rowRepK n

@[expose] def chainLB : List ℕ → Bool
  | a :: b :: t => Nat.blt b (2 ^ Nat.log2 a) && chainLB (b :: t)
  | _ => true

@[expose] noncomputable def fixLBP (c : ℕ) (ws : List ℕ) : Bool :=
  ws.all (fun w => decide (w < 4096) && decide (w ≠ 0) && parRow12 (c &&& (w * low12)) == 0) &&
    chainLB ws

theorem log2_lt_trans {a b c : ℕ} (h1 : b < 2 ^ Nat.log2 a) (h2 : c < 2 ^ Nat.log2 b) :
    c < 2 ^ Nat.log2 a := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [Nat.log2_zero, pow_zero, Nat.lt_one_iff] at h2
    subst h2
    positivity
  · exact lt_of_lt_of_le h2 ((Nat.log2_self_le hb.ne').trans h1.le)

theorem chainLB_iff : ∀ ws : List ℕ,
    chainLB ws = true ↔ ws.Pairwise fun a b => b < 2 ^ Nat.log2 a
  | [] => by simp [chainLB]
  | [a] => by simp [chainLB]
  | a :: b :: t => by
    rw [chainLB, Bool.and_eq_true, Nat.blt_eq, chainLB_iff (b :: t),
      List.pairwise_cons (l := b :: t)]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun x hx => ?_, h2⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h1
      · exact log2_lt_trans h1 (List.rel_of_pairwise_cons h2 hx)
    · rintro ⟨h1, h2⟩
      exact ⟨h1 b List.mem_cons_self, h2⟩

theorem testBit_parFold (s x p : ℕ) :
    (parFold s x).testBit p = (x.testBit p ^^ x.testBit (s + p)) := by
  rw [parFold, Nat.testBit_xor, Nat.testBit_shiftRight]

theorem testBit_parRow12 (x : ℕ) {i : ℕ} (hi : i < 12) :
    bz ((parRow12 x).testBit (12 * i)) = ∑ t : Fin 12, bz (x.testBit (12 * i + t)) := by
  have hd : (12 * i < 144 ∧ 12 * i % 12 = 0) := by omega
  rw [parRow12, Nat.testBit_and, low12_testBit, decide_eq_true hd, Bool.and_true,
    Nat.testBit_xor, Nat.testBit_shiftRight]
  simp only [testBit_parFold, bz_xor, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_succ,
    Fin.val_zero]
  ring_nf

theorem testBit_rowRepK {w : ℕ} (hw : w < 4096) :
    ∀ n i t : ℕ, i < n → t < 12 → (w * rowRepK n).testBit (12 * i + t) = w.testBit t
  | 0, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, t, hi, ht => by
    have e : w * rowRepK (n + 1) = 2 ^ 12 * (w * rowRepK n) + w := by
      rw [rowRepK]
      ring
    rw [e, Nat.testBit_two_pow_mul_add _ (by simpa using hw)]
    rcases i with _ | i
    · simp [ht]
    · have h1 : ¬ 12 * (i + 1) + t < 12 := by omega
      simp only [h1, ↓reduceIte]
      rw [show 12 * (i + 1) + t - 12 = 12 * i + t by omega]
      exact testBit_rowRepK hw n i t (by omega) ht

theorem testBit_mul_low12 {w : ℕ} (hw : w < 4096) {i t : ℕ} (hi : i < 12) (ht : t < 12) :
    (w * low12).testBit (12 * i + t) = w.testBit t := by
  have e : low12 = rowRepK 12 := by decide +kernel
  rw [e]
  exact testBit_rowRepK hw 12 i t hi ht

theorem testBit_idDiagK {i t : ℕ} (hi : i < 12) (ht : t < 12) :
    idDiagK.testBit (12 * i + t) = decide (t = i) := by
  have h : ∀ i < 12, ∀ t < 12, idDiagK.testBit (12 * i + t) = decide (t = i) := by
    decide +kernel
  exact h i hi t ht

theorem bz_parRow12_row (k : ℕ) {w i : ℕ} (hw : w < 4096) (hi : i < 12) :
    bz ((parRow12 ((k ^^^ idDiagK) &&& (w * low12))).testBit (12 * i)) =
      bz ((mulVecK k w).testBit i) + bz (w.testBit i) := by
  have e := congrFun (toVec_mulVecK k w) ⟨i, hi⟩
  simp only [toVec, toMatK, Matrix.mulVec, dotProduct, Matrix.of_apply] at e
  have hx : ∀ t : Fin 12, bz (((k ^^^ idDiagK) &&& (w * low12)).testBit (12 * i + t)) =
      bz (k.testBit (12 * i + t)) * bz (w.testBit t) +
        bz (decide ((t : ℕ) = i)) * bz (w.testBit t) := fun t => by
    rw [Nat.testBit_and, Nat.testBit_xor, testBit_idDiagK hi t.isLt, testBit_mul_low12 hw hi t.isLt,
      bz_and, bz_xor, add_mul]
  have hs : ∑ t : Fin 12, bz (decide ((t : ℕ) = i)) * bz (w.testBit t) = bz (w.testBit i) := by
    rw [Finset.sum_eq_single ⟨i, hi⟩ (fun t _ ht => by
      have h : (t : ℕ) ≠ i := fun h => ht (Fin.ext h)
      simp [h]) (by simp)]
    simp
  rw [testBit_parRow12 _ hi, Finset.sum_congr rfl (fun t _ => hx t), Finset.sum_add_distrib, e, hs]

theorem mulVecK_beq_par (k : ℕ) {w : ℕ} (hw : w < 4096) :
    (mulVecK k w == w) = (parRow12 ((k ^^^ idDiagK) &&& (w * low12)) == 0) := by
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.zero_testBit]
    by_cases hp : p < 144 ∧ p % 12 = 0
    · obtain ⟨i, rfl⟩ : ∃ i, p = 12 * i := ⟨p / 12, by omega⟩
      have hi : i < 12 := by omega
      apply bz_injective
      rw [bz_parRow12_row k hw hi, h]
      cases w.testBit i <;> decide
    · rw [parRow12, Nat.testBit_and, low12_testBit, decide_eq_false hp, Bool.and_false]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 12
    · have e := bz_parRow12_row k hw hi
      rw [h, Nat.zero_testBit, bz_false] at e
      revert e
      cases (mulVecK k w).testBit i <;> cases w.testBit i <;> decide
    · have h4 : (4096 : ℕ) ≤ 2 ^ i := by
        have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show 12 ≤ i by omega)
        simpa using this
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (mulVecK_lt k w) h4),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hw h4)]

theorem fixLB_eq_P (k : ℕ) (ws : List ℕ) : fixLB k ws = fixLBP (k ^^^ idDiagK) ws := by
  have e : decide (ws.Pairwise fun a b => b < 2 ^ Nat.log2 a) = chainLB ws := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, chainLB_iff]
  rw [fixLB, fixLBP, e]
  congr 2
  funext w
  by_cases hw : w < 4096
  · rw [mulVecK_beq_par k hw]
  · simp [hw]

theorem sumN_congr_lt : ∀ (n : ℕ) {f g : ℕ → ℕ}, (∀ v < n, f v = g v) →
    CFSG.KLie.CT.sumN n f = CFSG.KLie.CT.sumN n g
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
    change Nat.add (f n) (CFSG.KLie.CT.sumN n f) = Nat.add (g n) (CFSG.KLie.CT.sumN n g)
    rw [h n (Nat.lt_succ_self n), sumN_congr_lt n fun v hv => h v (Nat.lt_succ_of_lt hv)]

theorem fixCount_eq_P (k : ℕ) : fixCount k = CFSG.KLie.CT.sumN 4096 fun v =>
    nIf(Nat.beq (parRow12 ((k ^^^ idDiagK) &&& (v * low12))) 0, 1, 0) := by
  rw [fixCount_eq]
  refine sumN_congr_lt 4096 fun v hv => ?_
  have e : Nat.beq (mulVec12K k v) v = Nat.beq (parRow12 ((k ^^^ idDiagK) &&& (v * low12))) 0 := by
    have h := mulVecK_beq_par k hv
    rw [mulVecK_eq] at h
    exact h
  rw [e]

theorem fixesOn_P {vs : List ℕ} (hv : ∀ v ∈ vs, v < 4096) (c : ℕ) :
    fixesOn vs c = vs.all fun v => parRow12 ((c ^^^ idDiagK) &&& (v * low12)) == 0 := by
  apply Bool.eq_iff_iff.2
  simp only [fixesOn, List.all_eq_true]
  exact forall₂_congr fun v hv' => by rw [mulVecK_beq_par c (hv v hv')]

theorem fixesOn_fixVecs_basis {s : ℕ} {B : List ℕ} (hB : fixLB s B = true)
    (hc : fixCount s = 2 ^ B.length) (c : ℕ) : fixesOn (fixVecs s) c = fixesOn B c := by
  rw [fixLB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hB
  obtain ⟨hB1, hp⟩ := hB
  have hb : ∀ w ∈ B, w < 4096 ∧ w ≠ 0 ∧ mulVecK s w = w := fun w hw => by
    have h := hB1 w hw
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have h12 : (4096 : ℕ) = 2 ^ 12 := by norm_num
  have hsub : spanF B ⊆ (Finset.range 4096).filter fun v => mulVecK s v = v := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range, h12]
    exact ⟨lt_of_mem_spanF (fun w hw => h12 ▸ (hb w hw).1) x hx,
      fixed_of_mem_spanF (fun w hw => (hb w hw).2.2) x hx⟩
  have hF : ((Finset.range 4096).filter fun v => mulVecK s v = v).card = fixCount s := rfl
  have heq : spanF B = (Finset.range 4096).filter fun v => mulVecK s v = v := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hF, hc, card_spanF hp (fun w hw => (hb w hw).2.1)]
  apply Bool.eq_iff_iff.2
  simp only [fixesOn, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h w hw
    exact h w (mem_fixVecs.2 ⟨(hb w hw).1, (hb w hw).2.2⟩)
  · intro h v hv
    have hv' : v ∈ spanF B := by
      rw [heq, Finset.mem_filter, Finset.mem_range]
      exact mem_fixVecs.1 hv
    exact fixed_of_mem_spanF h v hv'

theorem commKer_of_orb {gs : Array (ℕ × ℕ)} {E : Enum} (hE : enumOK gs E = true) {s : ℕ}
    (ts : List (ℕ × ℕ)) (ks : List ℕ)
    (hts : ts.all (fun p => decide (p.1 < E.keys.size) && decide (p.2 < E.keys.size) &&
      mulK (E.keys.getD p.1 0) s == mulK (E.keys.getD p.2 0) (E.keys.getD p.1 0)) = true)
    (hys : ((ts.map Prod.snd).zip (ts.map Prod.snd).tail).all (fun p => decide (p.1 < p.2)) = true)
    (hks : ks.all (fun i => decide (i < E.keys.size) &&
      (mulK (E.keys.getD i 0) s == mulK s (E.keys.getD i 0))) = true)
    (hkz : (ks.zip ks.tail).all (fun p => decide (p.1 < p.2)) = true)
    (hcard : E.keys.size ≤ ts.length * ks.length) : commCount E s = ks.length ∧
      ∀ vs, kerOn E s vs = (ks.filter fun i => fixesOn vs (E.keys.getD i 0)).length :=
  ⟨commCount_of_orb hE ts ks hts hys hks hkz hcard,
    fun vs => kerOn_of_orb hE vs ts ks hts hys hks hkz hcard⟩

@[expose] def spread12K : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, x => x % 2 + 2 ^ 12 * spread12K n (x / 2)

theorem testBit_spread12K : ∀ (n x i : ℕ) {t : ℕ}, t < 12 →
    (spread12K n x).testBit (12 * i + t) = (decide (t = 0 ∧ i < n) && x.testBit i)
  | 0, x, i, t, _ => by simp [spread12K]
  | n + 1, x, i, t, ht => by
    have hb : x % 2 < 2 ^ 12 := lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
    rw [spread12K, Nat.add_comm, Nat.testBit_two_pow_mul_add _ hb]
    rcases i with _ | i
    · have e : x % 2 = x % 2 ^ 1 := by norm_num
      simp only [Nat.mul_zero, Nat.zero_add, ht, ↓reduceIte]
      rw [e, Nat.testBit_mod_two_pow]
      rcases t with _ | t <;> simp
    · have h1 : ¬ 12 * (i + 1) + t < 12 := by omega
      have h2 : 12 * (i + 1) + t - 12 = 12 * i + t := by omega
      simp only [h1, ↓reduceIte]
      rw [h2,testBit_spread12K n (x / 2) i ht, Nat.testBit_div_two]
      simp

theorem and_low12_eq_spread12K (k : ℕ) : k &&& low12 = spread12K 12 (mulVecK k 1) := by
  apply Nat.eq_of_testBit_eq
  intro p
  obtain ⟨i, t, ht, rfl⟩ : ∃ i t, t < 12 ∧ p = 12 * i + t :=
    ⟨p / 12, p % 12, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod p 12).symm⟩
  rw [Nat.testBit_and, low12_testBit, testBit_spread12K 12 _ i ht]
  by_cases hi : i < 12
  · have h := testBit_mulVecK_pow k hi (j := 0) (by norm_num)
    rw [pow_zero, Nat.add_zero] at h
    rw [h]
    rcases t with _ | t
    · have h2 : 12 * i + 0 < 144 ∧ (12 * i + 0) % 12 = 0 := by omega
      have h3 : 0 = 0 ∧ i < 12 := ⟨rfl, hi⟩
      rw [decide_eq_true h2, decide_eq_true h3, Bool.and_true, Bool.true_and, Nat.add_zero]
    · have h2 : ¬ (12 * i + (t + 1) < 144 ∧ (12 * i + (t + 1)) % 12 = 0) := by omega
      have h3 : ¬ (t + 1 = 0 ∧ i < 12) := by omega
      rw [decide_eq_false h2, decide_eq_false h3, Bool.and_false, Bool.false_and]
  · have h2 : ¬ (12 * i + t < 144 ∧ (12 * i + t) % 12 = 0) := by omega
    have h3 : ¬ (t = 0 ∧ i < 12) := by omega
    rw [decide_eq_false h2, decide_eq_false h3, Bool.and_false, Bool.false_and]

@[expose] noncomputable def col0M (k : ℕ) : ℕ :=
  (((k &&& low12) * 2659754699919401766201267083003561985) >>> 121) &&& 4095

theorem col0M_spread12K {x : ℕ} (hx : x < 4096) : col0M (spread12K 12 x) = x := by
  have h : ∀ a < 64, ∀ b < 64, col0M (spread12K 12 (a + 64 * b)) = a + 64 * b := by
    decide +kernel
  have e := h (x % 64) (Nat.mod_lt _ (by norm_num)) (x / 64) (by omega)
  rwa [Nat.mod_add_div] at e

theorem col0M_eq (k : ℕ) : col0M k = mulVecK k 1 := by
  have e : col0M k = col0M (k &&& low12) := by
    simp only [col0M, Nat.and_assoc, Nat.and_self]
  rw [e, and_low12_eq_spread12K, col0M_spread12K (mulVecK_lt k 1)]

theorem mulVecK_shiftRight_one (k : ℕ) {j : ℕ} (hj : j < 12) :
    mulVecK (k >>> j) 1 = mulVecK k (2 ^ j) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have h := testBit_mulVecK_pow (k >>> j) hi (j := 0) (by norm_num)
    rw [pow_zero, Nat.add_zero] at h
    rw [h, Nat.testBit_shiftRight, testBit_mulVecK_pow k hi hj, Nat.add_comm]
  · have h4 : (4096 : ℕ) ≤ 2 ^ i := by
      have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show 12 ≤ i by omega)
      simpa using this
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (mulVecK_lt _ _) h4),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (mulVecK_lt k _) h4)]

@[expose] noncomputable def sqPreK (j k : ℕ) : Bool :=
  parRow12 ((k ^^^ idDiagK) &&& ((2 ^ j ^^^ col0M (k >>> j)) * low12)) != 0

theorem mulK_sq_ne_of_sqPreK {j k : ℕ} (hj : j < 12) (h : sqPreK j k = true) : mulK k k ≠ idK := by
  intro hk
  have hp : 2 ^ j < 2 ^ 12 := Nat.pow_lt_pow_right (by norm_num) hj
  have hw : 2 ^ j ^^^ mulVecK k (2 ^ j) < 4096 := xor_lt (m := 12) hp (mulVecK_lt k _)
  have h2 : mulVecK k (mulVecK k (2 ^ j)) = 2 ^ j := by
    apply toVec_injOn (mulVecK_lt _ _) hp
    rw [toVec_mulVecK, toVec_mulVecK, Matrix.mulVec_mulVec, ← toMatK_mulK, hk, toMatK_idK,
      Matrix.one_mulVec]
  have hfix : mulVecK k (2 ^ j ^^^ mulVecK k (2 ^ j)) = 2 ^ j ^^^ mulVecK k (2 ^ j) := by
    rw [mulVecK_xor, h2, Nat.xor_comm]
  have e := mulVecK_beq_par k hw
  rw [hfix, beq_self_eq_true, ← mulVecK_shiftRight_one k hj, ← col0M_eq] at e
  rw [sqPreK, bne, ← e] at h
  exact absurd h (by decide)

theorem mulK_sq_bne {j : ℕ} (hj : j < 12) (k : ℕ) :
    (mulK k k != idK) = (sqPreK j k || mul12K k k != ID12) := by
  rw [← mulK_eq, ← idK_eq]
  cases hp : sqPreK j k
  · rw [Bool.false_or]
  · rw [Bool.true_or]
    exact bne_iff_ne.2 (mulK_sq_ne_of_sqPreK hj hp)

end CFSG.KC.O8

end
