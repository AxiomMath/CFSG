module

public import CFSG.Certificates.Kernel.G2Three.Sec1Tab
public import CFSG.Certificates.Kernel.G2Three.Sec1Group

public section

namespace CFSG.KC.G2Three.Sec1

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.G2Three CFSG.KD.G2Three.Sec1

@[expose] def m9 (c : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  fun i j => if c.testBit (3 * j.val + i.val) then 1 else 0

theorem fld7_bit (M a : ℕ) {i : ℕ} (hi : i < 3) :
    (Nat.land (Nat.shiftRight M a) 7).testBit i = M.testBit (a + i) := by
  change ((M >>> a) &&& 7).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  interval_cases i <;> simp [show Nat.testBit 7 0 = true by decide,
    show Nat.testBit 7 1 = true by decide, show Nat.testBit 7 2 = true by decide]

theorem fld7_bit_hi (M a : ℕ) {i : ℕ} (hi : 3 ≤ i) :
    (Nat.land (Nat.shiftRight M a) 7).testBit i = false := by
  change ((M >>> a) &&& 7).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : 7 < 2 ^ 3)
    (Nat.pow_le_pow_right (by norm_num) hi)), Bool.and_false]

theorem testBit_brec (b : Bool) (acc f i : ℕ) :
    (Bool.rec (motive := fun _ => ℕ) acc (Nat.xor acc f) b).testBit i =
      (acc.testBit i ^^ (b && f.testBit i)) := by
  cases b
  · simp
  · change (acc ^^^ f).testBit i = _
    simp [Nat.testBit_xor]

theorem colC_eq (M v : ℕ) : colC M v =
    Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ) 0 (Nat.xor 0 (Nat.land (Nat.shiftRight M 0) 7))
          (v.testBit 0))
        (Nat.xor (Bool.rec (motive := fun _ => ℕ) 0 (Nat.xor 0 (Nat.land (Nat.shiftRight M 0) 7))
          (v.testBit 0)) (Nat.land (Nat.shiftRight M 3) 7)) (v.testBit 1))
      (Nat.xor (Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ) 0 (Nat.xor 0 (Nat.land (Nat.shiftRight M 0) 7))
          (v.testBit 0))
        (Nat.xor (Bool.rec (motive := fun _ => ℕ) 0 (Nat.xor 0 (Nat.land (Nat.shiftRight M 0) 7))
          (v.testBit 0)) (Nat.land (Nat.shiftRight M 3) 7)) (v.testBit 1))
        (Nat.land (Nat.shiftRight M 6) 7)) (v.testBit 2) := by
  rw [← blt_land_bit, ← blt_land_bit, ← blt_land_bit]
  rfl

theorem colC_bit (M v : ℕ) {i : ℕ} (hi : i < 3) :
    (colC M v).testBit i = (((v.testBit 0 && M.testBit i) ^^ (v.testBit 1 && M.testBit (3 + i))) ^^
      (v.testBit 2 && M.testBit (6 + i))) := by
  rw [colC_eq]
  simp only [testBit_brec, fld7_bit _ _ hi, Nat.zero_testBit, Bool.false_xor, Nat.zero_add]

theorem colC_bit_hi (M v : ℕ) {i : ℕ} (hi : 3 ≤ i) : (colC M v).testBit i = false := by
  rw [colC_eq]
  simp only [testBit_brec, fld7_bit_hi _ _ hi, Nat.zero_testBit, Bool.false_xor, Bool.and_false,
    Bool.xor_false]

theorem testBit_lor_shl (acc c s t : ℕ) :
    (Nat.lor acc (Nat.shiftLeft c s)).testBit t =
      (acc.testBit t || (decide (s ≤ t) && c.testBit (t - s))) := by
  change (acc ||| c <<< s).testBit t = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]

theorem MUL9_eq (M N : ℕ) : MUL9 M N =
    Nat.lor (Nat.lor (Nat.lor 0 (Nat.shiftLeft (colC M (Nat.land (Nat.shiftRight N 0) 7)) 0))
      (Nat.shiftLeft (colC M (Nat.land (Nat.shiftRight N 3) 7)) 3))
      (Nat.shiftLeft (colC M (Nat.land (Nat.shiftRight N 6) 7)) 6) := rfl

theorem MUL9_bit (M N : ℕ) {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    (MUL9 M N).testBit (3 * j + i) =
      (colC M (Nat.land (Nat.shiftRight N (3 * j)) 7)).testBit i := by
  rw [MUL9_eq]
  simp only [testBit_lor_shl, Nat.zero_testBit, Bool.false_or]
  interval_cases j <;> interval_cases i <;> simp [colC_bit_hi]

theorem MUL9_bit_hi (M N : ℕ) {t : ℕ} (ht : 9 ≤ t) : (MUL9 M N).testBit t = false := by
  rw [MUL9_eq]
  simp only [testBit_lor_shl, Nat.zero_testBit, Bool.false_or]
  rw [colC_bit_hi _ _ (by omega), colC_bit_hi _ _ (by omega), colC_bit_hi _ _ (by omega)]
  simp

theorem MUL9_lt (M N : ℕ) : MUL9 M N < 512 :=
  Nat.lt_pow_two_of_testBit (n := 9) _ fun _ ht => MUL9_bit_hi M N ht

theorem ind_xor3 (a0 a1 a2 b0 b1 b2 : Bool) :
    (if ((b0 && a0) ^^ (b1 && a1)) ^^ (b2 && a2) then (1 : ZMod 2) else 0) =
      (if a0 then 1 else 0) * (if b0 then 1 else 0) +
        (if a1 then 1 else 0) * (if b1 then 1 else 0) +
        (if a2 then 1 else 0) * (if b2 then 1 else 0) := by
  cases a0 <;> cases a1 <;> cases a2 <;> cases b0 <;> cases b1 <;> cases b2 <;> decide

theorem m9_MUL9 (M N : ℕ) : m9 (MUL9 M N) = m9 M * m9 N := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp only [m9]
  rw [MUL9_bit _ _ hi hj, colC_bit _ _ hi, fld7_bit _ _ (by norm_num), fld7_bit _ _ (by norm_num),
    fld7_bit _ _ (by norm_num)]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.mul_zero, Nat.zero_add, Nat.mul_one,
    Nat.add_zero]
  exact ind_xor3 _ _ _ _ _ _

theorem m9_inj {a b : ℕ} (ha : a < 512) (hb : b < 512) (h : m9 a = m9 b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 9
  · have hij := congrFun (congrFun h ⟨t % 3, Nat.mod_lt _ (by norm_num)⟩) ⟨t / 3, by omega⟩
    simp only [m9] at hij
    have et : 3 * (t / 3) + t % 3 = t := Nat.div_add_mod t 3
    rw [et] at hij
    cases ha' : a.testBit t <;> cases hb' : b.testBit t <;> simp [ha', hb'] at hij ⊢
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega) :
      2 ^ 9 ≤ 2 ^ t)), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right
      (by norm_num) (by omega) : 2 ^ 9 ≤ 2 ^ t))]

theorem clos9_at {X G POS : ℕ → ℕ} {n k hi : ℕ} (h : clos9 X G POS n k hi = true)
    (hm : n * k ≤ 64 * hi) :
    ∀ i < n * k, POS i < n ∧ X (POS i) = MUL9 (X (i / k)) (G (i % k)) := fun i hi' => by
  obtain ⟨h1, h2⟩ := bAnd_g2 (allBelow_g2 h hm i hi')
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

theorem clos9_card {X Gd POS PA PB : ℕ → ℕ} {n k : ℕ} (hn : 0 < n) (h0 : X 0 = 273)
    (hcl : ∀ i < n * k, POS i < n ∧ X (POS i) = MUL9 (X (i / k)) (Gd (i % k)))
    (hpar : ∀ i < n - 1, PA i ≤ i ∧ PB i < k ∧ POS (PA i * k + PB i) = i + 1)
    (hinj : ∀ i < n, ∀ j < n, X i = X j → i = j) :
    n ≤ Nat.card (Submonoid.closure (Set.range fun s : Fin k => m9 (Gd s))) := by
  let C := Submonoid.closure (Set.range fun s : Fin k => m9 (Gd s))
  have hm : ∀ i < n, m9 (X i) ∈ C ∧ X i < 512 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases i with _ | i
      · refine ⟨?_, by rw [h0]; norm_num⟩
        have e1 : m9 (X 0) = 1 := by
          rw [h0]
          ext a b
          fin_cases a <;> fin_cases b <;> decide
        rw [e1]
        exact C.one_mem
      · obtain ⟨hpa, hpb, hpos⟩ := hpar i (by omega)
        obtain ⟨hx, -⟩ := ih (PA i) (by omega) (by omega)
        obtain ⟨hlt, hdv, hmd⟩ := flat_facts (by omega) (show PA i < n by omega) hpb
        obtain ⟨-, hXe⟩ := hcl _ hlt
        rw [hpos, hdv, hmd] at hXe
        rw [hXe, m9_MUL9]
        refine ⟨C.mul_mem hx (Submonoid.subset_closure ⟨⟨PB i, hpb⟩, rfl⟩), MUL9_lt _ _⟩
  have hinj' : Function.Injective (fun i : Fin n => (⟨m9 (X i), (hm i i.2).1⟩ : C)) := by
    intro i j hij
    have e : m9 (X i) = m9 (X j) := congrArg Subtype.val hij
    exact Fin.ext (hinj i i.2 j j.2 (m9_inj (hm i i.2).2 (hm j j.2).2 e))
  have := Nat.card_le_card_of_injective _ hinj'
  rwa [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this

theorem pwG_col {G : Type} [Group G] (g : ℕ → G) (M : ℕ) (j : Fin 3) :
    pwG g 3 ((M >>> (3 * j.val)) &&& 7) = vecE (fun i => g i.val) (fun i => m9 M i j) := by
  have hb : ∀ i < 3, ((M >>> (3 * j.val)) &&& 7).testBit i = M.testBit (3 * j.val + i) :=
    fun i hi => fld7_bit M _ hi
  rw [pwG_succ, pwG_succ, pwG_succ, hb 0 (by norm_num), hb 1 (by norm_num), hb 2 (by norm_num)]
  simp only [vecE, m9, pwG, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero, one_mul]
  cases M.testBit (3 * j.val) <;> cases M.testBit (3 * j.val + 1) <;>
    cases M.testBit (3 * j.val + 2) <;> simp [show ZMod.val (1 : ZMod 2) = 1 from rfl]

end CFSG.KC.G2Three.Sec1

end
