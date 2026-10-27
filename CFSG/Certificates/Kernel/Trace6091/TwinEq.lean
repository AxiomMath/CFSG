module

public import Certificates.Data.Kernel.KDense.Twins
public import CFSG.Monster.B.Rep4371.Model

public section

namespace CFSG.KC.Trace6091

open CFSG.KC CFSG.KC.KDense CFSG.KC.MonsterConv.Perm CFSG.Monster.B

theorem rec_succ (z : Nat) (s : Nat → Nat → Nat) (n : Nat) :
    Nat.rec (motive := fun _ => Nat) z s (n + 1) = s n (Nat.rec (motive := fun _ => Nat) z s n) :=
  rfl

theorem bitN_eq (x i : Nat) : bitN x i = (x.testBit i).toNat := by
  rw [Nat.toNat_testBit]
  change (x >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem selB_toNat (b : Bool) (m : Nat) : selB b.toNat m = if b then m else 0 := by
  cases b
  · exact Nat.zero_mul m
  · exact Nat.one_mul m

theorem toNat_xor (a b : Bool) : (a ^^ b).toNat = a.toNat ^^^ b.toNat := by
  cases a <;> cases b <;> rfl

theorem toNat_and (a b : Bool) : (a && b).toNat = a.toNat &&& b.toNat := by
  cases a <;> cases b <;> rfl

theorem combN_loop (m M : Nat → Nat) (a : Nat) : ∀ n, (∀ i < n, M i = m i) →
    Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.xor acc (selB (bitN a i) (M i))) n =
      Model.combN m n a
  | 0, _ => rfl
  | n + 1, h => by
    rw [rec_succ 0 (fun i acc => Nat.xor acc (selB (bitN a i) (M i))) n,
      combN_loop m M a n (fun i hi => h i (by omega)), bitN_eq, selB_toNat, h n (by omega)]
    simp only [Model.combN]
    rfl

theorem packN_loop (g : Nat → Nat) (f : Nat → Bool) : ∀ n, (∀ k < n, g k = (f k).toNat) →
    Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.lor acc (Nat.shiftLeft (g k) k)) n =
      Model.packN f n
  | 0, _ => rfl
  | n + 1, h => by
    rw [rec_succ 0 (fun k acc => Nat.lor acc (Nat.shiftLeft (g k) k)) n,
      packN_loop g f n (fun k hk => h k (by omega)), h n (by omega)]
    simp only [Model.packN]
    cases f n <;> simp [Nat.one_shiftLeft]

theorem xorSum_loop (g : Nat → Nat) (f : Nat → Bool) : ∀ n, (∀ k < n, g k = (f k).toNat) →
    Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.xor acc (g k)) n =
      (Model.xorSum f n).toNat
  | 0, _ => rfl
  | n + 1, h => by
    rw [rec_succ 0 (fun k acc => Nat.xor acc (g k)) n,
      xorSum_loop g f n (fun k hk => h k (by omega)), h n (by omega)]
    simp only [Model.xorSum]
    rw [toNat_xor]
    rfl

theorem testBit_orLoop (g : Nat → Nat) (t : Nat) : ∀ n,
    (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.lor acc (g k)) n).testBit t = true ↔
      ∃ k < n, (g k).testBit t = true
  | 0 => by
    change Nat.testBit 0 t = true ↔ _
    simp
  | n + 1 => by
    rw [rec_succ 0 (fun k acc => Nat.lor acc (g k)) n]
    change Nat.testBit (_ ||| _) t = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_orLoop g t n]
    constructor
    · rintro (⟨k, hk, h⟩ | h)
      · exact ⟨k, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      by_cases hkn : k = n
      · subst hkn
        exact Or.inr h
      · exact Or.inl ⟨k, by omega, h⟩

theorem xorSum_succ' (f : Nat → Bool) : ∀ k,
    Model.xorSum f (k + 1) = (f 0 ^^ Model.xorSum (fun i => f (i + 1)) k)
  | 0 => by simp [Model.xorSum]
  | k + 1 => by
    rw [Model.xorSum, xorSum_succ' f k, Model.xorSum, Bool.xor_assoc]

theorem parN_eq : ∀ k a, Model.parN k a = Model.xorSum a.testBit k
  | 0, _ => rfl
  | k + 1, a => by
    have ih := parN_eq k (a / 2)
    have hf : (fun i => a.testBit (i + 1)) = (a / 2).testBit := funext fun i => Nat.testBit_succ a i
    unfold Model.parN at ih ⊢
    rw [xorSum_succ', hf, ← ih, Model.popcN, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one (Model.popcN k (a / 2)) with h' | h' <;>
      simp [Nat.add_mod, h, h']

theorem xorSum_congr {f g : Nat → Bool} : ∀ {n}, (∀ i < n, f i = g i) →
    Model.xorSum f n = Model.xorSum g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [Model.xorSum]
    rw [xorSum_congr (fun i hi => h i (by omega)), h n (by omega)]

theorem xorSum_false : ∀ n, Model.xorSum (fun _ => false) n = false
  | 0 => rfl
  | n + 1 => by simp [Model.xorSum, xorSum_false n]

theorem xorSum_add (f : Nat → Bool) (k : Nat) : ∀ m,
    Model.xorSum f (k + m) = (Model.xorSum f k ^^ Model.xorSum (fun i => f (k + i)) m)
  | 0 => by simp [Model.xorSum]
  | m + 1 => by
    rw [← Nat.add_assoc]
    simp only [Model.xorSum]
    rw [xorSum_add f k m, Bool.xor_assoc]

theorem xorSum_xor (f g : Nat → Bool) : ∀ n,
    Model.xorSum (fun i => f i ^^ g i) n = (Model.xorSum f n ^^ Model.xorSum g n)
  | 0 => rfl
  | n + 1 => by
    simp only [Model.xorSum]
    rw [xorSum_xor f g n]
    have h4 : ∀ a b c d : Bool, ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by decide
    exact h4 _ _ _ _

@[expose] def foldX (k x : Nat) : Nat := x ^^^ x >>> k

theorem xorSum_foldX (k x : Nat) :
    Model.xorSum (foldX k x).testBit k = Model.xorSum x.testBit (k + k) := by
  have hf : (foldX k x).testBit = fun i => x.testBit i ^^ x.testBit (k + i) := by
    funext i
    simp [foldX]
  rw [hf, xorSum_xor, xorSum_add]

theorem par24_def (a : Nat) : par24 a =
    foldX 1 (foldX 2 (foldX 4 (foldX 8 (foldX 16 (a &&& (2 ^ 24 - 1)))))) &&& 1 := rfl

theorem par24_eq (a : Nat) : par24 a = (Model.xorSum a.testBit 24).toNat := by
  have h1 : ∀ n : Nat, n &&& 1 = (Model.xorSum n.testBit 1).toNat := fun n => by
    simp only [Model.xorSum, Bool.false_xor]
    rw [Nat.toNat_testBit, Nat.and_one_is_mod, Nat.pow_zero, Nat.div_one]
  rw [par24_def, h1]
  simp only [xorSum_foldX, Nat.reduceAdd]
  congr 1
  rw [(rfl : (32 : Nat) = 24 + 8), xorSum_add _ 24 8]
  have ht : (fun i => (a &&& (2 ^ 24 - 1)).testBit (24 + i)) = fun _ => false := by
    funext i
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    simp
  rw [ht, xorSum_false, Bool.xor_false]
  exact xorSum_congr fun i hi => by
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    simp [hi]

theorem bmT_eq : ∀ i < 12, bmT i = Model.bmaskN i := by decide +kernel

theorem umT_eq : ∀ k < 12, umT k = Model.umaskN k := by decide +kernel

theorem wordT_eq (a : Nat) : wordT a = Model.wordN a :=
  combN_loop Model.bmaskN bmT a 12 bmT_eq

theorem repT_eq (d : Nat) : repT d = Model.repN d :=
  combN_loop Model.umaskN umT d 12 umT_eq

theorem combT_BMS_eq (a : Nat) {n : Nat} (hn : n ≤ 12) :
    combT BMS 24 n a = Model.combN Model.bmaskN n a :=
  combN_loop Model.bmaskN bmT a n (fun i hi => bmT_eq i (by omega))

theorem coeffT_eq (w : Nat) : coeffT w = Model.coeffN w :=
  packN_loop (fun k => par24 (w &&& umT k)) (fun k => Model.parN 24 (w &&& Model.umaskN k)) 12
    (fun k hk => by rw [par24_eq, umT_eq k hk, parN_eq])

theorem dualT_eq (v : Nat) : dualT v = Model.dualN v :=
  packN_loop (fun j => par24 (v &&& bmT j)) (fun j => Model.parN 24 (v &&& Model.bmaskN j)) 12
    (fun j hj => by rw [par24_eq, bmT_eq j hj, parN_eq])

theorem pairT_eq (a d : Nat) : pairT a d = (Model.pairN a d).toNat := by
  change par24 (a &&& d &&& (2 ^ 12 - 1)) = _
  rw [par24_eq]
  unfold Model.pairN
  rw [parN_eq]
  congr 1
  simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Model.xorSum]
  simp only [Nat.reduceLT, decide_true, decide_false, Bool.and_true, Bool.and_false, Bool.xor_false]

theorem betaT_eq : ∀ j < 12, ∀ k < 12, betaT j k = (Model.betaN j k).toNat := by decide +kernel

theorem packBetaT_eq : ∀ n < 12, packBetaT n = Model.packN (Model.betaN n) 12 := by decide +kernel

theorem thetaT_loop (a : Nat) : ∀ n ≤ 12,
    Nat.rec (motive := fun _ => Nat) 0 (fun n acc => Nat.xor acc (selB (bitN a n)
      (Nat.xor (packBetaT n) (dualT (Nat.land (combT BMS 24 n a) (bmT n)))))) n =
      Model.thetaRec n a
  | 0, _ => rfl
  | n + 1, h => by
    rw [rec_succ 0 (fun n acc => Nat.xor acc (selB (bitN a n)
        (Nat.xor (packBetaT n) (dualT (Nat.land (combT BMS 24 n a) (bmT n)))))) n,
      thetaT_loop a n (by omega), bitN_eq, selB_toNat, packBetaT_eq n (by omega), dualT_eq]
    change _ ^^^ (if _ then _ ^^^ Model.dualN (combT BMS 24 n a &&& bmT n) else 0) = _
    rw [combT_BMS_eq a (by omega), bmT_eq n (by omega)]
    simp only [Model.thetaRec]
    cases a.testBit n
    · simp
    · simp [Nat.xor_assoc]

theorem thetaT_eq (a : Nat) : thetaT a = Model.thetaN a :=
  thetaT_loop a 12 (Nat.le_refl 12)

section Perm

variable {P : Nat} {p : Array Nat}

theorem permWordT_eq (hP : ∀ i < 24, pe P i = p[i]!) (w : Nat) :
    permWordT P w = Model.permWordN p w :=
  combN_loop (fun i => 2 ^ p[i]!) (fun i => Nat.shiftLeft 1 (pe P i)) w 24
    (fun i hi => by rw [Nat.shiftLeft_eq', Nat.one_shiftLeft, hP i hi])

theorem permCT_eq (hP : ∀ i < 24, pe P i = p[i]!) (a : Nat) : permCT P a = Model.permCN p a := by
  unfold permCT Model.permCN
  rw [wordT_eq, permWordT_eq hP, coeffT_eq]

theorem permDT_eq (hP : ∀ i < 24, pe P i = p[i]!) (d : Nat) : permDT P d = Model.permDN p d := by
  unfold permDT Model.permDN
  rw [repT_eq, permWordT_eq hP, dualT_eq]

theorem betaPT_eq (hP : ∀ i < 24, pe P i = p[i]!) {i j : Nat} (hi : i < 12) (hj : j < 12) :
    betaPT P i j = (Model.betaPN p i j).toNat := by
  unfold betaPT Model.betaPN Model.thetaBit
  simp only [Nat.shiftLeft_eq', Nat.one_shiftLeft, Nat.xor_eq]
  rw [permCT_eq hP, permCT_eq hP, thetaT_eq, pairT_eq, betaT_eq i hi j hj, toNat_xor]

theorem testBit_toNat (b : Bool) (m : Nat) : b.toNat.testBit m = (b && decide (m = 0)) := by
  cases b
  · simp
  · cases m <;> simp [Nat.testBit_succ]

theorem testBit_betaTabT (hP : ∀ i < 24, pe P i = p[i]!) {i j : Nat} (hi : i < 12) (hj : j < 12) :
    (betaTabT P).testBit (12 * i + j) = Model.betaPN p i j := by
  apply Bool.eq_iff_iff.mpr
  have hin : ∀ i', (Nat.rec (motive := fun _ => Nat) 0 (fun j acc2 => Nat.lor acc2
      (Nat.shiftLeft (betaPT P i' j) (Nat.add (Nat.mul 12 i') j))) 12).testBit (12 * i + j) = true ↔
      ∃ j' < 12, (Nat.shiftLeft (betaPT P i' j') (Nat.add (Nat.mul 12 i') j')).testBit
        (12 * i + j) = true :=
    fun i' => testBit_orLoop (fun j' => Nat.shiftLeft (betaPT P i' j') (Nat.add (Nat.mul 12 i') j'))
      _ 12
  refine (testBit_orLoop (fun i' => Nat.rec (motive := fun _ => Nat) 0 (fun j acc2 => Nat.lor acc2
      (Nat.shiftLeft (betaPT P i' j) (Nat.add (Nat.mul 12 i') j))) 12) _ 12).trans ?_
  constructor
  · rintro ⟨i', hi', h⟩
    obtain ⟨j', hj', h⟩ := (hin i').mp h
    rw [Nat.shiftLeft_eq', Nat.testBit_shiftLeft, betaPT_eq hP hi' hj', testBit_toNat] at h
    simp only [Nat.mul_eq, Nat.add_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hge, hb, h0⟩ := h
    have hii : i' = i := by omega
    have hjj : j' = j := by omega
    subst hii hjj
    exact hb
  · intro h
    refine ⟨i, hi, (hin i).mpr ⟨j, hj, ?_⟩⟩
    rw [Nat.shiftLeft_eq', Nat.testBit_shiftLeft, betaPT_eq hP hi hj, testBit_toNat]
    simp [h]

theorem blt_toNat (i j : Nat) :
    Bool.rec (motive := fun _ => Nat) 0 1 (Nat.blt i j) = (decide (i < j)).toNat := by
  have h : Nat.blt i j = decide (i < j) := Bool.eq_iff_iff.mpr (by simp [Nat.blt_eq])
  rw [h]
  cases decide (i < j) <;> rfl

theorem kappaT_eq (hP : ∀ i < 24, pe P i = p[i]!) (a : Nat) :
    kappaT (betaTabT P) a = (Model.kappaN p a).toNat := by
  unfold Model.kappaN
  refine xorSum_loop (fun i => Nat.rec (motive := fun _ => Nat) 0 (fun j acc2 => Nat.xor acc2
      (Nat.land (Nat.land (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.blt i j))
        (Nat.land (bitN a i) (bitN a j))) (bitN (betaTabT P) (Nat.add (Nat.mul 12 i) j)))) 12)
    _ 12 (fun i hi => ?_)
  refine xorSum_loop (fun j => Nat.land (Nat.land (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.blt i j))
      (Nat.land (bitN a i) (bitN a j))) (bitN (betaTabT P) (Nat.add (Nat.mul 12 i) j)))
    _ 12 (fun j hj => ?_)
  rw [blt_toNat, bitN_eq, bitN_eq, bitN_eq]
  change _ &&& _ &&& ((betaTabT P).testBit (12 * i + j)).toNat = _
  rw [testBit_betaTabT hP hi hj]
  simp only [Nat.land_eq, ← toNat_and, Bool.and_assoc]

end Perm

end CFSG.KC.Trace6091

end
