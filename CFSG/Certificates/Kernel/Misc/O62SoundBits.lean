module

public import Certificates.Data.Kernel.Misc.O62
public import CFSG.LargeExtraspecial.O62Check

public section

namespace CFSG.KC.Misc.O62

open CFSG.KC.Ord CFSG.KC.Misc
open CFSG.KC.LQT.P (letB impB allN anyN allL anyL)
open CFSG.LargeExtraspecial.O62

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by cases y <;> rfl

theorem letLN_eq (y : ℕ) (k : ℕ → List ℕ) : letLN y k = k y := by cases y <;> rfl

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by cases y <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem impB_eq (a b : Bool) : impB a b = (!a || b) := by cases a <;> rfl

theorem beq_eq_decide (a b : ℕ) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.2 (by simp)

theorem allN_iff (m : ℕ) (f : ℕ → Bool) : allN m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => simp [allN]
  | succ m ih =>
    have e : allN (m + 1) f = andB (f m) (allN m f) := rfl
    rw [e, andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h m (Nat.lt_succ_self m), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem anyN_iff (m : ℕ) (f : ℕ → Bool) : anyN m f = true ↔ ∃ i < m, f i = true := by
  induction m with
  | zero => simp [anyN]
  | succ m ih =>
    have e : anyN (m + 1) f = orB (f m) (anyN m f) := rfl
    rw [e, orB_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨m, Nat.lt_succ_self m, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem allL_eq (l : List ℕ) (f : ℕ → Bool) : allL l f = l.all f := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have e : allL (x :: t) f = andB (f x) (allL t f) := rfl
    rw [e, andB_eq, ih, List.all_cons]

theorem allLL_eq (l : List (List ℕ)) (f : List ℕ → Bool) : allLL l f = l.all f := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have e : allLL (x :: t) f = andB (f x) (allLL t f) := rfl
    rw [e, andB_eq, ih, List.all_cons]

theorem anyLL_eq (l : List (List ℕ)) (f : List ℕ → Bool) : anyLL l f = l.any f := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have e : anyLL (x :: t) f = orB (f x) (anyLL t f) := rfl
    rw [e, orB_eq, ih, List.any_cons]

theorem memN_eq (x : ℕ) (l : List ℕ) : memN x l = decide (x ∈ l) := by
  unfold memN
  rw [letB_eq]
  induction l with
  | nil => rfl
  | cons z t ih =>
    have e : List.rec (motive := fun _ => Bool) false (fun z _ ih => orB (Nat.beq x z) ih)
        (z :: t) = orB (Nat.beq x z) (List.rec (motive := fun _ => Bool) false
          (fun z _ ih => orB (Nat.beq x z) ih) t) := rfl
    rw [e, orB_eq, ih, beq_eq_decide]
    simp

theorem nodupN_eq (l : List ℕ) : nodupN l = decide l.Nodup := by
  induction l with
  | nil => rfl
  | cons z t ih =>
    have e : nodupN (z :: t) = andB (notB (memN z t)) (nodupN t) := rfl
    rw [e, andB_eq, notB_eq, memN_eq, ih]
    simp [List.nodup_cons]

theorem eqLN_iff (a b : List ℕ) : eqLN a b = true ↔ a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [eqLN]
    | cons y t => simp [eqLN]
  | cons x s ih =>
    cases b with
    | nil => simp [eqLN]
    | cons y t =>
      have e : eqLN (x :: s) (y :: t) = andB (Nat.beq x y) (eqLN s t) := rfl
      rw [e, andB_eq, Bool.and_eq_true, ih]
      simp

theorem lenN_eq (l : List ℕ) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have e : lenN (x :: t) = Nat.succ (lenN t) := rfl
    rw [e, ih]; rfl

theorem lenW_eq (l : List (List ℕ)) : lenW l = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have e : lenW (x :: t) = Nat.succ (lenW t) := rfl
    rw [e, ih]; rfl

theorem parW_eq (w : List ℕ) : parW w = w.length % 2 := by
  induction w with
  | nil => rfl
  | cons a t ih =>
    have e : parW (a :: t) = Nat.xor (parW t) 1 := rfl
    rw [e, ih, List.length_cons]
    rcases Nat.mod_two_eq_zero_or_one t.length with h | h
    · rw [h, show Nat.xor 0 1 = 1 from rfl]; omega
    · rw [h, show Nat.xor 1 1 = 0 from rfl]; omega

theorem cntEven_eq (l : List (List ℕ)) :
    cntEven l = (l.filter fun w => w.length % 2 == 0).length := by
  induction l with
  | nil => rfl
  | cons w t ih =>
    have e : cntEven (w :: t) = Nat.add (cntEven t) (Nat.xor (parW w) 1) := rfl
    rw [e, ih, parW_eq, List.filter_cons]
    rcases Nat.mod_two_eq_zero_or_one w.length with h | h
    · simp [h]
    · simp [h]

theorem isNilN_iff (w : List ℕ) : isNilN w = true ↔ w = [] := by
  cases w <;> simp [isNilN]

theorem codesK_eq (l : List (List ℕ)) : codesK l = l.map wordCK := by
  induction l with
  | nil => rfl
  | cons w t ih =>
    have e : codesK (w :: t) = List.cons (wordCK w) (codesK t) := rfl
    rw [e, ih]; rfl

theorem raw_xor (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl

theorem raw_lor (a b : ℕ) : Nat.lor a b = a ||| b := rfl

theorem raw_land (a b : ℕ) : Nat.land a b = a &&& b := rfl

theorem raw_shl (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl

theorem raw_shr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl

theorem eq_of_testBit_lt {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : ∀ k < n, a.testBit k = b.testBit k) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · exact h k hk
  · have hle : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hk)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)]

theorem testBit_ge6 {c : ℕ} (hc : c < 64) {j : ℕ} (hj : 6 ≤ j) : c.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj))

theorem testBit_63 (k : ℕ) : (63 : ℕ).testBit k = decide (k < 6) := by
  have := Nat.testBit_two_pow_sub_one 6 k
  simpa using this

theorem xor_lt64 {a b : ℕ} (ha : a < 64) (hb : b < 64) : a ^^^ b < 64 :=
  Nat.xor_lt_two_pow (n := 6) ha hb

theorem bitK_eq (v k : ℕ) : bitK v k = if v.testBit k then 1 else 0 := by
  unfold bitK
  show (v >>> k) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ k) with h | h <;> simp [h]

theorem lookT_tab3 {c₀ c₁ c₂ : ℕ} (h₀ : c₀ < 64) (h₁ : c₁ < 64) (h₂ : c₂ < 64) {v : ℕ}
    (hv : v < 8) :
    lookT (tab3 c₀ c₁ c₂) v = Code.sel v 0 c₀ ^^^ Code.sel v 1 c₁ ^^^ Code.sel v 2 c₂ := by
  apply eq_of_testBit_lt (n := 6)
  · exact Nat.and_lt_two_pow _ (by norm_num)
  · exact xor_lt64 (xor_lt64 (Code.sel_lt _ _ _ h₀) (Code.sel_lt _ _ _ h₁))
      (Code.sel_lt _ _ _ h₂)
  · intro k hk
    unfold lookT tab3
    rw [letN_eq]
    interval_cases v <;> interval_cases k <;>
    simp (config := {decide := true}) [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or,
      Nat.testBit_shiftLeft, testBit_ge6 h₀, testBit_ge6 h₁, testBit_ge6 h₂, testBit_63,
      Code.sel]

theorem packK_eq {c₀ c₁ c₂ c₃ c₄ c₅ : ℕ} (h₀ : c₀ < 64) (h₁ : c₁ < 64) (h₂ : c₂ < 64)
    (h₃ : c₃ < 64) (h₄ : c₄ < 64) (h₅ : c₅ < 64) :
    packK c₀ c₁ c₂ c₃ c₄ c₅ = Code.pack c₀ c₁ c₂ c₃ c₄ c₅ := by
  apply eq_of_testBit_lt (n := 36)
  · apply Nat.lt_pow_two_of_testBit
    intro i hi
    unfold packK
    simp (disch := omega) [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_ge6 h₀,
      testBit_ge6 h₁, testBit_ge6 h₂, testBit_ge6 h₃, testBit_ge6 h₄, testBit_ge6 h₅]
  · exact Code.pack_lt h₀ h₁ h₂ h₃ h₄ h₅
  · intro k hk
    unfold packK
    interval_cases k <;>
    simp (config := {decide := true}) [Code.pack, Code.testBit_pack_step h₀,
      Code.testBit_pack_step h₁, Code.testBit_pack_step h₂, Code.testBit_pack_step h₃,
      Code.testBit_pack_step h₄, Nat.testBit_or,
      Nat.testBit_shiftLeft, testBit_ge6 h₀, testBit_ge6 h₁, testBit_ge6 h₂, testBit_ge6 h₃,
      testBit_ge6 h₄]

theorem sel_and7 {v j : ℕ} (hj : j < 3) (c : ℕ) :
    Code.sel (v &&& 7) j c = Code.sel v j c := by
  interval_cases j <;> simp (config := {decide := true}) [Code.sel, Nat.testBit_and]

theorem sel_shr3 (v j c : ℕ) : Code.sel (v >>> 3) j c = Code.sel v (3 + j) c := by
  simp [Code.sel, Nat.testBit_shiftRight]

theorem actT_eq {c₀ c₁ c₂ c₃ c₄ c₅ : ℕ} (h₀ : c₀ < 64) (h₁ : c₁ < 64) (h₂ : c₂ < 64)
    (h₃ : c₃ < 64) (h₄ : c₄ < 64) (h₅ : c₅ < 64) {v : ℕ} (hv : v < 64) :
    actT (tab3 c₀ c₁ c₂) (tab3 c₃ c₄ c₅) v = Code.actCols c₀ c₁ c₂ c₃ c₄ c₅ v := by
  unfold actT
  have h1 : v &&& 7 < 8 := Nat.and_lt_two_pow (n := 3) _ (by norm_num)
  have h2 : v >>> 3 < 8 := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  rw [raw_xor, raw_land, raw_shr, lookT_tab3 h₀ h₁ h₂ h1, lookT_tab3 h₃ h₄ h₅ h2]
  simp only [Code.actCols, sel_and7 (by norm_num : 0 < 3), sel_and7 (by norm_num : 1 < 3),
    sel_and7 (by norm_num : 2 < 3), sel_shr3, Nat.xor_assoc]

theorem colK_lt (m j : ℕ) : colK m j < 64 := Nat.and_lt_two_pow (n := 6) _ (by norm_num)

theorem actCols_lt {c₀ c₁ c₂ c₃ c₄ c₅ : ℕ} (h₀ : c₀ < 64) (h₁ : c₁ < 64) (h₂ : c₂ < 64)
    (h₃ : c₃ < 64) (h₄ : c₄ < 64) (h₅ : c₅ < 64) (v : ℕ) :
    Code.actCols c₀ c₁ c₂ c₃ c₄ c₅ v < 64 :=
  xor_lt64 (xor_lt64 (xor_lt64 (xor_lt64 (xor_lt64 (Code.sel_lt _ _ _ h₀) (Code.sel_lt _ _ _ h₁))
    (Code.sel_lt _ _ _ h₂)) (Code.sel_lt _ _ _ h₃)) (Code.sel_lt _ _ _ h₄))
    (Code.sel_lt _ _ _ h₅)

theorem mulK_eq (a b : ℕ) : mulK a b = Code.mul a b := by
  have ha : ∀ j, colK a j < 64 := fun j => colK_lt a j
  have hb : ∀ j, colK b j < 64 := fun j => colK_lt b j
  unfold mulK Code.mul
  simp only [letN_eq]
  have key : ∀ j, actT (tab3 (colK a 0) (colK a 1) (colK a 2))
      (tab3 (colK a 3) (colK a 4) (colK a 5)) (colK b j) =
      Code.actCols (Code.col a 0) (Code.col a 1) (Code.col a 2) (Code.col a 3) (Code.col a 4)
        (Code.col a 5) (Code.col b j) := fun j =>
    actT_eq (ha 0) (ha 1) (ha 2) (ha 3) (ha 4) (ha 5) (hb j)
  have hl : ∀ j, Code.actCols (Code.col a 0) (Code.col a 1) (Code.col a 2) (Code.col a 3)
      (Code.col a 4) (Code.col a 5) (Code.col b j) < 64 := fun j =>
    actCols_lt (ha 0) (ha 1) (ha 2) (ha 3) (ha 4) (ha 5) _
  rw [key 0, key 1, key 2, key 3, key 4, key 5, packK_eq (hl 0) (hl 1) (hl 2) (hl 3) (hl 4) (hl 5)]

theorem oneK_eq : oneK = Code.one := by decide

theorem reflColK_eq (n j : ℕ) : reflColK n j = reflCol n j := by
  unfold reflColK reflCol
  rw [raw_xor, raw_land, bitK_eq, raw_shl, Nat.one_shiftLeft]
  by_cases h : n.testBit (j ^^^ 1) <;> simp [h]

theorem reflCK_eq (n : ℕ) : reflCK n = reflC n := by
  unfold reflCK reflC
  simp only [reflColK_eq]
  exact packK_eq (reflCol_lt n (by norm_num)) (reflCol_lt n (by norm_num))
    (reflCol_lt n (by norm_num)) (reflCol_lt n (by norm_num)) (reflCol_lt n (by norm_num))
    (reflCol_lt n (by norm_num))

theorem wordCK_eq (w : List ℕ) : wordCK w = wordC w := by
  induction w with
  | nil => exact oneK_eq
  | cons n t ih =>
    have e : wordCK (n :: t) = mulK (reflCK n) (wordCK t) := rfl
    rw [e, wordC_cons, mulK_eq, reflCK_eq, ih]

theorem revN_aux (w acc : List ℕ) :
    List.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
      (fun x _ ih acc => ih (List.cons x acc)) w acc = w.reverse ++ acc := by
  induction w generalizing acc with
  | nil => rfl
  | cons x t ih =>
    have e : List.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
      (fun x _ ih acc => ih (List.cons x acc)) (x :: t) acc =
        List.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
      (fun x _ ih acc => ih (List.cons x acc)) t (x :: acc) := rfl
    rw [e, ih]; simp

theorem revN_eq (w : List ℕ) : revN w = w.reverse := by
  unfold revN
  rw [revN_aux]; simp

theorem qBK_eq (minus : Bool) (n : ℕ) : qBK (if minus then 1 else 0) n = qB minus n := by
  unfold qBK qB
  simp only [bitK_eq]
  cases minus <;> cases n.testBit 0 <;> cases n.testBit 1 <;> cases n.testBit 2 <;>
    cases n.testBit 3 <;> cases n.testBit 4 <;> cases n.testBit 5 <;> decide

theorem isInvK_eq (x : ℕ) : isInvK x = Check.isInv x := by
  unfold isInvK Check.isInv
  rw [andB_eq, notB_eq, mulK_eq, oneK_eq, beq_eq_decide, beq_eq_decide]
  rfl

theorem commK_eq (x y : ℕ) : commK x y = Check.comm x y := by
  unfold commK Check.comm
  rw [mulK_eq, mulK_eq, beq_eq_decide]
  rfl

theorem cmul_assoc (a b c : ℕ) :
    Code.mul (Code.mul a b) c = Code.mul a (Code.mul b c) :=
  Code.eq_of_mat_eq (Code.mul_lt _ _) (Code.mul_lt _ _)
    (by simp only [Code.mat_mul, Matrix.mul_assoc])

theorem cmul_one {a : ℕ} (ha : a < 2 ^ 36) : Code.mul a Code.one = a :=
  Code.eq_of_mat_eq (Code.mul_lt _ _) ha
    (by rw [Code.mat_mul, Code.mat_one, Matrix.mul_one])

theorem one_cmul {a : ℕ} (ha : a < 2 ^ 36) : Code.mul Code.one a = a :=
  Code.eq_of_mat_eq (Code.mul_lt _ _) ha
    (by rw [Code.mat_mul, Code.mat_one, Matrix.one_mul])

end CFSG.KC.Misc.O62

end
