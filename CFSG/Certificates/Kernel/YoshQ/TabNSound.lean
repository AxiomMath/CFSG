module

public import Certificates.Data.Kernel.YoshQ.TabN
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.TabWords
public import Certificates.Data.CFSGNative.SporadicSchreier.Classes

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.KS.PF

variable {n w : Nat}

theorem pg_mod {x i : Nat} (hi : i < n) :
    pg w (mask w) (x % 2 ^ (n * w)) i = pg w (mask w) x i := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_pgM, testBit_pgM, Nat.testBit_mod_two_pow]
  by_cases hk : k < w
  · have : w * i + k < n * w := by
      have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hi)
      rw [Nat.mul_succ] at this
      rw [Nat.mul_comm n w]
      omega
    simp [hk, this]
  · simp [hk]

theorem pg_mod_ge {x i : Nat} (hi : n ≤ i) : pg w (mask w) (x % 2 ^ (n * w)) i = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_pgM, Nat.testBit_mod_two_pow, Nat.zero_testBit]
  have : ¬ w * i + k < n * w := by
    have := Nat.mul_le_mul_left w hi
    rw [Nat.mul_comm n w]
    omega
  simp [this]

theorem mod_shr (x : Nat) : (x % 2 ^ (n * w)) >>> (n * w) = 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))

theorem pg_lt32 (hw : w ≤ 32) (x i : Nat) : pg w (mask w) x i < 2 ^ 32 :=
  Nat.lt_of_lt_of_le (pg_lt w x i) (Nat.pow_le_pow_right (by decide) hw)

theorem toNat_ofNat_pg (hw : w ≤ 32) (x i : Nat) :
    (UInt32.ofNat (pg w (mask w) x i)).toNat = pg w (mask w) x i :=
  UInt32.toNat_ofNat_of_lt' (pg_lt32 hw x i)

theorem size_tabN (x : Nat) : (tabN n w x).size = n := by simp [tabN]

theorem getElem!_tabN (x i : Nat) :
    (tabN n w x)[i]! = if i < n then UInt32.ofNat (pg w (mask w) (x % 2 ^ (n * w)) i) else 0 := by
  by_cases hi : i < n
  · rw [getElem!_pos _ i (by simpa [tabN] using hi)]
    simp [tabN, hi]
  · rw [getElem!_neg _ i (by simpa [tabN] using hi)]
    simp only [hi, ↓reduceIte]
    rfl

theorem ap_tabN (hw : w ≤ 32) (x i : Nat) : ap (tabN n w x) i = pg w (mask w) (x % 2 ^ (n * w)) i := by
  unfold ap
  rw [getElem!_tabN]
  by_cases hi : i < n
  · simp only [hi, ↓reduceIte]
    exact toNat_ofNat_pg hw _ _
  · simp only [hi, ↓reduceIte, pg_mod_ge (Nat.le_of_not_lt hi)]
    rfl

theorem tabN_ext {x y : Nat}
    (h : ∀ i < n, pg w (mask w) (x % 2 ^ (n * w)) i = pg w (mask w) (y % 2 ^ (n * w)) i) :
    tabN n w x = tabN n w y := by
  apply Array.ext (by simp [tabN])
  intro i h1 _
  have hi : i < n := by simpa [tabN] using h1
  simp [tabN, h i hi]

theorem compT_tabN (hw : w ≤ 32) (hn : n < 2 ^ 32) (x y : Nat) :
    compT n (tabN n w x) (tabN n w y) = tabN n w (pmN n w x y) := by
  apply Array.ext (by simp [compT, tabN])
  intro i h1 _
  have hi : i < n := by simpa [compT] using h1
  simp only [compT, Array.getElem_ofFn]
  have e1 : ((tabN n w y)[i]!).toNat = pg w (mask w) (y % 2 ^ (n * w)) i := by
    rw [getElem!_tabN]
    simp only [hi, ↓reduceIte]
    exact toNat_ofNat_pg hw _ _
  rw [e1, getElem!_tabN]
  simp only [tabN, Array.getElem_ofFn]
  have e2 : pg w (mask w) (pmN n w x y % 2 ^ (n * w)) i =
      pg w (mask w) (x % 2 ^ (n * w)) (pg w (mask w) (y % 2 ^ (n * w)) i) := by
    rw [pg_mod hi, pmN, pg_pcomp hn hi, pg_mod hi]
  rw [e2]
  split
  · rfl
  · rename_i hge
    rw [pg_mod_ge (Nat.le_of_not_lt hge)]
    rfl

theorem tabN_inj_iff (hw0 : 0 < w) (hw : w ≤ 32) {x y : Nat} :
    (∀ i < n, ap (tabN n w x) i = ap (tabN n w y) i) ↔ x % 2 ^ (n * w) = y % 2 ^ (n * w) := by
  constructor
  · intro h
    apply eq_of_fields hw0 (mod_shr x) (mod_shr y)
    intro i hi
    have := h i hi
    rwa [ap_tabN hw, ap_tabN hw] at this
  · intro h i _
    rw [ap_tabN hw, ap_tabN hw, h]

theorem tblEq_tabN (hw0 : 0 < w) (hw : w ≤ 32) (x y : Nat) :
    tblEq n (tabN n w x) (tabN n w y) = eqN n w x y := by
  apply Bool.eq_iff_iff.2
  unfold tblEq eqN
  rw [CFSG.KS.TW.allIn_iff]
  simp only [beq_iff_eq, Nat.beq_eq]
  exact tabN_inj_iff hw0 hw

theorem idT_tabN (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (hw32 : w ≤ 32) :
    idT n = tabN n w (pidn n w) := by
  apply Array.ext (by simp [idT, tabN])
  intro i h1 _
  have hi : i < n := by simpa [idT] using h1
  simp only [idT, tabN, Array.getElem_ofFn]
  rw [pg_mod hi, pg_pidn hn hw hi]

theorem testBit_ge {i b : Nat} (hi : i < 2 ^ w) (hb : w ≤ b) : i.testBit b = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) hb))

theorem testBit_setF {acc v i : Nat} (hi : i < 2 ^ w) (j : Nat) :
    (setF w acc v i).testBit j =
      if w * v ≤ j ∧ j < w * v + w then i.testBit (j - w * v) else acc.testBit j := by
  unfold setF
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_xor, testBit_pgM]
  by_cases h1 : w * v ≤ j
  · by_cases h2 : j < w * v + w
    · have e : w * v + (j - w * v) = j := by omega
      have h3 : j - w * v < w := by omega
      simp only [h1, h2, h3, e, and_self, ↓reduceIte, ge_iff_le, decide_true, Bool.true_and]
      rcases Bool.eq_false_or_eq_true (acc.testBit j) with h | h <;> simp [h]
    · have h3 : ¬ j - w * v < w := by omega
      simp [h1, h2, h3, testBit_ge hi (Nat.le_of_not_lt h3)]
  · simp [h1]

theorem pg_setF {acc v i : Nat} (hi : i < 2 ^ w) (k : Nat) :
    pg w (mask w) (setF w acc v i) k = if k = v then i else pg w (mask w) acc k := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_pgM, testBit_setF hi]
  by_cases hk : k = v
  · rw [if_pos hk, ← hk]
    by_cases hb : b < w
    · have h1 : w * k ≤ w * k + b ∧ w * k + b < w * k + w := ⟨by omega, by omega⟩
      simp [hb, h1]
    · simp only [hb, decide_false, Bool.false_and]
      exact (testBit_ge hi (Nat.le_of_not_lt hb)).symm
  · rw [if_neg hk, testBit_pgM]
    by_cases hb : b < w
    · have h1 : ¬ (w * v ≤ w * k + b ∧ w * k + b < w * v + w) := by
        rintro ⟨h1, h2⟩
        rcases Nat.lt_or_gt_of_ne hk with h | h
        · have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt h)
          rw [Nat.mul_succ] at this
          omega
        · have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt h)
          rw [Nat.mul_succ] at this
          omega
      simp [hb, h1]
    · simp [hb]

theorem replicate_tabN : Array.replicate n (0 : UInt32) = tabN n w 0 := by
  apply Array.ext (by simp [tabN])
  intro i h1 _
  have e : pg w (mask w) 0 i = 0 := by simp [pg]
  simp [tabN, e]

theorem set!_tabN (hw : w ≤ 32) {acc v i : Nat} (hv : v < n) (hi : i < 2 ^ w) :
    (tabN n w acc).set! v (UInt32.ofNat i) = tabN n w (setF w acc v i) := by
  rw [Array.set!_eq_setIfInBounds]
  apply Array.ext (by simp [tabN])
  intro k h1 _
  have hk : k < n := by simpa [tabN] using h1
  rw [Array.getElem_setIfInBounds (by simpa [tabN] using hk)]
  simp only [tabN, Array.getElem_ofFn]
  rw [pg_mod hk, pg_mod hk, pg_setF hi]
  by_cases e : v = k
  · rw [if_pos e, if_pos e.symm]
  · rw [if_neg e, if_neg (Ne.symm e)]

theorem foldl_inv (hw : w ≤ 32) (hnw : n ≤ 2 ^ w) (x : Nat) :
    ∀ l : List Nat, (∀ i ∈ l, i < n) → ∀ acc : Nat,
      l.foldl (fun r i => r.set! ((tabN n w x)[i]!).toNat (UInt32.ofNat i)) (tabN n w acc) =
        tabN n w (l.foldl (fun acc i =>
          if pg w (mask w) (x % 2 ^ (n * w)) i < n then
            setF w acc (pg w (mask w) (x % 2 ^ (n * w)) i) i
          else acc) acc)
  | [], _, _ => rfl
  | i :: l, hl, acc => by
    have hi : i < n := hl i List.mem_cons_self
    simp only [List.foldl_cons]
    have e1 : ((tabN n w x)[i]!).toNat = pg w (mask w) (x % 2 ^ (n * w)) i := by
      rw [getElem!_tabN]
      simp only [hi, ↓reduceIte]
      exact toNat_ofNat_pg hw _ _
    rw [e1]
    by_cases hv : pg w (mask w) (x % 2 ^ (n * w)) i < n
    · rw [if_pos hv, set!_tabN hw hv (by omega)]
      exact foldl_inv hw hnw x l (fun j hj => hl j (List.mem_cons_of_mem i hj)) _
    · rw [if_neg hv, Array.set!_eq_setIfInBounds,
        Array.setIfInBounds_eq_of_size_le (by rw [size_tabN]; omega)]
      exact foldl_inv hw hnw x l (fun j hj => hl j (List.mem_cons_of_mem i hj)) _

theorem invT_tabN (hw : w ≤ 32) (hnw : n ≤ 2 ^ w) (x : Nat) :
    invT n (tabN n w x) = tabN n w (invN n w x) := by
  unfold invT invN
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, pure_bind, List.forIn_pure_yield_eq_foldl]
  rw [← List.range_eq_range', replicate_tabN (w := w)]
  exact foldl_inv hw hnw x _ (fun i hi => List.mem_range.1 hi) 0

end CFSG.KC.YoshQ

end
