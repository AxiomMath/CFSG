module

public import Certificates.Data.Kernel.M12Dec
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsTransversalCheckInputs
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.M12Dec

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.ComponentClassification.M12Cover.InternalSylow

theorem b64_eq (c : Char) : b64 c = b64K c.toNat := by
  unfold b64 b64K
  generalize c.toNat = n
  have bf : ∀ {a b : Nat}, a ≠ b → Nat.beq a b = false :=
    fun h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
  have lf : ∀ {a b : Nat}, ¬ a ≤ b → Nat.ble a b = false :=
    fun h => Bool.eq_false_iff.2 fun h' => h (Nat.le_of_ble_eq_true h')
  by_cases h1 : n = 43
  · subst h1
    rfl
  rw [ite_eq_right h1, bf h1]
  by_cases h2 : n = 47
  · subst h2
    rfl
  rw [ite_eq_right h2, bf h2]
  by_cases h3 : n ≤ 57
  · rw [ite_eq_left h3, Nat.ble_eq_true_of_le h3]
    rfl
  rw [ite_eq_right h3, lf h3]
  by_cases h4 : n ≤ 90
  · rw [ite_eq_left h4, Nat.ble_eq_true_of_le h4]
    rfl
  rw [ite_eq_right h4, lf h4]
  rfl

theorem pg_sub {w r P a b c : Nat} (hc : r * a + w * b = w * c) (hlt : w * b + w ≤ r) :
    pg w (mask w) (pg r (mask r) P a) b = pg w (mask w) P c := by
  have m : ∀ x : Nat, mask x = 2 ^ x - 1 := fun x => by
    change (1 <<< x) - 1 = 2 ^ x - 1
    rw [Nat.one_shiftLeft]
  unfold pg
  rw [m, m]
  change ((P >>> (r * a) &&& (2 ^ r - 1)) >>> (w * b) &&& (2 ^ w - 1)) =
    (P >>> (w * c) &&& (2 ^ w - 1))
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < w
  · have h1 : w * b + j < r := by omega
    have h2 : r * a + (w * b + j) = w * c + j := by omega
    simp [hj, h1, h2]
  · simp [hj]

theorem strB_eq (y : Nat) (k : Nat → Bool) : strB y k = k y := by
  cases y <;> rfl

theorem rows_eq (w P idx : Nat) :
    pg w (mask w) (pg (Nat.mul 64 w) (mask (Nat.mul 64 w)) P (Nat.div idx 64)) (Nat.mod idx 64) =
      pg w (mask w) P idx := by
  have hm : idx % 64 + 1 ≤ 64 := Nat.mod_lt idx (by decide)
  refine pg_sub ?_ ?_
  · change 64 * w * (idx / 64) + w * (idx % 64) = w * idx
    rw [Nat.mul_comm 64 w, Nat.mul_assoc, ← Nat.mul_add, Nat.div_add_mod]
  · change w * (idx % 64) + w ≤ 64 * w
    calc w * (idx % 64) + w = w * (idx % 64 + 1) := (Nat.mul_succ w _).symm
      _ ≤ w * 64 := Nat.mul_le_mul_left w hm
      _ = 64 * w := Nat.mul_comm w 64

theorem decK_cons (k w : Nat) (R : Nat → Nat) (N : Nat) (c : Char) (cs : List Char)
    (cnt cur idx : Nat) :
    decK k w R N (c :: cs) cnt cur idx =
      bIf(Nat.beq (Nat.succ cnt) k,
        bAnd(strB (Nat.div idx 64) (fun q => Nat.beq (pg w (mask w) (R q) (Nat.mod idx 64))
            (Nat.add (Nat.mul cur 64) (b64K c.toNat))),
          strB (Nat.succ idx) (decK k w R N cs 0 0)),
        decK k w R N cs (Nat.succ cnt) (Nat.add (Nat.mul cur 64) (b64K c.toNat)) idx) := rfl

theorem decK_spec {k w P N : Nat} {R : Nat → Nat}
    (hR : ∀ idx, pg w (mask w) (R (Nat.div idx 64)) (Nat.mod idx 64) = pg w (mask w) P idx) :
    ∀ (cs : List Char) (cnt cur : Nat) (acc : Array Nat),
    (∀ j (hj : j < acc.size), acc[j] = pg w (mask w) P j) →
    decK k w R N cs cnt cur acc.size = true → decodeAux k cs cnt cur acc = unpack N w P
  | [], cnt, cur, acc, he, h => by
    have hN : acc.size = N := Nat.eq_of_beq_eq_true h
    rw [decodeAux]
    apply Array.ext
    · rw [hN]
      unfold unpack
      rw [Array.size_ofFn]
    · intro j h1 _
      rw [he j h1]
      simp only [unpack, Array.getElem_ofFn]
  | c :: cs, cnt, cur, acc, he, h => by
    rw [decK_cons] at h
    rw [decodeAux]
    by_cases hk : cnt + 1 = k
    · have hb : Nat.beq (Nat.succ cnt) k = true := by
        subst hk
        exact Nat.beq_refl _
      rw [hb] at h
      obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
      rw [strB_eq, hR] at h1
      rw [strB_eq] at h2
      rw [ite_eq_left hk]
      refine decK_spec hR cs 0 0 _ (fun j hj => ?_) (by rw [Array.size_push]; exact h2)
      rw [Array.getElem_push]
      by_cases hj' : j < acc.size
      · simp only [hj', ↓reduceDIte]
        exact he j hj'
      · simp only [hj', ↓reduceDIte]
        have e : j = acc.size := by
          rw [Array.size_push] at hj
          omega
        rw [e, Nat.eq_of_beq_eq_true h1, b64_eq]
        rfl
    · have hb : Nat.beq (Nat.succ cnt) k = false :=
        Bool.eq_false_iff.2 fun h' => hk (Nat.eq_of_beq_eq_true h')
      rw [hb] at h
      rw [ite_eq_right hk, b64_eq]
      exact decK_spec hR cs (cnt + 1) _ acc he h

theorem unpack_get {n w P i : Nat} (hP0 : Nat.beq (Nat.shiftRight P (n * w)) 0 = true) :
    (unpack n w P)[i]! = pg w (mask w) P i := by
  have hP : P < 2 ^ (n * w) := Nat.lt_of_div_eq_zero (Nat.two_pow_pos _)
    (by rw [← Nat.shiftRight_eq_div_pow]; exact Nat.eq_of_beq_eq_true hP0)
  by_cases h : i < n
  · unfold unpack
    rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact h), Array.getElem_ofFn]
  · rw [getElem!_neg _ i (by unfold unpack; rw [Array.size_ofFn]; exact h)]
    have hw : n * w ≤ w * i := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left w (by omega)
    have e : Nat.shiftRight P (Nat.mul w i) = 0 := by
      have e1 : Nat.shiftRight P (Nat.mul w i) = P >>> (w * i) := rfl
      rw [e1, Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by decide) hw))
    unfold pg
    rw [e]
    exact (Nat.zero_and _).symm

theorem decodeB64_sound {k w P N : Nat} {cs : List Char}
    (h : decK k w (rowsOf w P) N cs 0 0 0 = true) :
    decodeB64 k (String.ofList cs) = unpack N w P := by
  unfold decodeB64
  rw [String.toList_ofList]
  exact decK_spec (rows_eq w P) cs 0 0 #[] (fun j hj => absurd hj (Nat.not_lt_zero _)) h

end CFSG.KC.M12Dec

end
