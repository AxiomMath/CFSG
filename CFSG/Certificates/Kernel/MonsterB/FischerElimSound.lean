module

public import Certificates.Data.Kernel.MonsterB.FischerElim
public import CFSG.Monster.B.TwoA.Fischer.CertBin

public section

namespace CFSG.KC.FischerE

open CFSG.Monster.B.Binary.Native CFSG.Monster.B.TwoA.Fischer.Cert

def InvL : List Nat → Prop
  | [] => True
  | t :: ts => (t = 0 ∨ (2 ^ ts.length ≤ t ∧ t < 2 ^ (ts.length + 1))) ∧ InvL ts

theorem bit_probe (v n : Nat) : Nat.blt 0 (Nat.land v (Nat.shiftLeft 1 n)) = v.testBit n := by
  have h1 : Nat.land v (Nat.shiftLeft 1 n) = v &&& 2 ^ n := by
    change v &&& (1 <<< n) = _
    rw [Nat.one_shiftLeft]
  rw [h1, Nat.and_two_pow]
  cases v.testBit n
  · rw [Bool.toNat_false, Nat.zero_mul]
    rfl
  · rw [Bool.toNat_true, Nat.one_mul]
    rw [Nat.blt_eq]
    exact Nat.two_pow_pos n

theorem beq_zero_false {t : Nat} (h : t ≠ 0) : Nat.beq t 0 = false := by
  rw [Bool.eq_false_iff]
  intro e
  exact h (Nat.eq_of_beq_eq_true e)

theorem insL_cons (t : Nat) (ts : List Nat) (p v : Nat) : insL (t :: ts) p v =
    if v.testBit p then (if t = 0 then v :: ts else t :: insL ts (p - 1) (v ^^^ t))
    else t :: insL ts (p - 1) v := by
  change Bool.rec (motive := fun _ => List Nat) (List.cons t (insL ts (Nat.sub p 1) v))
    (Bool.rec (motive := fun _ => List Nat) (List.cons t (insL ts (Nat.sub p 1) (Nat.xor v t)))
      (List.cons v ts) (Nat.beq t 0)) (Nat.blt 0 (Nat.land v (Nat.shiftLeft 1 p))) = _
  rw [bit_probe]
  cases v.testBit p
  · rfl
  · by_cases ht : t = 0
    · subst ht
      rfl
    · rw [beq_zero_false ht, if_neg ht]
      rfl

theorem length_insL : ∀ (R : List Nat) (p v : Nat), (insL R p v).length = R.length
  | [], _, _ => rfl
  | t :: ts, p, v => by
    rw [insL_cons]
    split_ifs <;> simp [length_insL]

theorem lt_of_testBit_false {v n : Nat} (hv : v < 2 ^ (n + 1)) (hb : v.testBit n = false) :
    v < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rcases Nat.eq_or_lt_of_le hi with h | h
  · rw [← h]
    exact hb
  · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) h))

theorem xor_lt_of_testBit {v t n : Nat} (hv : v < 2 ^ (n + 1)) (ht : t < 2 ^ (n + 1))
    (hbv : v.testBit n = true) (hbt : t.testBit n = true) : v ^^^ t < 2 ^ n := by
  apply lt_of_testBit_false (Nat.xor_lt_two_pow hv ht)
  rw [Nat.testBit_xor, hbv, hbt]
  rfl

theorem testBit_of_bounds {t n : Nat} (h1 : 2 ^ n ≤ t) (h2 : t < 2 ^ (n + 1)) :
    t.testBit n = true := by
  by_contra h
  have := lt_of_testBit_false h2 (by simpa using h)
  omega

theorem log2_of_bounds {v n : Nat} (h1 : 2 ^ n ≤ v) (h2 : v < 2 ^ (n + 1)) : Nat.log2 v = n := by
  have hv : v ≠ 0 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  rw [Nat.log2_eq_iff hv]
  exact ⟨h1, h2⟩

theorem ge_of_testBit {v n : Nat} (h : v.testBit n = true) : 2 ^ n ≤ v :=
  Nat.ge_two_pow_of_testBit h

theorem invL_insL : ∀ (R : List Nat) (v : Nat), InvL R → v < 2 ^ R.length →
    InvL (insL R (R.length - 1) v)
  | [], _, _, _ => trivial
  | t :: ts, v, ⟨ht, hts⟩, hv => by
    have hp : (t :: ts).length - 1 = ts.length := by simp
    rw [hp, insL_cons]
    have hv' : v < 2 ^ (ts.length + 1) := by simpa using hv
    by_cases hb : v.testBit ts.length
    · rw [if_pos hb]
      by_cases ht0 : t = 0
      · rw [if_pos ht0]
        exact ⟨Or.inr ⟨ge_of_testBit hb, hv'⟩, hts⟩
      · rw [if_neg ht0]
        have htb := ht.resolve_left ht0
        refine ⟨by rw [length_insL]; exact ht, ?_⟩
        have hx := xor_lt_of_testBit hv' htb.2 hb (testBit_of_bounds htb.1 htb.2)
        exact invL_insL ts _ hts hx
    · rw [if_neg hb]
      refine ⟨by rw [length_insL]; exact ht, ?_⟩
      exact invL_insL ts v hts (lt_of_testBit_false hv' (by simpa using hb))

theorem getD_mid (A S : List Nat) (t : Nat) :
    (A ++ t :: S).toArray[A.length]?.getD 0 = t := by
  simp

theorem set_mid (A S : List Nat) (t v : Nat) :
    (A ++ t :: S).toArray.set! A.length v = (A ++ v :: S).toArray := by
  rw [Array.set!_eq_setIfInBounds, List.setIfInBounds_toArray, List.set_append_right _ _ (by simp)]
  simp

theorem insertVec_eq : ∀ (R S : List Nat) (v fuel : Nat), InvL R → v < 2 ^ R.length →
    R.length + 1 ≤ fuel →
    insertVec (R.reverse ++ S).toArray fuel v = some ((insL R (R.length - 1) v).reverse ++ S).toArray
  | [], S, v, fuel, _, hv, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hv0 : v = 0 := by simpa using hv
    subst hv0
    simp [insertVec, insL]
  | t :: ts, S, v, fuel, ⟨ht, hts⟩, hv, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hp : (t :: ts).length - 1 = ts.length := by simp
    have hv' : v < 2 ^ (ts.length + 1) := by simpa using hv
    have hf' : ts.length + 1 ≤ f := by simp at hf; omega
    rw [hp, insL_cons]
    have e1 : (t :: ts).reverse ++ S = ts.reverse ++ t :: S := by simp
    by_cases hb : v.testBit ts.length
    · rw [if_pos hb]
      have hge := ge_of_testBit hb
      have hlog := log2_of_bounds hge hv'
      have hv0 : v ≠ 0 := by
        have := Nat.one_le_two_pow (n := ts.length)
        omega
      have hlen : ts.reverse.length = ts.length := List.length_reverse
      rw [e1, insertVec, if_neg hv0]
      simp only [hlog]
      rw [← hlen, getD_mid]
      by_cases ht0 : t = 0
      · rw [if_pos ht0, if_pos ht0, set_mid]
        simp
      · rw [if_neg ht0, if_neg ht0]
        have htb := ht.resolve_left ht0
        have hx := xor_lt_of_testBit hv' htb.2 hb (testBit_of_bounds htb.1 htb.2)
        have ih := insertVec_eq ts (t :: S) (v ^^^ t) f hts hx hf'
        rw [hlen, ih]
        simp
    · rw [if_neg hb, e1]
      have hlt := lt_of_testBit_false hv' (by simpa using hb)
      have ih := insertVec_eq ts (t :: S) v (f + 1) hts hlt (by omega)
      rw [ih]
      simp

theorem length_elimL (p : Nat) : ∀ (vs R : List Nat), (elimL p vs R).length = R.length
  | [], _ => rfl
  | v :: vs, R => by
    change (elimL p vs (insL R p v)).length = _
    rw [length_elimL p vs, length_insL]

theorem elimList_eq {d : Nat} : ∀ (vs R : List Nat), R.length = d → InvL R →
    (∀ v ∈ vs, v < 2 ^ d) → elimList d R.reverse.toArray vs = some (elimL (d - 1) vs R).reverse.toArray
  | [], R, _, _, _ => rfl
  | v :: vs, R, hR, hI, hvs => by
    have hv : v < 2 ^ R.length := by rw [hR]; exact hvs v List.mem_cons_self
    have h1 := insertVec_eq R [] v (d + 1) hI hv (by omega)
    rw [List.append_nil, List.append_nil, hR] at h1
    rw [elimList, h1]
    change elimList d _ vs = some (elimL (d - 1) vs (insL R (d - 1) v)).reverse.toArray
    have hI' := invL_insL R v hI hv
    rw [hR] at hI'
    exact elimList_eq vs _ (by rw [length_insL, hR]) hI' fun w hw => hvs w (List.mem_cons_of_mem v hw)

theorem zerosL_eq : ∀ d, zerosL d = List.replicate d 0
  | 0 => rfl
  | d + 1 => by
    change 0 :: zerosL d = _
    rw [zerosL_eq d, List.replicate_succ]

theorem invL_zeros : ∀ d, InvL (List.replicate d 0)
  | 0 => trivial
  | d + 1 => ⟨Or.inl rfl, invL_zeros d⟩

theorem elimTable_eq {d : Nat} {vs : List Nat} (h : ∀ v ∈ vs, v < 2 ^ d) :
    elimTable d vs = some (elimL (d - 1) vs (zerosL d)).reverse.toArray := by
  have e : Array.replicate d 0 = (zerosL d).reverse.toArray := by
    rw [zerosL_eq, List.reverse_replicate]
    rfl
  rw [elimTable, e]
  exact elimList_eq vs _ (by rw [zerosL_eq, List.length_replicate]) (by rw [zerosL_eq]; exact invL_zeros d) h

theorem nzL_eq : ∀ R : List Nat, nzL R = (R.map fun t => if t = 0 then 0 else 1).sum
  | [] => rfl
  | t :: ts => by
    change Bool.rec (motive := fun _ => Nat) (Nat.succ (nzL ts)) (nzL ts) (Nat.beq t 0) = _
    rw [List.map_cons, List.sum_cons, ← nzL_eq ts]
    by_cases ht : t = 0
    · subst ht
      simp
    · rw [beq_zero_false ht, if_neg ht]
      change nzL ts + 1 = 1 + nzL ts
      omega

theorem tableRank_eq (R : List Nat) {d : Nat} (hR : R.length = d) :
    tableRank d R.reverse.toArray = nzL R := by
  have e : (List.range d).map (fun p => if R.reverse.toArray[p]! = 0 then 0 else 1) =
      R.reverse.map (fun t => if t = 0 then 0 else 1) := by
    apply List.ext_getElem
    · simp [hR]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      have hi : i < R.reverse.length := by simpa using h2
      rw [List.getElem!_toArray, getElem!_pos R.reverse i hi]
  rw [tableRank, e, List.map_reverse, List.sum_reverse, nzL_eq]

theorem spanRankIs_eq (d : Nat) (vs : List Nat) (r : Nat) :
    spanRankIs d vs r = (allBelow d vs && Nat.beq (nzL (elimL (d - 1) vs (zerosL d))) r) := by
  rw [spanRankIs]
  cases hb : allBelow d vs
  · rfl
  · rw [elimTable_eq (allBelow_iff.1 hb)]
    simp only [rankOpt, Bool.true_and]
    have hl : (elimL (d - 1) vs (zerosL d)).length = d := by
      rw [length_elimL, zerosL_eq, List.length_replicate]
    rw [tableRank_eq _ hl]
    simp only [List.size_toArray, List.length_reverse, hl, beq_self_eq_true, Bool.true_and]
    apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, Nat.beq_eq]

theorem freeIs_eq (d : Nat) (vs Q : List Nat) :
    freeIs d vs Q = (allBelow d vs && (List.range d).all fun p =>
      ((elimL (d - 1) vs (zerosL d)).reverse.toArray[p]! == 0) == Q.contains p) := by
  rw [freeIs]
  cases hb : allBelow d vs
  · rfl
  · rw [elimTable_eq (allBelow_iff.1 hb)]

end CFSG.KC.FischerE

end
