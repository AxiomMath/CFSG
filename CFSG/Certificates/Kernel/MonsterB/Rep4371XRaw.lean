module

public import CFSG.Certificates.Kernel.MonsterB.Rep4371XKeys

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Trace6091 CFSG.KC.Rep4371Row CFSG.Monster.B

theorem lIf_true (t e : Terms) : lIf true t e = t := rfl

theorem lIf_false (t e : Terms) : lIf false t e = e := rfl

theorem nbeq_bool (a b : Bool) : Nat.beq a.toNat b.toNat = (a == b) := by
  cases a <;> cases b <;> rfl

theorem nbeq (x y : Nat) : Nat.beq x y = (x == y) := by
  cases h : Nat.beq x y
  · have hne : x ≠ y := fun e => by
      rw [e, Nat.beq_refl] at h
      exact Bool.noConfusion h
    exact (beq_eq_false_iff_ne.mpr hne).symm
  · exact (beq_iff_eq.mpr (Nat.eq_of_beq_eq_true h)).symm

theorem and3 (x : Nat) : x &&& 3 = x % 4 := Nat.and_two_pow_sub_one_eq_mod x 2

theorem oddT_lt (i : Nat) : oddT i < 4096 := KeysOKAux.f12_lt _ _

theorem ble_true {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := Nat.ble_eq_true_of_le h

theorem ble_false {a b : Nat} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  rw [Bool.eq_false_iff]
  intro h'
  exact h (Nat.le_of_ble_eq_true h')

theorem pairwise_inj {l : List Nat} {f : Nat → Nat} (h : l.Pairwise (fun a b => f a < f b)) :
    ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b := by
  induction l with
  | nil => intro a ha
           exact absurd ha List.not_mem_nil
  | cons x l ih =>
    rw [List.pairwise_cons] at h
    intro a ha b hb hab
    rw [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd hab (Nat.ne_of_lt (h.1 b hb))
    · exact absurd hab (Nat.ne_of_gt (h.1 a ha))
    · exact ih h.2 a ha b hb hab

theorem oddP_eq (a : Nat) : oddP a = ((Model.wordN a).testBit 0 == (Model.wordN a).testBit 1) := by
  unfold oddP
  rw [bitN_eq, bitN_eq, nbeq_bool, wordT_eq]

theorem oddCodes_eq : Model.oddCodes = ((List.range 1024).map oddT).toArray := by
  unfold Model.oddCodes Model.oddCodesOf
  rw [← odd_filter]
  exact congrArg List.toArray (List.filter_congr fun a _ => (oddP_eq a).symm)

theorem oddCodes_get {i : Nat} (hi : i < 1024) : Model.oddCodes[i]! = oddT i := by
  rw [oddCodes_eq, getElem!_pos _ _ (by simpa using hi)]
  simp

theorem octP_eq (a : Nat) :
    octP a = (Model.popcN 24 (Model.wordN a) == 8 && Model.wordN a % 4 == 3) := by
  unfold octP
  rw [nbeq, nbeq, KeysOKAux.popc24_eq, Rep4371.native_popcN, wordT_eq, Nat.land_eq, and3]

theorem octT_mem {b : Nat} (hb : b < 77) : octT b ∈ (List.range 4096).filter octP :=
  oct_perm.symm.subset (List.mem_map_of_mem (List.mem_range.mpr hb))

theorem octT_word {b : Nat} (hb : b < 77) :
    Rep4371.Native.popcN 24 (Model.wordN (octT b)) = 8 ∧ Model.wordN (octT b) % 4 = 3 := by
  have h := (List.mem_filter.mp (octT_mem hb)).2
  rw [octP_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  rw [Rep4371.native_popcN]
  exact h

theorem octCoeffs_eq : Model.octCoeffs = ((List.range 77).map octT).toArray := by
  unfold Model.octCoeffs Model.octCoeffsOf
  have hF : ((List.range 4096).filter fun a => Model.popcN 24 (Model.wordN a) == 8 &&
      Model.wordN a % 4 == 3) = (List.range 4096).filter octP := by
    apply List.filter_congr
    intro a _
    rw [octP_eq]
  rw [hF]
  refine congrArg List.toArray ?_
  have hw : ∀ a, Model.wordN a = wordT a := fun a => (wordT_eq a).symm
  apply List.Perm.eq_of_pairwise (le := fun a b => decide (Model.wordN a ≤ Model.wordN b) = true)
  · intro a b ha hb hab hba
    have ha' : a ∈ (List.range 77).map octT :=
      oct_perm.subset ((List.mergeSort_perm _ _).subset ha)
    have he : wordT a = wordT b := by
      rw [← hw, ← hw]
      exact Nat.le_antisymm (of_decide_eq_true hab) (of_decide_eq_true hba)
    exact pairwise_inj oct_sorted a ha' b hb he
  · exact List.pairwise_mergeSort (le := fun a b => decide (Model.wordN a ≤ Model.wordN b))
      (fun a b c hab hbc => decide_eq_true
      (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
      (fun a b => by
        rcases Nat.le_total (Model.wordN a) (Model.wordN b) with h | h <;> simp [h]) _
  · refine oct_sorted.imp ?_
    intro a b h
    rw [hw, hw]
    exact decide_eq_true (Nat.le_of_lt h)
  · exact (List.mergeSort_perm _ _).trans oct_perm

theorem octCoeffs_get {b : Nat} (hb : b < 77) : Model.octCoeffs[b]! = octT b := by
  rw [octCoeffs_eq, getElem!_pos _ _ (by simpa using hb)]
  simp

theorem oddKT_eq {TH : Nat} (hTH : thOK TH = true) {c : Nat} (hc : c < 4096) (i : Nat) :
    kd (oddKT TH c i) = Model.oddKey c i := by
  unfold oddKT
  simp only [strictN_eq, thH_eq hTH]
  rw [KeysOKAux.oddCodeT_eq, Rep4371.native_oddCode, thetaT_eq, dualT_eq, Nat.shiftLeft_eq',
    Nat.one_shiftLeft]
  have hb : Model.oddCode c i < 4096 := by
    unfold Model.oddCode
    have h12 : (4096 : Nat) = 2 ^ 12 := rfl
    rw [h12] at hc ⊢
    refine Nat.xor_lt_two_pow hc ?_
    split <;> decide
  rw [kd_kc (by decide) hb]
  rfl

theorem suppList_eq {w : Nat} (h0 : w.testBit 0 = true) (h1 : w.testBit 1 = true) :
    Model.localOrder w = CFSG.Monster.AxisCount.Native.suppList w := by
  unfold Model.localOrder CFSG.Monster.AxisCount.Native.suppList
  have e : List.range' 0 24 = 0 :: 1 :: List.range' 2 22 := rfl
  rw [List.range_eq_range', e]
  have hc : ∀ i ∈ List.range' 2 22, (decide (2 ≤ i) && w.testBit i) = w.testBit i := by
    intro i hi
    rw [List.mem_range'_1] at hi
    simp [hi.1]
  have hl : List.filter (fun i => decide (2 ≤ i) && w.testBit i) (0 :: 1 :: List.range' 2 22) =
      List.filter (fun i => w.testBit i) (List.range' 2 22) := by
    rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_neg (by simp), List.filter_congr hc]
  have hr : List.filter (fun i => w.testBit i) (0 :: 1 :: List.range' 2 22) =
      0 :: 1 :: List.filter (fun i => w.testBit i) (List.range' 2 22) := by
    rw [List.filter_cons_of_pos h0, List.filter_cons_of_pos h1]
  rw [hl, hr]
  rfl

theorem spreadN_eq {w : Nat} (h0 : w.testBit 0 = true) (h1 : w.testBit 1 = true) (m : Nat) :
    Model.spreadN w m = CFSG.Monster.AxisCount.Native.spreadG w m := by
  unfold Model.spreadN CFSG.Monster.AxisCount.Native.spreadG
  rw [suppList_eq h0 h1, Rep4371.native_combN]

theorem octKT_eq {TH : Nat} (hTH : thOK TH = true) {b : Nat} (hb : b < 77) (m : Nat) :
    kd (octKT TH (octT b) m) = Model.octKey (octT b) m := by
  obtain ⟨hw, h3⟩ := octT_word hb
  have h0 : (Model.wordN (octT b)).testBit 0 = true := by
    rw [Nat.testBit_zero]
    simp
    omega
  have h1 : (Model.wordN (octT b)).testBit 1 = true := by
    rw [Nat.testBit_succ, Nat.testBit_zero]
    simp
    omega
  have hl : (KDense.TabAux.flt (fun i => (Model.wordN (octT b)).testBit i) 24).length = 8 := by
    rw [KDense.TabAux.flt_length_popcN]
    exact hw
  have hc : Model.octCode (octT b) m = CFSG.Monster.AxisCount.Native.octCodeG (octT b) m := by
    unfold Model.octCode CFSG.Monster.AxisCount.Native.octCodeG
    rw [spreadN_eq h0 h1, Rep4371.native_popcN]
    rfl
  unfold octKT
  simp only [strictN_eq, thH_eq hTH]
  rw [KeysOKAux.octCodeT_eq hw, thetaT_eq, dualT_eq, wordT_eq, KDense.TabAux.spreadT_eq hl, ← hc,
    ← spreadN_eq h0 h1]
  have hb' : Model.octCode (octT b) m < 4096 := by
    unfold Model.octCode
    have h12 : (4096 : Nat) = 2 ^ 12 := rfl
    rw [h12]
    refine Nat.xor_lt_two_pow (KeysOKAux.f12_lt _ _) ?_
    split <;> decide
  rw [kd_kc (by decide) hb']
  rfl

theorem dual_lor (i : Nat) : dualT (Nat.lor (nat_lit 1) (Nat.shiftLeft (nat_lit 1) i)) =
    Model.dualN (2 ^ 0 ||| 2 ^ i) := by
  rw [dualT_eq, Nat.lor_eq, Nat.shiftLeft_eq', Nat.one_shiftLeft]
  rfl

theorem dual_lor2 (i : Nat) : dualT (Nat.lor (nat_lit 2) (Nat.shiftLeft (nat_lit 1) i)) =
    Model.dualN (2 ^ 1 ||| 2 ^ i) := by
  rw [dualT_eq, Nat.lor_eq, Nat.shiftLeft_eq', Nat.one_shiftLeft]
  rfl

theorem rawModel_eq {TH : Nat} (hTH : thOK TH = true) (k : Nat) :
    Model.rawModel k = (rawT TH k).map td := by
  unfold rawT
  by_cases h0 : k = 0
  · subst h0
    rfl
  have hb0 : Nat.beq k (nat_lit 0) = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact h0 (Nat.eq_of_beq_eq_true h)
  rw [hb0, lIf_false]
  unfold Model.rawModel
  rw [if_neg h0]
  by_cases h22 : k ≤ 22
  · rw [ble_true h22, lIf_true, if_pos h22]
    simp only [List.map_cons, List.map_nil, td]
    have hk1 : Nat.add k (nat_lit 1) < 4096 := by
      change k + 1 < 4096
      omega
    rw [kd_kc (by decide) hk1]
    rfl
  rw [ble_false h22, lIf_false, if_neg h22]
  by_cases h66 : k ≤ 66
  · rw [ble_true h66, lIf_true, if_pos h66]
    unfold rawPair
    simp only [strictL_eq]
    have hi : Nat.add (Nat.shiftRight (Nat.sub k (nat_lit 23)) (nat_lit 1)) (nat_lit 2) = (k - 23) / 2 + 2 := by
      change (k - 23) >>> 1 + 2 = _
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
    rw [hi, dual_lor, dual_lor2]
    have hpar : Nat.land (Nat.sub k (nat_lit 23)) (nat_lit 1) = (k - 23) % 2 := Nat.and_one_is_mod _
    rw [hpar]
    simp only [List.map_cons, List.map_nil, td]
    rcases Nat.mod_two_eq_zero_or_one (k - 23) with h | h
    · rw [if_pos h, h]
      rw [kd_kc (by decide) (by decide), kd_kc (by decide) (by decide)]
      rfl
    · rw [if_neg (by omega), h]
      rw [kd_kc (by decide) (by decide), kd_kc (by decide) (by decide)]
      rfl
  rw [ble_false h66, lIf_false, if_neg h66]
  by_cases h1090 : k ≤ 1090
  · rw [ble_true h1090, lIf_true, if_pos h1090]
    simp only [strictL_eq, List.map_cons, List.map_nil, td]
    rw [oddCodes_get (by omega), oddKT_eq hTH (oddT_lt _), oddKT_eq hTH (oddT_lt _)]
    rfl
  rw [ble_false h1090, lIf_false, if_neg h1090]
  by_cases h2322 : k ≤ 2322
  · rw [ble_true h2322, lIf_true, if_pos h2322]
    unfold octPair
    simp only [strictL_eq, List.map_cons, List.map_nil, td]
    have hq : Nat.shiftRight (Nat.sub k (nat_lit 1091)) (nat_lit 4) = (k - 1091) / 16 := by
      change (k - 1091) >>> 4 = _
      rw [Nat.shiftRight_eq_div_pow]
    have hr : Nat.land (Nat.sub k (nat_lit 1091)) (nat_lit 15) = (k - 1091) % 16 :=
      Nat.and_two_pow_sub_one_eq_mod _ 4
    have hq77 : (k - 1091) / 16 < 77 := by omega
    have hr16 : (k - 1091) % 16 < 16 := Nat.mod_lt _ (by decide)
    rw [hq, hr, octKT_eq hTH hq77, octKT_eq hTH hq77, octCoeffs_get hq77,
      (localPairs_tab _ hr16).1, (localPairs_tab _ hr16).2]
  rw [ble_false h2322, lIf_false, if_neg h2322]
  simp only [List.map_cons, List.map_nil, td]
  have hm : Nat.mod (Nat.sub k (nat_lit 2323)) (nat_lit 1024) = (k - 2323) % 1024 := rfl
  have hη : nIf(Nat.ble (nat_lit 3347) k, nat_lit 1, nat_lit 0) = (decide (3347 ≤ k)).toNat := by
    by_cases h : 3347 ≤ k
    · rw [ble_true h, decide_eq_true h]
      rfl
    · rw [ble_false h, decide_eq_false h]
      rfl
  rw [hm, hη, kd_kc (by decide) (Nat.lt_of_lt_of_le (toNat_lt _) (by decide)), ← keyW_eq,
    oddCodes_get (Nat.mod_lt _ (by decide))]

theorem appT_eq (L M : Terms) : appT L M = L ++ M := by
  induction L with
  | nil => rfl
  | cons f L ih =>
    change List.cons f (appT L M) = _
    rw [ih]
    rfl

theorem scaleT_eq (m : Int) (L : Terms) : scaleT m L = L.map fun f => (f.1, m * f.2) := by
  induction L with
  | nil => rfl
  | cons f L ih =>
    change List.cons (f.1, Int.mul m f.2) (scaleT m L) = _
    rw [ih]
    rfl

theorem actVecT_eq {act : Model.Key → List (Model.Key × Int)} {f : Nat → Terms}
    (h : ∀ κ, act (kd κ) = (f κ).map td) (L : Terms) :
    Model.actVec act (L.map td) = (actVecT f L).map td := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    unfold Model.actVec at ih ⊢
    rw [List.map_cons, List.flatMap_cons, ih]
    change _ = (appT (scaleT e.2 (f e.1)) (actVecT f L)).map td
    rw [appT_eq, scaleT_eq, List.map_append]
    congr 1
    change (act (kd e.1)).map (fun g => (g.1, e.2 * g.2)) = _
    rw [h e.1, List.map_map, List.map_map]
    rfl

theorem rowModel_eq {TH : Nat} (hTH : thOK TH = true) (row : Array (Nat × Int)) :
    Model.rowModel row = (actVecT (rawT TH) row.toList).map td := by
  unfold Model.rowModel
  generalize row.toList = L
  induction L with
  | nil => rfl
  | cons e L ih =>
    rw [List.flatMap_cons, ih]
    change _ = (appT (scaleT e.2 (rawT TH e.1)) (actVecT (rawT TH) L)).map td
    rw [appT_eq, scaleT_eq, List.map_append, List.map_map, rawModel_eq hTH, List.map_map]
    rfl

theorem sgI_two (s : Nat) : 2 * sgI s 1 = sgI s 2 := by
  unfold sgI
  cases Nat.beq s 1 <;> rfl

theorem tauRow_eq {k : Nat} (hk : k < 4371) : Model.tauRow k = (tauT k).toArray := by
  unfold tauT
  by_cases h0 : k = 0
  · subst h0
    rfl
  have hb0 : Nat.beq k (nat_lit 0) = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact h0 (Nat.eq_of_beq_eq_true h)
  rw [hb0, lIf_false]
  unfold Model.tauRow
  rw [if_neg h0]
  by_cases h22 : k ≤ 22
  · rw [ble_true h22, lIf_true, if_pos h22]
    rfl
  rw [ble_false h22, lIf_false, if_neg h22]
  by_cases h66 : k ≤ 66
  · rw [ble_true h66, lIf_true, if_pos h66]
    have hpar : Nat.land (Nat.sub k (nat_lit 23)) (nat_lit 1) = (k - 23) % 2 := Nat.and_one_is_mod _
    have hh : Nat.shiftRight (Nat.sub k (nat_lit 23)) (nat_lit 1) = (k - 23) / 2 := by
      change (k - 23) >>> 1 = _
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
    rw [hpar, hh]
    rcases Nat.mod_two_eq_zero_or_one (k - 23) with h | h
    · rw [if_pos h, h]
      rfl
    · rw [if_neg (by omega), h]
      rfl
  rw [ble_false h66, lIf_false, if_neg h66]
  by_cases h1090 : k ≤ 1090
  · rw [ble_true h1090, lIf_true, if_pos h1090, oddCodes_get (by omega), bitN_eq, wordT_eq,
      sgI_toNat]
    rfl
  rw [ble_false h1090, lIf_false, if_neg h1090]
  by_cases h2322 : k ≤ 2322
  · rw [ble_true h2322, lIf_true, if_pos h2322]
    unfold tauOct
    simp only [strictL_eq]
    rw [buildL_eq]
    have hq : Nat.shiftRight (Nat.sub k (nat_lit 1091)) (nat_lit 4) = (k - 1091) / 16 := by
      change (k - 1091) >>> 4 = _
      rw [Nat.shiftRight_eq_div_pow]
    have hr : Nat.land (Nat.sub k (nat_lit 1091)) (nat_lit 15) = (k - 1091) % 16 :=
      Nat.and_two_pow_sub_one_eq_mod _ 4
    rw [hq, hr]
    apply Array.toList_inj.mp
    rw [Array.toList_map, Array.toList_range, List.toList_toArray]
    apply List.map_congr_left
    intro j hj
    have hj16 : j < 16 := List.mem_range.mp hj
    rw [mentry_tab _ (Nat.mod_lt _ (by decide)) _ hj16, sgI_two]
    rfl
  rw [ble_false h2322, lIf_false, if_neg h2322]
  by_cases h3346 : k ≤ 3346
  · rw [ble_true h3346, lIf_true, if_pos h3346, oddCodes_get (by omega), pT_model, sgI_toNat]
    rfl
  rw [ble_false h3346, lIf_false, if_neg h3346, oddCodes_get (by omega), bitN_eq, wordT_eq, pT_model,
    toNat_xor_eq, sgI_toNat]
  rfl

end CFSG.KC.Rep4371X

end
