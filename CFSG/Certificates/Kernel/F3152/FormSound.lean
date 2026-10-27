module

public import CFSG.Certificates.Kernel.F3152.LineSound
public import CFSG.Certificates.Kernel.BabyMonster.PktDecode
public import CFSG.Certificates.Kernel.Spor.TextAtSound
public import CFSG.Certificates.Kernel.Spor.F3LaneSepSound
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.KS.F3152

open CFSG.F3.Native CFSG.KS.F3L CFSG.Monster.B.Fischer.Native CFSG.KC.BM.B64 CFSG.KC.BM.Pkt

theorem ofNat_toNat_ascii : ∀ x < 128, (Char.ofNat x).toNat = x := by decide +kernel

theorem chAt_eq (N m : Nat) : chAt N m = (N >>> (8 * m)) % 256 :=
  Nat.and_two_pow_sub_one_eq_mod _ 8

theorem flatMap_get {L : List (Nat × Nat)} (hw : ∀ p ∈ L, p.2 = 752) :
    ∀ {r m : Nat}, r < L.length → m < 752 →
      (L.flatMap pieceBytes)[752 * r + m]? = some (chAt (L.getD r (0, 0)).1 m) := by
  induction L with
  | nil => intro r m hr; exact absurd hr (Nat.not_lt_zero r)
  | cons p L ih =>
    intro r m hr hm
    have hp : p.2 = 752 := hw p List.mem_cons_self
    have hlen : (pieceBytes p).length = 752 := by
      unfold pieceBytes
      rw [List.length_map, List.length_range, hp]
    rw [List.flatMap_cons]
    rcases r with _ | r
    · simp only [Nat.mul_zero, Nat.zero_add]
      rw [List.getElem?_append_left (by omega)]
      unfold pieceBytes
      rw [List.getElem?_map, List.getElem?_range (by omega)]
      rfl
    · have e : 752 * (r + 1) + m - 752 = 752 * r + m := by omega
      rw [List.getElem?_append_right (by omega), hlen, e]
      exact ih (fun q hq => hw q (List.mem_cons_of_mem _ hq)) (by simpa using hr) hm

theorem text_get {CH : List (Nat × Nat)} {n : Nat} {S : Nat → V} (hlen : CH.length = n)
    (hl : ∀ r < n, CH[r]? = some ((CH.getD r (0, 0)).1, 752) ∧
      lineOK (S r) (CH.getD r (0, 0)).1 = true) {r m : Nat} (hr : r < n) (hm : m < 752) :
    ((String.ofList (CFSG.KC.YModel.charsOf CH)).toUTF8.get! (752 * r + m)).toNat =
      ((CH.getD r (0, 0)).1 >>> (8 * m)) % 256 := by
  have hmem : ∀ p ∈ CH, ∃ r < n, p = ((CH.getD r (0, 0)).1, 752) := by
    intro p hp
    obtain ⟨r, hr, e⟩ := List.getElem_of_mem hp
    refine ⟨r, by omega, ?_⟩
    have := (hl r (by omega)).1
    rw [List.getElem?_eq_getElem hr, e] at this
    exact Option.some.inj this
  have hw : ∀ p ∈ CH, p.2 = 752 := by
    intro p hp
    obtain ⟨r, _, rfl⟩ := hmem p hp
    rfl
  have hasc : ∀ x ∈ CH.flatMap pieceBytes, x < 128 := by
    intro x hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨r, hr, rfl⟩ := hmem p hp
    unfold pieceBytes at hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
    rw [chAt_eq]
    exact lineOK_code (hl r hr).2 (List.mem_range.1 hm)
  have hB := flatMap_get hw (r := r) (m := m) (by omega) hm
  have hj : 752 * r + m < (CH.flatMap pieceBytes).length := by
    rcases (List.getElem?_eq_some_iff.1 hB) with ⟨h, -⟩
    exact h
  rw [charsOf_eq, bytesOf_eq]
  have hc : ∀ c ∈ ((CH.flatMap pieceBytes).map Char.ofNat).take
      ((CH.flatMap pieceBytes).map Char.ofNat).length, c.toNat < 128 := by
    intro c hc
    rw [List.take_length] at hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    rw [ofNat_toNat_ascii x (hasc x hx)]
    exact hasc x hx
  rw [CFSG.KS.Text.get!_toUTF8 hc (by simpa using hj) (by simpa using hj), List.getElem_map]
  have e1 : (CH.flatMap pieceBytes)[752 * r + m] = chAt (CH.getD r (0, 0)).1 m := by
    rw [List.getElem?_eq_getElem hj] at hB
    exact Option.some.inj hB
  have hlt := hasc _ (List.getElem_mem hj)
  rw [ofNat_toNat_ascii _ hlt, UInt8.toNat_ofNat_of_lt' (by
    change _ < 256
    omega), e1, chAt_eq]

theorem toMat_polarRows (b : ByteArray) (off : Nat) :
    toMat 77 (polarRows b off) = toMat 77 (formRows b off) + (toMat 77 (formRows b off)).transpose := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [Matrix.add_apply, Matrix.transpose_apply, toMat_apply, toMat_apply, toMat_apply,
    polarRows_val b off hi hj]

theorem polarRows_wf (b : ByteArray) (off : Nat) : RowsWF (polarRows b off) := by
  intro i
  by_cases hi : i < 77
  · rw [polarRows_get b off hi]
    exact V.wf_add (formRows_wf b off i) (RowsWF.transpose 77 _ i)
  · rw [getElem!_neg _ i (by rw [polarRows_size]; exact hi)]
    exact V.wf_zero

theorem get_lt_three (a : V) (j : Nat) : a.get j < 3 := by
  unfold V.get
  split_ifs <;> omega

theorem natCast_inj3 {x y : Nat} (hx : x < 3) (hy : y < 3) (h : (x : ZMod 3) = y) : x = y := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h

theorem coefOK_of {C : Array V} {b : ByteArray} {off : Nat}
    (h : toMat 77 C + (toMat 77 C).transpose =
      toMat 77 (formRows b off) + (toMat 77 (formRows b off)).transpose) :
    coefOK C b off = true := by
  unfold coefOK
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro j hj
  by_cases hij : i ≤ j
  · rw [decide_eq_true hij, Bool.not_true, Bool.false_or, beq_iff_eq]
    have e := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
    simp only [Matrix.add_apply, Matrix.transpose_apply, toMat_apply] at e
    rw [formRows_val b off hi hj, formRows_val b off hj hi, ite_eq_left hij] at e
    have ht : trit b off (pairIdx i j) < 3 := Nat.mod_lt _ (by norm_num)
    unfold coefAt
    by_cases e' : i = j
    · subst e'
      rw [ite_eq_left rfl]
      rw [ite_eq_left le_rfl] at e
      apply natCast_inj3 (get_lt_three _ _) ht
      have h4 : (2 : ZMod 3) * 2 = 1 := by decide
      have e2 : (2 : ZMod 3) * C[i]!.val i = 2 * (trit b off (pairIdx i i) : ZMod 3) := by
        rw [two_mul, two_mul]
        exact e
      have e3 := congrArg ((2 : ZMod 3) * ·) e2
      simp only [← mul_assoc, h4, one_mul] at e3
      exact e3
    · rw [ite_eq_right e']
      have hji : ¬ j ≤ i := by omega
      rw [ite_eq_right hji, add_zero] at e
      have e2 : ((C[i]!.get j + C[j]!.get i : Nat) : ZMod 3) = (trit b off (pairIdx i j) : ZMod 3) := by
        push_cast
        exact e
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ht] at e2
      exact e2
  · rw [decide_eq_false hij]
    rfl

theorem pullback_of_polar {b b' : ByteArray} {off off' : Nat} {A : Array V} (hAw : RowsWF A)
    (h : (toMat 77 A).transpose * toMat 77 (polarRows b' off') * toMat 77 A = toMat 77 (polarRows b off)) :
    pullbackOK b off b' off' A (transpose 77 A) = true := by
  unfold pullbackOK
  apply coefOK_of
  have hT : (transpose 77 A).size = 77 := by
    unfold transpose
    rw [Array.size_ofFn]
  rw [toMat_mul hT (RowsWF.transpose 77 A) (RowsWF.mul _ 77 (formRows_wf b' off') hAw),
    toMat_mul (formRows_size b' off') (formRows_wf b' off') hAw, toMat_transpose,
    ← toMat_polarRows b off, ← h, toMat_polarRows]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]

theorem rowsWF_unlane {L : V} (h : L.wf = true) : RowsWF (unlane 77 L) :=
  RowsWF.of_canonM (canonM_unlane 77 h)

theorem pullback_of_lanes {A : Array V} {LA LAt Sg Sr : V} (hA : A = unlane 77 LA)
    (hLA : LA.wf = true) (htr : trLane 77 LA = LAt) {b b' : ByteArray} {off off' : Nat}
    (hg : polarRows b' off' = unlane 77 Sg) (hr : polarRows b off = unlane 77 Sr)
    (h : mulK LAt (mulK Sg LA) = Sr) : pullbackOK b off b' off' A (transpose 77 A) = true := by
  have hAw : RowsWF A := by
    rw [hA]
    exact rowsWF_unlane hLA
  apply pullback_of_polar hAw
  have e : mul 77 (transpose 77 A) (mul 77 (polarRows b' off') A) = polarRows b off := by
    simp only [hg, hr]
    rw [hA, transpose_unlane hLA, htr, mul_unlane (by norm_num), mul_unlane (by norm_num)]
    exact congrArg (unlane 77) h
  have hT : (transpose 77 A).size = 77 := by
    unfold transpose
    rw [Array.size_ofFn]
  have := congrArg (toMat 77) e
  rw [toMat_mul hT (RowsWF.transpose 77 A) (RowsWF.mul _ 77 (polarRows_wf b' off') hAw),
    toMat_mul (polarRows_size b' off') (polarRows_wf b' off') hAw, toMat_transpose] at this
  rw [Matrix.mul_assoc]
  exact this

end CFSG.KS.F3152

end
