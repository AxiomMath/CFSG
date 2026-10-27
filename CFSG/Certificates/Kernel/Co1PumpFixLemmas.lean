module

public import Certificates.Data.Kernel.Co1PumpFix
public import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas

public section

namespace CFSG.KS.Co1PumpFix

open CFSG.KC.Co1Pairs CFSG.KS CFSG.KS.SporSch.M24

@[expose] def pfPar (r v : ℕ) : Bool := ActL.xs (fun j => r.testBit j && v.testBit j) (List.range 24)

theorem pfPar_xor_right (r u w : ℕ) : pfPar r (u ^^^ w) = (pfPar r u ^^ pfPar r w) := by
  unfold pfPar
  rw [← ActL.xs_xor]
  refine ActL.xs_congr fun j _ => ?_
  rw [Nat.testBit_xor]
  cases r.testBit j <;> cases u.testBit j <;> cases w.testBit j <;> rfl

theorem pfPar_xor_left (r r' v : ℕ) : pfPar (r ^^^ r') v = (pfPar r v ^^ pfPar r' v) := by
  unfold pfPar
  rw [← ActL.xs_xor]
  refine ActL.xs_congr fun j _ => ?_
  rw [Nat.testBit_xor]
  cases r.testBit j <;> cases r'.testBit j <;> cases v.testBit j <;> rfl

theorem pfPar_of {s v : ℕ} (h : ∀ j < 24, s.testBit j = true → v.testBit j = false) :
    pfPar s v = false := by
  unfold pfPar
  rw [ActL.xs_congr (g := fun _ => false), ActL.xs_false]
  intro j hj
  cases hs : s.testBit j
  · rfl
  · rw [h j (List.mem_range.mp hj) hs]
    rfl

theorem pfPar_zero_left (v : ℕ) : pfPar 0 v = false :=
  pfPar_of fun j _ h => by simp at h

theorem pfPar_zero_right (r : ℕ) : pfPar r 0 = false :=
  pfPar_of fun j _ _ => Nat.zero_testBit j

theorem pf_xs_pow (q v : ℕ) : ∀ l : List ℕ, l.Nodup →
    ActL.xs (fun j => (2 ^ q).testBit j && v.testBit j) l = (decide (q ∈ l) && v.testBit q)
  | [], _ => by simp [ActL.xs_nil]
  | a :: l, hl => by
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    rw [ActL.xs_cons, pf_xs_pow q v l hl', Nat.testBit_two_pow]
    by_cases hqa : q = a
    · subst hqa
      simp [ha]
    · simp [hqa]

theorem pfPar_pow {q : ℕ} (v : ℕ) (hq : q < 24) : pfPar (2 ^ q) v = v.testBit q := by
  unfold pfPar
  rw [pf_xs_pow q v _ List.nodup_range]
  simp [hq]

theorem pf_testBit_actK (M v i : ℕ) :
    (actK M v).testBit i = (decide (i < 24) && pfPar (rowK M i) v) := by
  have h := ActL.testBit_foldr_or (fun i => Nat.beq (parK (Nat.land (rowK M i) v)) 1) i
    (List.range 24)
  beta_reduce at h
  rw [ActL.actK_eq_foldr, h, ActL.parK_and _ _ (ActL.rowK_lt M i)]
  simp only [List.mem_range, pfPar]

theorem pf_actK_xor (M u w : ℕ) : actK M (u ^^^ w) = actK M u ^^^ actK M w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, pf_testBit_actK, pf_testBit_actK, pf_testBit_actK, pfPar_xor_right]
  by_cases hi : i < 24 <;> simp [hi]

theorem pf_actK_lt (M v : ℕ) : actK M v < 2 ^ 24 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [pf_testBit_actK, decide_eq_false (by omega : ¬ i < 24), Bool.false_and]

theorem pf_actK_zero (M : ℕ) : actK M 0 = 0 :=
  Nat.eq_of_testBit_eq fun i => by
    rw [pf_testBit_actK, pfPar_zero_right, Bool.and_false, Nat.zero_testBit]

theorem pf_nrow {M v i : ℕ} (hv : actK M v = v) (hi : i < 24) : pfPar (nrowK M i) v = false := by
  have e : nrowK M i = rowK M i ^^^ 2 ^ i := by
    change rowK M i ^^^ 1 <<< i = _
    rw [Nat.one_shiftLeft]
  have h := pf_testBit_actK M v i
  rw [hv, decide_eq_true hi, Bool.true_and] at h
  rw [e, pfPar_xor_left, pfPar_pow v hi, ← h, Bool.xor_self]

theorem pf_selK {M v : ℕ} (c : ℕ) (hv : actK M v = v) : pfPar (selK M c) v = false := by
  have e : selK M c = (List.range 24).foldr
      (fun i s => if c.testBit i = true then s ^^^ nrowK M i else s) 0 := by
    refine (MatL.foldN_eq _ _).trans ?_
    simp only [MatL.nIf_eq, MatL.hasBit_eq]
    try rfl
  rw [e]
  suffices h : ∀ l : List ℕ, (∀ i ∈ l, i < 24) → pfPar (l.foldr
      (fun i s => if c.testBit i = true then s ^^^ nrowK M i else s) 0) v = false from
    h _ fun i hi => List.mem_range.mp hi
  intro l
  induction l with
  | nil => exact fun _ => pfPar_zero_left v
  | cons a l ih =>
    intro hl
    have ih' := ih fun i hi => hl i (List.mem_cons_of_mem _ hi)
    rw [List.foldr_cons]
    split
    · rw [pfPar_xor_left, ih', pf_nrow hv (hl a (by simp))]
      rfl
    · exact ih'

theorem pf_entK {M J q : ℕ} {e : ℕ × ℕ × ℕ} (h : entK M J q e = true) :
    (J.testBit q = true → actK M e.2.2 = e.2.2 ∧ e.2.2 &&& J = 2 ^ q) ∧
      (J.testBit q = false → e.2.1 &&& J = e.2.1 ∧ selK M e.1 = 2 ^ q ^^^ e.2.1) := by
  unfold entK at h
  generalize actK M e.2.2 = A at h ⊢
  generalize selK M e.1 = S at h ⊢
  rw [MatL.hasBit_eq] at h
  cases hq : J.testBit q
  · rw [hq] at h
    simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
    refine ⟨fun h' => absurd h' (by decide), fun _ => ⟨h.1, ?_⟩⟩
    rw [h.2]
    change (1 <<< q) ^^^ e.2.1 = _
    rw [Nat.one_shiftLeft]
  · rw [hq] at h
    simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
    refine ⟨fun _ => ⟨h.1, ?_⟩, fun h' => absurd h' (by decide)⟩
    have h2 := h.2
    change e.2.2 &&& J = 1 <<< q at h2
    rw [h2, Nat.one_shiftLeft]

theorem pf_entsK_nil {M J q : ℕ} (h : entsK M J [] q = true) : q = 24 := by
  have h' : Nat.beq q 24 = true := h
  exact Nat.eq_of_beq_eq_true h'

theorem pf_entsK_cons {M J q : ℕ} {e : ℕ × ℕ × ℕ} {F : List (ℕ × ℕ × ℕ)}
    (h : entsK M J (e :: F) q = true) : entK M J q e = true ∧ entsK M J F (q + 1) = true := by
  have h' : bAnd(entK M J q e, entsK M J F (q + 1)) = true := h
  rw [MatL.bAnd_eq, Bool.and_eq_true] at h'
  exact h'

theorem pf_entsK {M J : ℕ} : ∀ {F : List (ℕ × ℕ × ℕ)} {q : ℕ}, entsK M J F q = true →
    q + F.length = 24 ∧ ∀ i (hi : i < F.length), entK M J (q + i) F[i] = true
  | [], q, h => ⟨by simpa using pf_entsK_nil h, fun i hi => absurd hi (by simp)⟩
  | e :: F, q, h => by
    obtain ⟨h1, h2⟩ := pf_entsK_cons h
    obtain ⟨h3, h4⟩ := pf_entsK h2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => simpa using h1
    | succ i =>
      have := h4 i (by simpa using hi)
      rw [show q + (i + 1) = q + 1 + i by omega]
      simpa using this

@[expose] def pfL (J : ℕ) : List (ℕ × ℕ × ℕ) → ℕ → ℕ → List ℕ
  | [], _, x => [x]
  | e :: F, q, x => if J.testBit q = true then pfL J F (q + 1) x ++ pfL J F (q + 1) (x ^^^ e.2.2)
      else pfL J F (q + 1) x

theorem pf_cntK (mem : ℕ → Bool) (J : ℕ) : ∀ (F : List (ℕ × ℕ × ℕ)) (q x acc : ℕ),
    cntK mem J F q x acc = acc + (pfL J F q x).countP mem
  | [], q, x, acc => by
    change Bool.rec (motive := fun _ => ℕ) acc (Nat.succ acc) (mem x) = _
    simp only [pfL]
    cases hm : mem x <;> simp [hm]
  | e :: F, q, x, acc => by
    have ih := pf_cntK mem J F (q + 1)
    have hx : Nat.xor x e.2.2 = x ^^^ e.2.2 := rfl
    change Bool.rec (motive := fun _ => ℕ) (cntK mem J F (q + 1) x acc)
      (cntK mem J F (q + 1) (Nat.xor x e.2.2) (cntK mem J F (q + 1) x acc)) (hasBit J q) = _
    rw [MatL.hasBit_eq, hx]
    simp only [ih, pfL]
    cases J.testBit q
    · simp
    · simp only [if_true, List.countP_append]
      omega

theorem pf_L_fixed {M J : ℕ} : ∀ {F : List (ℕ × ℕ × ℕ)} {q x : ℕ}, entsK M J F q = true →
    actK M x = x → ∀ y ∈ pfL J F q x, actK M y = y
  | [], q, x, _, hx, y, hy => by
    simp only [pfL, List.mem_singleton] at hy
    rw [hy]
    exact hx
  | e :: F, q, x, h, hx, y, hy => by
    obtain ⟨h1, h2⟩ := pf_entsK_cons h
    simp only [pfL] at hy
    split at hy
    · rename_i hq
      rcases List.mem_append.mp hy with hy | hy
      · exact pf_L_fixed h2 hx y hy
      · refine pf_L_fixed h2 ?_ y hy
        rw [pf_actK_xor, hx, ((pf_entK h1).1 hq).1]
    · exact pf_L_fixed h2 hx y hy

theorem pf_L_low {M J : ℕ} : ∀ {F : List (ℕ × ℕ × ℕ)} {q x : ℕ}, entsK M J F q = true →
    ∀ y ∈ pfL J F q x, ∀ j, J.testBit j = true → j < q → y.testBit j = x.testBit j
  | [], q, x, _, y, hy, j, _, _ => by
    simp only [pfL, List.mem_singleton] at hy
    rw [hy]
  | e :: F, q, x, h, y, hy, j, hj, hjq => by
    obtain ⟨h1, h2⟩ := pf_entsK_cons h
    simp only [pfL] at hy
    split at hy
    · rename_i hq
      rcases List.mem_append.mp hy with hy | hy
      · exact pf_L_low h2 y hy j hj (by omega)
      · rw [pf_L_low h2 y hy j hj (by omega), Nat.testBit_xor]
        have hb := congrArg (fun z => z.testBit j) ((pf_entK h1).1 hq).2
        simp only [Nat.testBit_and, hj, Bool.and_true, Nat.testBit_two_pow] at hb
        rw [hb, decide_eq_false (by omega), Bool.xor_false]
    · exact pf_L_low h2 y hy j hj (by omega)

theorem pf_L_bit {M J q x : ℕ} {e : ℕ × ℕ × ℕ} {F : List (ℕ × ℕ × ℕ)}
    (h : entsK M J (e :: F) q = true) (hq : J.testBit q = true) :
    ∀ y ∈ pfL J F (q + 1) (x ^^^ e.2.2), y.testBit q = !x.testBit q := by
  intro y hy
  obtain ⟨h1, h2⟩ := pf_entsK_cons h
  rw [pf_L_low h2 y hy q hq (by omega), Nat.testBit_xor]
  have hb := congrArg (fun z => z.testBit q) ((pf_entK h1).1 hq).2
  simp only [Nat.testBit_and, hq, Bool.and_true, Nat.testBit_two_pow, decide_true] at hb
  rw [hb]
  cases x.testBit q <;> rfl

theorem pf_L_nodup {M J : ℕ} : ∀ {F : List (ℕ × ℕ × ℕ)} {q x : ℕ}, entsK M J F q = true →
    (pfL J F q x).Nodup
  | [], q, x, _ => by simp [pfL]
  | e :: F, q, x, h => by
    obtain ⟨_, h2⟩ := pf_entsK_cons h
    simp only [pfL]
    split
    · rename_i hq
      refine List.Nodup.append (pf_L_nodup h2) (pf_L_nodup h2) ?_
      intro y hy1 hy2
      have e1 := pf_L_low h2 y hy1 q hq (by omega)
      have e2 := pf_L_bit (x := x) h hq y hy2
      rw [e1] at e2
      cases hx : x.testBit q <;> rw [hx] at e2 <;> exact absurd e2 (by decide)
    · exact pf_L_nodup h2

theorem pf_L_length {M J : ℕ} : ∀ {F : List (ℕ × ℕ × ℕ)} {q x : ℕ}, entsK M J F q = true →
    (pfL J F q x).length = 2 ^ ((List.range' q F.length).countP fun j => J.testBit j)
  | [], q, x, _ => by simp [pfL]
  | e :: F, q, x, h => by
    obtain ⟨_, h2⟩ := pf_entsK_cons h
    simp only [pfL, List.length_cons, List.range'_succ, List.countP_cons]
    split
    · rename_i hq
      rw [List.length_append, pf_L_length h2, pf_L_length h2]
      simp [hq, pow_succ, mul_two]
    · rename_i hq
      rw [pf_L_length h2]
      simp [hq]

theorem pf_L_exists {M J : ℕ} : ∀ {F : List (ℕ × ℕ × ℕ)} {q x v : ℕ}, entsK M J F q = true →
    (∀ j, J.testBit j = true → j < q → v.testBit j = x.testBit j) →
    ∃ y ∈ pfL J F q x, ∀ j, J.testBit j = true → j < 24 → v.testBit j = y.testBit j
  | [], q, x, v, h, hv => by
    have hq := pf_entsK_nil h
    subst hq
    exact ⟨x, by simp [pfL], fun j hj hj24 => hv j hj hj24⟩
  | e :: F, q, x, v, h, hv => by
    obtain ⟨h1, h2⟩ := pf_entsK_cons h
    simp only [pfL]
    split
    · rename_i hq
      by_cases hvx : v.testBit q = x.testBit q
      · obtain ⟨y, hy, hy'⟩ := pf_L_exists (x := x) (v := v) h2 fun j hj hjq => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hjq with hjq | rfl
          · exact hv j hj hjq
          · exact hvx
        exact ⟨y, List.mem_append_left _ hy, hy'⟩
      · obtain ⟨y, hy, hy'⟩ := pf_L_exists (x := x ^^^ e.2.2) (v := v) h2 fun j hj hjq => by
          have hb := congrArg (fun z => z.testBit j) ((pf_entK h1).1 hq).2
          simp only [Nat.testBit_and, hj, Bool.and_true, Nat.testBit_two_pow] at hb
          rw [Nat.testBit_xor, hb]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hjq with hjq | rfl
          · rw [decide_eq_false (by omega), Bool.xor_false]
            exact hv j hj hjq
          · rw [decide_eq_true rfl]
            revert hvx
            cases v.testBit j <;> cases x.testBit j <;> decide
        exact ⟨y, List.mem_append_right _ hy, hy'⟩
    · rename_i hq
      exact pf_L_exists h2 fun j hj hjq => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjq with hjq | rfl
        · exact hv j hj hjq
        · simp [hj] at hq

theorem pf_zero {M J : ℕ} {F : List (ℕ × ℕ × ℕ)} (h : entsK M J F 0 = true) {u : ℕ}
    (hu : actK M u = u) (hu24 : u < 2 ^ 24) (hJ : ∀ j < 24, J.testBit j = true → u.testBit j = false) :
    u = 0 := by
  obtain ⟨hlen, hent⟩ := pf_entsK h
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit]
  by_cases hj : j < 24
  · cases hJj : J.testBit j
    · have hi : j < F.length := by omega
      have he := (pf_entK (hent j hi)).2
      rw [Nat.zero_add] at he
      obtain ⟨hs, hsel⟩ := he hJj
      have h0 := pf_selK (F[j]).1 hu
      rw [hsel, pfPar_xor_left, pfPar_pow u hj] at h0
      have h1 : pfPar (F[j]).2.1 u = false := pfPar_of fun k hk hsk => by
        have := congrArg (fun z => z.testBit k) hs
        simp only [Nat.testBit_and, hsk, Bool.true_and] at this
        exact hJ k hk this
      rw [h1, Bool.xor_false] at h0
      exact h0
    · exact hJ j hj hJj
  · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hu24 (Nat.pow_le_pow_right (by norm_num)
      (by omega)))

theorem pf_popK (J : ℕ) : popK J = (List.range' 0 24).countP fun j => J.testBit j := by
  have e : popK J = (List.range 24).foldr
      (fun i s => if J.testBit i = true then Nat.succ s else s) 0 := by
    refine (MatL.foldN_eq _ _).trans ?_
    simp only [MatL.nIf_eq, MatL.hasBit_eq]
    try rfl
  rw [e, ← List.range_eq_range']
  generalize List.range 24 = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih, List.countP_cons]
    split <;> simp_all

theorem entsK_fixed {M J : ℕ} {F : List (ℕ × ℕ × ℕ)} (h : entsK M J F 0 = true) :
    ∃ L : List ℕ, L.Nodup ∧ L.length = 2 ^ popK J ∧ (∀ x ∈ L, x < 2 ^ 24) ∧
      (∀ v < 2 ^ 24, CFSG.KS.SporSch.M24.actK M v = v ↔ v ∈ L) ∧
      ∀ mem : ℕ → Bool, cntK mem J F 0 0 0 = L.countP mem := by
  obtain ⟨hlen, -⟩ := pf_entsK h
  rw [Nat.zero_add] at hlen
  have hfix := pf_L_fixed (x := 0) h (pf_actK_zero M)
  refine ⟨pfL J F 0 0, pf_L_nodup h, ?_, fun x hx => ?_, fun v hv => ⟨fun hfv => ?_, fun hvL => ?_⟩,
    fun mem => ?_⟩
  · rw [pf_L_length h, hlen, pf_popK]
  · rw [← hfix x hx]
    exact pf_actK_lt M x
  · obtain ⟨y, hy, hvy⟩ := pf_L_exists (x := 0) (v := v) h fun j _ hj => absurd hj (by omega)
    have hyf := hfix y hy
    have hy24 : y < 2 ^ 24 := by
      rw [← hyf]
      exact pf_actK_lt M y
    have hu : v ^^^ y = 0 := pf_zero h (by rw [pf_actK_xor, hfv, hyf])
      (Nat.xor_lt_two_pow hv hy24) fun j hj hJj => by
        rw [Nat.testBit_xor, hvy j hJj hj, Bool.xor_self]
    have hvy' : v = y := Nat.eq_of_testBit_eq fun j => by
      have := congrArg (fun z => z.testBit j) hu
      simp only [Nat.testBit_xor, Nat.zero_testBit] at this
      revert this
      cases v.testBit j <;> cases y.testBit j <;> decide
    rw [hvy']
    exact hy
  · exact hfix v hvL
  · rw [pf_cntK, Nat.zero_add]

end CFSG.KS.Co1PumpFix

end
