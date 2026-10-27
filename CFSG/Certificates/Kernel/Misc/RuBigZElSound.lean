module

public import Certificates.Data.Kernel.Misc.RuBigZFix
public import CFSG.Certificates.Kernel.Misc.RuBigZSound

public section

namespace CFSG.KC.Misc.RuBigZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuScan

@[expose] def NcB (f P : Nat → Nat) (o r : Nat) : Prop :=
  ∃ k < r, ∃ p < 4060, f (apP (P (o + k)) p) ≠ apP (P (o + k)) (f p)

@[expose] def OrbC (f : Nat → Nat) (x xi J : Nat) (P : Nat → Nat) (o : Nat) : Prop :=
  (∃ p < 4060, f (f p) ≠ p) ∨
  (∃ j, 1 ≤ j ∧ j ≤ J ∧ ∃ p < 4060,
    f (xAp x j (f (xAp xi j p))) ≠ xAp x j (f (xAp xi j (f p)))) ∨
  ∃ m < 32, ∀ b < 4, f b = mAp P o 5 m b

@[expose] def TwoC (ys : List Nat) (E : Nat) : Prop :=
  ∀ b < 4, ∃ e ≤ E, yPow ys (2 ^ e) b = b

@[expose] def G16C (f R : Nat → Nat) (g gi : Nat) : Prop :=
  ∀ k < 4, ∀ b < 4, apP g (f (apP gi (apP (R (12 + k)) b))) =
    apP (R (12 + k)) (apP g (f (apP gi b)))

theorem testBit_foldr_lor (g : Nat → Nat) (s : Nat) :
    ∀ (l : List Nat) {j : Nat}, j ∈ l →
      (l.foldr (fun j acc => Nat.lor acc (Nat.shiftLeft 1 (g j))) s).testBit (g j) = true
  | [], _, hj => absurd hj List.not_mem_nil
  | a :: l, j, hj => by
    have e : ∀ x y : Nat, Nat.lor x y = x ||| y := fun _ _ => rfl
    rw [List.foldr_cons, e, Nat.testBit_lor, Bool.or_eq_true]
    rcases List.mem_cons.mp hj with rfl | hj
    · right
      rw [shl1, Nat.testBit_two_pow_self]
    · left
      exact testBit_foldr_lor g s l hj

theorem notIn_testBit {m r : Nat} (h : notIn m r = true) : m.testBit r = false := by
  unfold notIn at h
  rw [← fld_one_beq]
  have h0 : Nat.land (Nat.shiftRight m r) 1 = 0 := Nat.eq_of_beq_eq_true h
  rw [h0]
  rfl

theorem bIf_ft {c : Bool} (h : bIf(c, false, true) = true) : c = false := by
  cases c
  · rfl
  · exact absurd h Bool.false_ne_true

theorem twoB_sound {ys : List Nat} {e b : Nat} (h : twoB ys e b = true) :
    yPow ys (2 ^ e) b = b := by
  unfold twoB at h
  rw [shl1] at h
  exact Nat.eq_of_beq_eq_true h

theorem spB_sound {ys : List Nat} {P : Nat → Nat} {o r m : Nat} (h : spB ys P o r m = true) :
    m < 2 ^ r ∧ ∀ b < 4, yAp ys b = mAp P o r m b := by
  unfold spB at h
  rw [RuBase.bAnd_eq', Bool.and_eq_true] at h
  refine ⟨?_, fun b hb => Nat.eq_of_beq_eq_true (RuBase.allN_iff.1 h.2 b hb)⟩
  have := Nat.blt_eq.mp h.1
  rwa [shl1] at this

theorem orbOK_sound {ys : List Nat} {x xi J : Nat} {P : Nat → Nat} {o sub pl : Nat}
    (h : orbOK ys x xi J P o sub pl = true) : OrbC (yAp ys) x xi J P o := by
  unfold orbOK at h
  simp only [sB] at h
  cases h0 : Nat.beq sub (nat_lit 0)
  · rw [h0] at h
    cases h1 : Nat.beq sub (nat_lit 1)
    · rw [h1] at h
      cases h2 : Nat.beq sub (nat_lit 2)
      · rw [h2] at h
        exact absurd h Bool.false_ne_true
      · rw [h2] at h
        have h' : spB ys P o 5 pl = true := h
        obtain ⟨hm, hb⟩ := spB_sound h'
        exact Or.inr (Or.inr ⟨pl, hm, hb⟩)
    · rw [h1] at h
      have h' : bAnd(Nat.ble 1 (fld(pl, 0, 3)), bAnd(Nat.ble (fld(pl, 0, 3)) J,
          bAnd(Nat.blt (fld(pl, 2, 4095)) 4060,
            bIf(Nat.beq (yAp ys (xAp x (fld(pl, 0, 3)) (yAp ys (xAp xi (fld(pl, 0, 3))
              (fld(pl, 2, 4095))))))
              (xAp x (fld(pl, 0, 3)) (yAp ys (xAp xi (fld(pl, 0, 3)) (yAp ys (fld(pl, 2, 4095)))))),
              false, true)))) = true := h
      simp only [RuBase.bAnd_eq', Bool.and_eq_true] at h'
      exact Or.inr (Or.inl ⟨_, Nat.le_of_ble_eq_true h'.1, Nat.le_of_ble_eq_true h'.2.1, _,
        Nat.blt_eq.mp h'.2.2.1, Nat.ne_of_beq_eq_false (bIf_ft h'.2.2.2)⟩)
  · rw [h0] at h
    have h' : bAnd(Nat.blt (fld(pl, 0, 4095)) 4060,
        bIf(Nat.beq (yAp ys (yAp ys (fld(pl, 0, 4095)))) (fld(pl, 0, 4095)), false, true)) = true := h
    simp only [RuBase.bAnd_eq', Bool.and_eq_true] at h'
    exact Or.inl ⟨_, Nat.blt_eq.mp h'.1, Nat.ne_of_beq_eq_false (bIf_ft h'.2)⟩

theorem ncB_of {ys : List Nat} {R : Nat → Nat} {o r k p : Nat}
    (h : bAnd(Nat.blt p 4060, bAnd(Nat.blt k r, bIf(Nat.beq (yAp ys (apP (R (Nat.add o k)) p))
      (apP (R (Nat.add o k)) (yAp ys p)), false, true))) = true) : NcB (yAp ys) R o r := by
  simp only [RuBase.bAnd_eq', Bool.and_eq_true] at h
  exact ⟨k, Nat.blt_eq.mp h.2.1, p, Nat.blt_eq.mp h.1, Nat.ne_of_beq_eq_false (bIf_ft h.2.2)⟩

theorem twoC_of {ys : List Nat} {rec : Nat}
    (h : allN 4 (fun b => twoB ys (fld(rec, Nat.add 2 (Nat.mul 3 b), 7)) b) = true) : TwoC ys 7 :=
  fun b hb => ⟨fld(rec, Nat.add 2 (Nat.mul 3 b), 7), Nat.and_le_right,
    twoB_sound (RuBase.allN_iff.1 h b hb)⟩

theorem g16C_of {ys : List Nat} {R : Nat → Nat} {g gi : Nat} (h : g16B ys R g gi = true) :
    G16C (yAp ys) R g gi := fun k hk b hb => by
  unfold g16B at h
  have h1 := RuBase.allN_iff.1 h k hk
  simp only [sB] at h1
  exact Nat.eq_of_beq_eq_true (RuBase.allN_iff.1 h1 b hb)

theorem orbM_sound {LR TR : Nat → Nat} {v r : Nat} (h : notIn (orbM LR TR v) r = true) {a b : Nat}
    (ha : a < rcnt (LR 1)) (hb : b < rcnt (LR 2)) :
    yAp [TR (roff 4060 48720 (LR 1) + a), TR (roff 4060 48720 (LR 2) + b)] (apP v 0) ≠ r := by
  intro he
  have hb' := notIn_testBit h
  unfold orbM at hb'
  simp only [sN] at hb'
  rw [Raw.Orb.foldN_eq] at hb'
  obtain ⟨hj, e1, e2⟩ := idx2 ha hb
  have key := testBit_foldr_lor (fun j => yAp [TR (roff 4060 48720 (LR 1) + j / rcnt (LR 2)),
    TR (roff 4060 48720 (LR 2) + j % rcnt (LR 2))] (apP v 0)) 0
    (List.range (rcnt (LR 1) * rcnt (LR 2))) (List.mem_range.mpr hj)
  simp only [e1, e2, he] at key
  exact Bool.false_ne_true (hb'.symm.trans key)

theorem l0OK_sound {LR TR R L : Nat → Nat} {i : Nat} (h : l0OK LR TR R L i = true)
    (hk : l0kOK L i = true) :
    (∀ X < 5, L (21 * i + X) ≠ 1 → ∃ k < rkX X, ∃ r < 4060,
      apP (TR (roff 4060 48720 (LR 0) + i)) r =
        apP (R (bX X + k)) (apP (TR (roff 4060 48720 (LR 0) + i)) 0) ∧
      notIn (orbM LR TR (R (bX X + k))) r = true) ∧
    (L (21 * i + 5) ≠ 1 → ∃ k < 4, ∀ w < 16, ∃ r < 4060,
      apP (TR (roff 4060 48720 (LR 0) + i)) r =
        apP (R (21 + w)) (apP (TR (roff 4060 48720 (LR 0) + i)) 0) ∧
      notIn (orbM LR TR (R (12 + k))) r = true) := by
  unfold l0OK at h
  unfold l0kOK at hk
  simp only [sB, RuBase.bAnd_eq', Bool.and_eq_true] at h
  simp only [sB] at hk
  obtain ⟨hA, hB⟩ := h
  refine ⟨fun X hX hne => ?_, fun hne => ?_⟩
  · have hb : Nat.beq (L (21 * i + X)) 1 = false :=
      Bool.eq_false_iff.mpr fun e => hne (Nat.eq_of_beq_eq_true e)
    have h1 : bIf(Nat.beq (L (21 * i + X)) 1, true,
        bAnd(Nat.blt (L (21 * i + X) >>> 5) 4060,
          bAnd(Nat.beq (apP (TR (roff 4060 48720 (LR 0) + i)) (L (21 * i + X) >>> 5))
            (apP (R (bX X + fld(L (21 * i + X), 1, 15))) (apP (TR (roff 4060 48720 (LR 0) + i)) 0)),
          notIn (orbM LR TR (R (bX X + fld(L (21 * i + X), 1, 15)))) (L (21 * i + X) >>> 5))))
        = true := RuBase.allN_iff.1 hA X hX
    have h2 : bIf(Nat.beq (L (21 * i + X)) 1, true,
        Nat.blt (fld(L (21 * i + X), 1, 15)) (nIf(Nat.blt X 5, rkX X, 4))) = true :=
      RuBase.allN_iff.1 hk X (by omega)
    rw [hb] at h1 h2
    have h2' : Nat.blt (fld(L (21 * i + X), 1, 15)) (nIf(Nat.blt X 5, rkX X, 4)) = true := h2
    rw [Nat.blt_eq.mpr hX] at h2'
    have hk' : fld(L (21 * i + X), 1, 15) < rkX X := Nat.blt_eq.mp h2'
    have h1' : bAnd(Nat.blt (L (21 * i + X) >>> 5) 4060,
        bAnd(Nat.beq (apP (TR (roff 4060 48720 (LR 0) + i)) (L (21 * i + X) >>> 5))
          (apP (R (bX X + fld(L (21 * i + X), 1, 15))) (apP (TR (roff 4060 48720 (LR 0) + i)) 0)),
        notIn (orbM LR TR (R (bX X + fld(L (21 * i + X), 1, 15)))) (L (21 * i + X) >>> 5))) = true :=
      h1
    simp only [RuBase.bAnd_eq', Bool.and_eq_true] at h1'
    exact ⟨_, hk', _, Nat.blt_eq.mp h1'.1, Nat.eq_of_beq_eq_true h1'.2.1, h1'.2.2⟩
  · have hb : Nat.beq (L (21 * i + 5)) 1 = false :=
      Bool.eq_false_iff.mpr fun e => hne (Nat.eq_of_beq_eq_true e)
    have hB' : bIf(Nat.beq (L (21 * i + 5)) 1, true, allN 16 (fun w =>
        bAnd(Nat.blt (L (21 * i + 5 + w) >>> 5) 4060,
          bAnd(Nat.beq (apP (TR (roff 4060 48720 (LR 0) + i)) (L (21 * i + 5 + w) >>> 5))
            (apP (R (21 + w)) (apP (TR (roff 4060 48720 (LR 0) + i)) 0)),
          notIn (orbM LR TR (R (12 + fld(L (21 * i + 5), 1, 15)))) (L (21 * i + 5 + w) >>> 5)))))
        = true := hB
    have h2 : bIf(Nat.beq (L (21 * i + 5)) 1, true,
        Nat.blt (fld(L (21 * i + 5), 1, 15)) (nIf(Nat.blt 5 5, rkX 5, 4))) = true :=
      RuBase.allN_iff.1 hk 5 (by omega)
    rw [hb] at hB' h2
    have hk' : fld(L (21 * i + 5), 1, 15) < 4 := Nat.blt_eq.mp h2
    refine ⟨_, hk', fun w hw => ?_⟩
    have h3 := RuBase.allN_iff.1 hB' w hw
    simp only [RuBase.bAnd_eq', Bool.and_eq_true] at h3
    exact ⟨_, Nat.blt_eq.mp h3.1, Nat.eq_of_beq_eq_true h3.2.1, h3.2.2⟩

theorem alChk_sound {LR L AL : Nat → Nat} {X n : Nat} (h : alChk LR L AL X n = true) :
    ∀ i < rcnt (LR 0), L (21 * i + X) = 1 → ∃ a < n, AL a = i := by
  unfold alChk at h
  simp only [sB, RuBase.bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨hA, hB⟩ := h
  have hA' : ∀ a < n, AL a < rcnt (LR 0) ∧ L (21 * AL a + X) = 1 ∧
      (a + 1 < n → AL a < AL (a + 1)) := by
    intro a ha
    have h1 := RuBase.allN_iff.1 hA a ha
    simp only [Bool.and_eq_true] at h1
    refine ⟨Nat.blt_eq.mp h1.1, Nat.eq_of_beq_eq_true h1.2.1, fun hlt => ?_⟩
    have h3 : bIf(Nat.blt (a + 1) n, Nat.blt (AL a) (AL (a + 1)), true) = true := h1.2.2
    rw [Nat.blt_eq.mpr hlt] at h3
    exact Nat.blt_eq.mp h3
  have hcnt : ((List.range (rcnt (LR 0))).filter (fun i => Nat.beq (L (21 * i + X)) 1)).length =
      n := by
    rw [← foldr_count, ← Raw.Orb.foldN_eq]
    exact Nat.eq_of_beq_eq_true hB
  have mono : ∀ a k, a + k + 1 < n → AL a < AL (a + k + 1) := by
    intro a k
    induction k with
    | zero => exact fun hl => (hA' a (by omega)).2.2 hl
    | succ k ih =>
      exact fun hl => (ih (by omega)).trans ((hA' (a + k + 1) (by omega)).2.2 (by omega))
  have inj : ∀ a < n, ∀ b < n, AL a = AL b → a = b := by
    intro a ha b hb e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := mono a (b - a - 1) (by omega)
      have e1 : a + (b - a - 1) + 1 = b := by omega
      rw [e1, e] at h1
      exact lt_irrefl _ h1
    · have h1 := mono b (a - b - 1) (by omega)
      have e1 : b + (a - b - 1) + 1 = a := by omega
      rw [e1, e] at h1
      exact lt_irrefl _ h1
  have hnd : ((List.range n).map AL).Nodup :=
    List.Nodup.map_on (fun a ha b hb e => inj a (List.mem_range.mp ha) b (List.mem_range.mp hb) e)
      List.nodup_range
  have hsub : (List.range n).map AL ⊆
      (List.range (rcnt (LR 0))).filter (fun i => Nat.beq (L (21 * i + X)) 1) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    have h1 := hA' a (List.mem_range.mp ha)
    exact List.mem_filter.mpr ⟨List.mem_range.mpr h1.1, Nat.beq_eq.mpr h1.2.1⟩
  have hperm := (List.subperm_of_subset hnd hsub).perm_of_length_le
    (by rw [hcnt, List.length_map, List.length_range])
  intro i hi hL
  have hmem : i ∈ (List.range (rcnt (LR 0))).filter (fun i => Nat.beq (L (21 * i + X)) 1) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, Nat.beq_eq.mpr hL⟩
  obtain ⟨a, ha, e⟩ := List.mem_map.mp (hperm.mem_iff.mpr hmem)
  exact ⟨a, List.mem_range.mp ha, e⟩

theorem elChk_sound {LR TR R Q AL EL : Nat → Nat} {X lo cnt : Nat}
    (h : elChk LR TR R Q AL EL X lo cnt = true) {a : Nat} (ha1 : lo ≤ a) (ha2 : a < lo + cnt)
    {j : Nat} (hj : j < rcnt (LR 1) * rcnt (LR 2)) :
    elOne [TR (roff 4060 48720 (LR 0) + AL a), TR (roff 4060 48720 (LR 1) + j / rcnt (LR 2)),
      TR (roff 4060 48720 (LR 2) + j % rcnt (LR 2))] R Q X
      (EL (rcnt (LR 1) * rcnt (LR 2) * a + j)) = true := by
  unfold elChk at h
  simp only [sB, RuBase.bAnd_eq'] at h
  obtain ⟨d, rfl⟩ : ∃ d, a = lo + d := ⟨a - lo, by omega⟩
  have h1 := RuBase.allN_iff.1 h d (by omega)
  simp only [Bool.and_eq_true] at h1
  exact RuBase.allN_iff.1 h1.2 j hj

theorem elOne_sound0 {ys : List Nat} {R Q : Nat → Nat} {rec : Nat} (h : elOne ys R Q 0 rec = true) :
    NcB (yAp ys) R 0 3 ∨ OrbC (yAp ys) (Q 10) (Q 11) 3 Q 0 := by
  unfold elOne at h
  simp only [sB] at h
  cases h0 : Nat.beq (Nat.land rec (nat_lit 3)) (nat_lit 0)
  · rw [h0] at h
    cases h1 : Nat.beq (Nat.land rec (nat_lit 3)) (nat_lit 1)
    · rw [h1] at h
      exact absurd h Bool.false_ne_true
    · rw [h1] at h
      have h' : orbOK ys (Q 10) (Q 11) 3 Q 0 (fld(rec, 2, 3)) (rec >>> 4) = true := h
      exact Or.inr (orbOK_sound h')
  · rw [h0] at h
    exact Or.inl (ncB_of (ys := ys) (R := R) (o := bX 0) (r := rkX 0) (k := fld(rec, 2, 15))
      (p := fld(rec, 6, 4095)) h)

theorem elOne_sound1 {ys : List Nat} {R Q : Nat → Nat} {rec : Nat} (h : elOne ys R Q 1 rec = true) :
    NcB (yAp ys) R 3 6 ∨ ∃ m < 64, ∀ b < 4, yAp ys b = mAp R 3 6 m b := by
  unfold elOne at h
  simp only [sB] at h
  cases h0 : Nat.beq (Nat.land rec (nat_lit 3)) (nat_lit 0)
  · rw [h0] at h
    cases h1 : Nat.beq (Nat.land rec (nat_lit 3)) (nat_lit 1)
    · rw [h1] at h
      exact absurd h Bool.false_ne_true
    · rw [h1] at h
      have h' : spB ys R 3 6 (rec >>> 2) = true := h
      obtain ⟨hm, hb⟩ := spB_sound h'
      exact Or.inr ⟨_, hm, hb⟩
  · rw [h0] at h
    exact Or.inl (ncB_of (ys := ys) (R := R) (o := bX 1) (r := rkX 1) (k := fld(rec, 2, 15))
      (p := fld(rec, 6, 4095)) h)

theorem elOne_sound2 {ys : List Nat} {R Q : Nat → Nat} {rec : Nat} (h : elOne ys R Q 2 rec = true) :
    NcB (yAp ys) R 9 3 ∨ ∃ m < 64, ∀ b < 4, yAp ys b = mAp R 3 6 m b := by
  unfold elOne at h
  simp only [sB] at h
  cases h0 : Nat.beq (Nat.land rec (nat_lit 3)) (nat_lit 0)
  · rw [h0] at h
    cases h1 : Nat.beq (Nat.land rec (nat_lit 3)) (nat_lit 1)
    · rw [h1] at h
      exact absurd h Bool.false_ne_true
    · rw [h1] at h
      have h' : spB ys R 3 6 (rec >>> 2) = true := h
      obtain ⟨hm, hb⟩ := spB_sound h'
      exact Or.inr ⟨_, hm, hb⟩
  · rw [h0] at h
    exact Or.inl (ncB_of (ys := ys) (R := R) (o := bX 2) (r := rkX 2) (k := fld(rec, 2, 15))
      (p := fld(rec, 6, 4095)) h)

theorem elOne_sound3 {ys : List Nat} {R Q : Nat → Nat} {rec : Nat} (h : elOne ys R Q 3 rec = true) :
    NcB (yAp ys) R 12 4 ∨
      (TwoC ys 7 ∧ G16C (yAp ys) R (Q 16) (Q 17) ∧ OrbC (yAp ys) (Q 12) (Q 13) 2 Q 5) := by
  unfold elOne at h
  simp only [sB] at h
  cases h0 : Nat.beq (Nat.land rec (nat_lit 3)) (nat_lit 0)
  · rw [h0] at h
    cases h1 : Nat.beq (Nat.land rec (nat_lit 3)) (nat_lit 1)
    · rw [h1] at h
      exact absurd h Bool.false_ne_true
    · rw [h1] at h
      have h' : bAnd(allN 4 (fun b => twoB ys (fld(rec, Nat.add 2 (Nat.mul 3 b), 7)) b),
          bAnd(g16B ys R (Q 16) (Q 17),
            orbOK ys (Q 12) (Q 13) 2 Q 5 (fld(rec, 14, 3)) (rec >>> 16))) = true := h
      simp only [RuBase.bAnd_eq', Bool.and_eq_true] at h'
      exact Or.inr ⟨twoC_of h'.1, g16C_of h'.2.1, orbOK_sound h'.2.2⟩
  · rw [h0] at h
    exact Or.inl (ncB_of (ys := ys) (R := R) (o := bX 3) (r := rkX 3) (k := fld(rec, 2, 15))
      (p := fld(rec, 6, 4095)) h)

theorem elOne_sound4 {ys : List Nat} {R Q : Nat → Nat} {rec : Nat} (h : elOne ys R Q 4 rec = true) :
    NcB (yAp ys) R 16 5 ∨ (TwoC ys 7 ∧ OrbC (yAp ys) (Q 14) (Q 15) 2 R 16) := by
  unfold elOne at h
  simp only [sB] at h
  cases h0 : Nat.beq (Nat.land rec (nat_lit 3)) (nat_lit 0)
  · rw [h0] at h
    cases h1 : Nat.beq (Nat.land rec (nat_lit 3)) (nat_lit 1)
    · rw [h1] at h
      exact absurd h Bool.false_ne_true
    · rw [h1] at h
      have h' : bAnd(allN 4 (fun b => twoB ys (fld(rec, Nat.add 2 (Nat.mul 3 b), 7)) b),
          orbOK ys (Q 14) (Q 15) 2 R 16 (fld(rec, 14, 3)) (rec >>> 16)) = true := h
      simp only [RuBase.bAnd_eq', Bool.and_eq_true] at h'
      exact Or.inr ⟨twoC_of h'.1, orbOK_sound h'.2⟩
  · rw [h0] at h
    exact Or.inl (ncB_of (ys := ys) (R := R) (o := bX 4) (r := rkX 4) (k := fld(rec, 2, 15))
      (p := fld(rec, 6, 4095)) h)

theorem elOne_sound5 {ys : List Nat} {R Q : Nat → Nat} {rec : Nat} (h : elOne ys R Q 5 rec = true) :
    (∃ k < 4, ∃ p < 4060, ∀ w < 16, apP (R (21 + w)) (yAp ys p) ≠ yAp ys (apP (R (12 + k)) p)) ∨
      TwoC ys 10 := by
  unfold elOne at h
  simp only [sB] at h
  cases h0 : Nat.beq (Nat.land rec (nat_lit 3)) (nat_lit 0)
  · rw [h0] at h
    cases h1 : Nat.beq (Nat.land rec (nat_lit 3)) (nat_lit 1)
    · rw [h1] at h
      exact absurd h Bool.false_ne_true
    · rw [h1] at h
      have h' : allN 4 (fun b => bAnd(Nat.ble (fld(rec, Nat.add 2 (Nat.mul 4 b), 15)) 10,
          twoB ys (fld(rec, Nat.add 2 (Nat.mul 4 b), 15)) b)) = true := h
      refine Or.inr fun b hb => ?_
      have hb' := RuBase.allN_iff.1 h' b hb
      simp only [RuBase.bAnd_eq', Bool.and_eq_true] at hb'
      exact ⟨_, Nat.le_of_ble_eq_true hb'.1, twoB_sound hb'.2⟩
  · rw [h0] at h
    have h' : bAnd(Nat.blt (fld(rec, 6, 4095)) 4060, bAnd(Nat.blt (fld(rec, 2, 15)) 4,
        allN 16 (fun w => bIf(Nat.beq (apP (R (Nat.add 21 w)) (yAp ys (fld(rec, 6, 4095))))
          (yAp ys (apP (R (Nat.add 12 (fld(rec, 2, 15)))) (fld(rec, 6, 4095)))), false, true))))
        = true := h
    simp only [RuBase.bAnd_eq', Bool.and_eq_true] at h'
    exact Or.inl ⟨_, Nat.blt_eq.mp h'.2.1, _, Nat.blt_eq.mp h'.1,
      fun w hw => Nat.ne_of_beq_eq_false (bIf_ft (RuBase.allN_iff.1 h'.2.2 w hw))⟩

theorem fixL_sound {LR TR : Nat → Nat} {l x : Nat} (h : fixL LR TR l x = true) {k : Nat}
    (hk : k < rcnt (LR l)) : apP (TR (roff 4060 48720 (LR l) + k)) x = x :=
  Nat.eq_of_beq_eq_true (RuBase.allN_iff.1 h k hk)

theorem ptR_xAp {x : Nat} {g : Equiv.Perm (Fin 4060)} (hx : PtR (apP x) g) :
    ∀ j, PtR (xAp x j) (g ^ j)
  | 0 => fun y => by rw [pow_zero]; rfl
  | j + 1 => fun y => by
    change strictN (xAp x j y) (fun v => apP x v) = _
    rw [sN, ptR_xAp hx j y, hx _, pow_succ', Equiv.Perm.mul_apply]

theorem ptR_yPow {ys : List Nat} {g : Equiv.Perm (Fin 4060)} (hf : PtR (yAp ys) g) :
    ∀ j, PtR (yPow ys j) (g ^ j)
  | 0 => fun y => by rw [pow_zero]; rfl
  | j + 1 => fun y => by
    change strictN (yPow ys j y) (fun v => yAp ys v) = _
    rw [sN, ptR_yPow hf j y, hf _, pow_succ', Equiv.Perm.mul_apply]

theorem prune {t s v : Equiv.Perm (Fin 4060)} {o : Fin 4060} (hs : s o = o)
    (h : t * s * v = v * (t * s)) : t⁻¹ (v (t o)) = s (v o) := by
  have e := congrArg (fun p : Equiv.Perm (Fin 4060) => p o) h
  simp only [Equiv.Perm.mul_apply, hs] at e
  rw [← e]
  simp

theorem prune_norm {t s v w : Equiv.Perm (Fin 4060)} {o : Fin 4060} (hs : s o = o)
    (h : t * s * v * (t * s)⁻¹ = w) : t⁻¹ (w (t o)) = s (v o) := by
  have hs' : s⁻¹ o = o := by rw [Equiv.Perm.inv_eq_iff_eq, hs]
  rw [← h]
  simp [Equiv.Perm.mul_apply, mul_inv_rev, hs']

end CFSG.KC.Misc.RuBigZ

end
