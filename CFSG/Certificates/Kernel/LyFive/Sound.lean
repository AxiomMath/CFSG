
module

public import Certificates.Data.Kernel.LyFive
public import CFSG.Certificates.Kernel.LyOmega.Sound

public section

namespace CFSG.KS.LyFive

open CFSG.KC.LyFive CFSG.KC.LyOm CFSG.KC.Loop CFSG.KC.LL CFSG.KC.Ord CFSG.KS.LyOm
  CFSG.RankThree.Native

theorem strictN_eq (v : ℕ) (k : ℕ → ℕ) : strictN v k = k v := by cases v <;> rfl

theorem strictL_eq (v : ℕ) (k : ℕ → List ℕ) : strictL v k = k v := by cases v <;> rfl

theorem letB_eq (v : ℕ) (k : ℕ → Bool) : letB v k = k v := by cases v <;> rfl

theorem bAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

theorem bIf_eq (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem nIf_eq (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem beq_eq {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem fldW_lt (r o w : ℕ) : fldW r o w < 2 ^ w := by
  unfold fldW
  change (r >>> o) &&& ((1 <<< w) - 1) < 2 ^ w
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

@[expose] def InsLt : FiveIns → Prop
  | .mu i j k => i < 65 ∧ j < 65 ∧ k < 65
  | .pwr _ i k => i < 65 ∧ k < 65

@[expose] def insLtB : FiveIns → Bool
  | .mu i j k => decide (i < 65) && decide (j < 65) && decide (k < 65)
  | .pwr _ i k => decide (i < 65) && decide (k < 65)

theorem insLt_of {ins : FiveIns} (h : insLtB ins = true) : InsLt ins := by
  cases ins <;> simp_all [insLtB, InsLt]

@[expose] def RegRep (R : List ℕ) (Rm : ℕ → Matrix (Fin 111) (Fin 111) (ZMod 5)) : Prop :=
  R.length = 65 ∧ ∀ k < 65, LCanon 12 111 111 (R.getD k 0) ∧ bigM (R.getD k 0) = Rm k

theorem getD_set_eq (R : List ℕ) (k j v : ℕ) (hk : k < R.length) :
    (R.set k v).getD j 0 = if j = k then v else R.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : k = j
  · subst h
    simp [hk]
  · simp [h, Ne.symm h]

section Products

variable {C : BConsts} (hC : bConstsOK C = true)
  (hOne : LCanon 12 111 111 C.ONEF ∧ bigM C.ONEF = 1)
include hC

theorem wordR_sound {G : ℕ → ℕ} {M : ℕ → Matrix (Fin 111) (Fin 111) (ZMod 5)} :
    ∀ (w : List ℕ) (X : ℕ), LCanon 12 111 111 X →
      (∀ l ∈ w, LCanon 12 111 111 (G l) ∧ bigM (G l) = M l) →
      LCanon 12 111 111 (wordR (fMul C) G X w) ∧ bigM (wordR (fMul C) G X w) = bigM X * (w.map M).prod
  | [], X, hX, _ => ⟨hX, by simp [wordR]⟩
  | l :: w, X, hX, hG => by
    have e : wordR (fMul C) G X (l :: w) = wordR (fMul C) G (fMul C X (G l)) w :=
      strictN_eq (fMul C X (G l)) (fun v => wordR (fMul C) G v w)
    obtain ⟨cl, el⟩ := hG l List.mem_cons_self
    have m := fMul_sound hC hX cl
    obtain ⟨c, e2⟩ := wordR_sound w (fMul C X (G l)) m.1 (fun l' hl' => hG l' (List.mem_cons_of_mem _ hl'))
    rw [e]
    refine ⟨c, ?_⟩
    rw [e2, m.2, el, List.map_cons, List.prod_cons, Matrix.mul_assoc]

include hOne in
theorem wordF_sound {G : ℕ → ℕ} {M : ℕ → Matrix (Fin 111) (Fin 111) (ZMod 5)} (w : List ℕ)
    (hG : ∀ l ∈ w, LCanon 12 111 111 (G l) ∧ bigM (G l) = M l) :
    LCanon 12 111 111 (wordF C G w) ∧ bigM (wordF C G w) = (w.map M).prod := by
  cases w with
  | nil =>
    change LCanon 12 111 111 C.ONEF ∧ bigM C.ONEF = _
    exact ⟨hOne.1, by rw [hOne.2]; rfl⟩
  | cons l w =>
    obtain ⟨cl, el⟩ := hG l List.mem_cons_self
    have h := wordR_sound hC w (G l) cl (fun l' hl' => hG l' (List.mem_cons_of_mem _ hl'))
    refine ⟨h.1, ?_⟩
    change bigM (wordR (fMul C) G (G l) w) = _
    rw [h.2, el, List.map_cons, List.prod_cons]

include hOne in
theorem powF_sound {X : ℕ} (hX : LCanon 12 111 111 X) :
    ∀ e, LCanon 12 111 111 (powF C X e) ∧ bigM (powF C X e) = bigM X ^ e
  | 0 => ⟨hOne.1, by rw [pow_zero]; exact hOne.2⟩
  | e + 1 => by
    obtain ⟨c, h⟩ := powF_sound hX e
    have ee : powF C X (e + 1) = fMul C (powF C X e) X :=
      strictN_eq (powF C X e) (fun a => fMul C a X)
    have m := fMul_sound hC c hX
    rw [ee]
    exact ⟨m.1, by rw [m.2, h, pow_succ]⟩

theorem pow5F_sound {X : ℕ} (hX : LCanon 12 111 111 X) :
    LCanon 12 111 111 (pow5F C X) ∧ bigM (pow5F C X) = bigM X ^ 5 := by
  have m2 := fMul_sound hC hX hX
  have m4 := fMul_sound hC m2.1 m2.1
  have m5 := fMul_sound hC m4.1 hX
  have e : pow5F C X = fMul C (fMul C (fMul C X X) (fMul C X X)) X := by
    unfold pow5F
    rw [strictN_eq, strictN_eq]
  rw [e]
  refine ⟨m5.1, ?_⟩
  rw [m5.2, m4.2, m2.2]
  noncomm_ring

include hOne in
theorem slpStepF_sound {R : List ℕ} {Rm : ℕ → Matrix (Fin 111) (Fin 111) (ZMod 5)}
    (hR : RegRep R Rm) (ins : FiveIns) (hins : InsLt ins) :
    RegRep (slpStepF C R ins) (fiveSlpStep Rm ins) := by
  obtain ⟨hlen, hget⟩ := hR
  cases ins with
  | mu i j k =>
    obtain ⟨hi, hj, hk⟩ := hins
    have m := fMul_sound hC (hget i hi).1 (hget j hj).1
    change RegRep (strictL _ _) _
    rw [strictL_eq]
    refine ⟨by rw [List.length_set, hlen], fun t ht => ?_⟩
    rw [getD_set_eq R k t _ (by omega)]
    simp only [fiveSlpStep, Function.update_apply]
    split_ifs with h
    · rw [m.2, (hget i hi).2, (hget j hj).2]
      exact ⟨m.1, rfl⟩
    · exact hget t ht
  | pwr e i k =>
    obtain ⟨hi, hk⟩ := hins
    have m := powF_sound hC hOne (hget i hi).1 e
    change RegRep (strictL _ _) _
    rw [strictL_eq]
    refine ⟨by rw [List.length_set, hlen], fun t ht => ?_⟩
    rw [getD_set_eq R k t _ (by omega)]
    simp only [fiveSlpStep, Function.update_apply]
    split_ifs with h
    · rw [m.2, (hget i hi).2]
      exact ⟨m.1, rfl⟩
    · exact hget t ht

include hOne in
theorem slpF_sound : ∀ (prog : List FiveIns) {R : List ℕ}
    {Rm : ℕ → Matrix (Fin 111) (Fin 111) (ZMod 5)}, RegRep R Rm → (∀ ins ∈ prog, InsLt ins) →
    RegRep (slpF C R prog) (fiveSlpRun prog Rm)
  | [], _, _, hR, _ => hR
  | ins :: prog, R, Rm, hR, hp => by
    have h1 := slpStepF_sound hC hOne hR ins (hp ins List.mem_cons_self)
    exact slpF_sound prog h1 (fun i hi => hp i (List.mem_cons_of_mem _ hi))

end Products

theorem edgeF_sound {C : BConsts} {G : ℕ → ℕ} {cj : List ℕ} {l Mp Mo : ℕ}
    (h : edgeF C G cj l Mp Mo = true) :
    (l < 8 → fMul C (G (cj.getD l 0)) Mp = fMul C Mo (G (cj.getD l 0))) ∧
      (¬ l < 8 → powF C Mp (l - 6) = Mo) := by
  unfold edgeF at h
  rw [bIf_eq] at h
  by_cases hl : l < 8
  · have hb : Nat.blt l 8 = true := Nat.blt_eq.mpr hl
    rw [if_pos hb, letB_eq] at h
    exact ⟨fun _ => beq_eq h, fun h' => absurd hl h'⟩
  · have hb : ¬ Nat.blt l 8 = true := fun e => hl (Nat.blt_eq.mp e)
    rw [if_neg hb] at h
    exact ⟨fun h' => absurd h' hl, fun _ => beq_eq h⟩

@[expose] def TreeRec (C : BConsts) (G : ℕ → ℕ) (TB cj rt : List ℕ) (i : ℕ) : Prop :=
  recF TB i 0 14 < 15625 ∧ ((100 ≤ recF TB i 27 7 ∧ recF TB i 27 7 < 117 ∧
      recF TB i 0 14 = rt.getD (recF TB i 27 7 - 100) 0) ∨
    (recF TB i 27 7 < 100 ∧ recF TB i 14 13 < i ∧ recF TB i 27 7 < 11 ∧
      edgeF C G cj (recF TB i 27 7) (elF C G (recF TB (recF TB i 14 13) 0 14))
        (elF C G (recF TB i 0 14)) = true))

theorem treeGo_sound {C : BConsts} {G : ℕ → ℕ} {TB cj rt : List ℕ} {NT : ℕ} :
    ∀ (f i pp Mp : ℕ), (pp < 8192 → Mp = elF C G (recF TB pp 0 14)) →
      treeGo C G TB cj rt NT f i pp Mp = true →
      ∀ i', i ≤ i' → i' < i + f → i' < NT → TreeRec C G TB cj rt i'
  | 0, _, _, _, _, _, i', h1, h2, _ => absurd h2 (by omega)
  | f + 1, i, pp, Mp, hinv, h, i', h1, h2, h3 => by
    change Bool.rec (motive := fun _ => Bool) true (letB (recF TB i 27 7) fun l =>
      letB (recF TB i 0 14) fun o => Bool.rec (motive := fun _ => Bool) false
       (Bool.rec (motive := fun _ => Bool)
        (letB (recF TB i 14 13) fun p => Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool)
              (letB (elF C G (recF TB p 0 14)) fun Mq => Bool.rec (motive := fun _ => Bool) false
                (treeGo C G TB cj rt NT f (Nat.succ i) p Mq) (edgeF C G cj l Mq (elF C G o)))
              (Bool.rec (motive := fun _ => Bool) false (treeGo C G TB cj rt NT f (Nat.succ i) pp Mp)
                (edgeF C G cj l Mp (elF C G o)))
              (Nat.beq p pp)) (Nat.blt l 11)) (Nat.blt p i))
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false (treeGo C G TB cj rt NT f (Nat.succ i) pp Mp)
            (Nat.beq o (rt.getD (Nat.sub l 100) 0))) (Nat.blt l 117))
        (Nat.ble 100 l)) (Nat.blt o 15625)) (Nat.blt i NT) = true at h
    have hi : Nat.blt i NT = true := Nat.blt_eq.mpr (by omega)
    rw [hi, letB_eq, letB_eq] at h
    obtain ⟨ho, h⟩ := bAnd_true h
    have ho' : recF TB i 0 14 < 15625 := Nat.blt_eq.mp ho
    by_cases hr : 100 ≤ recF TB i 27 7
    · have hb : Nat.ble 100 (recF TB i 27 7) = true := Nat.ble_eq.mpr hr
      rw [hb] at h
      obtain ⟨h117, h⟩ := bAnd_true h
      obtain ⟨hrt, h⟩ := bAnd_true h
      rcases Nat.lt_or_ge i' (i + 1) with hlt | hge
      · have e : i' = i := by omega
        subst e
        exact ⟨ho', Or.inl ⟨hr, Nat.blt_eq.mp h117, beq_eq hrt⟩⟩
      · exact treeGo_sound f (i + 1) pp Mp hinv h i' hge (by omega) h3
    · have hb : Nat.ble 100 (recF TB i 27 7) = false :=
        Bool.eq_false_iff.mpr fun e => hr (Nat.ble_eq.mp e)
      rw [hb, letB_eq] at h
      obtain ⟨hpi, h⟩ := bAnd_true h
      obtain ⟨hl11, h⟩ := bAnd_true h
      have hl100 : recF TB i 27 7 < 100 := by omega
      have hp8 : recF TB i 14 13 < 8192 := fldW_lt _ _ _
      by_cases hpp : Nat.beq (recF TB i 14 13) pp = true
      · rw [hpp] at h
        obtain ⟨he, h⟩ := bAnd_true h
        have epp : recF TB i 14 13 = pp := beq_eq hpp
        rcases Nat.lt_or_ge i' (i + 1) with hlt | hge
        · have e : i' = i := by omega
          subst e
          have eM : Mp = elF C G (recF TB (recF TB i' 14 13) 0 14) := by
            rw [epp]
            exact hinv (epp ▸ hp8)
          refine ⟨ho', Or.inr ⟨hl100, Nat.blt_eq.mp hpi, Nat.blt_eq.mp hl11, ?_⟩⟩
          rw [← eM]
          first | exact he | skip
        · exact treeGo_sound f (i + 1) pp Mp hinv h i' hge (by omega) h3
      · have hpp' : Nat.beq (recF TB i 14 13) pp = false := Bool.eq_false_iff.mpr hpp
        rw [hpp', letB_eq] at h
        obtain ⟨he, h⟩ := bAnd_true h
        rcases Nat.lt_or_ge i' (i + 1) with hlt | hge
        · have e : i' = i := by omega
          subst e
          exact ⟨ho', Or.inr ⟨hl100, Nat.blt_eq.mp hpi, Nat.blt_eq.mp hl11, he⟩⟩
        · exact treeGo_sound f (i + 1) (recF TB i 14 13) (elF C G (recF TB (recF TB i 14 13) 0 14))
            (fun _ => rfl) h i' hge (by omega) h3

theorem treeBlk_sound {C : BConsts} {G : ℕ → ℕ} {TB cj rt : List ℕ} {NT k : ℕ}
    (h : treeBlk C G TB cj rt NT k = true) :
    ∀ i, 64 * k ≤ i → i < 64 * k + 64 → i < NT → TreeRec C G TB cj rt i :=
  treeGo_sound 64 (64 * k) 16383 0 (fun h => absurd h (by norm_num)) h

theorem recB_spec {g : ℕ → Bool} : ∀ n,
    Nat.rec (motive := fun _ => Bool) true
      (fun k ih => Bool.rec (motive := fun _ => Bool) false ih (g k)) n = true →
      ∀ k < n, g k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact recB_spec n h2 k hk
    · exact h1

theorem allBelow_spec {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true) :
    ∀ i < m, i < 64 * hi → f i = true := by
  intro i him hih
  have hq : i / 64 < hi := by omega
  have h1 := recB_spec hi h (i / 64) hq
  have h2 := recB_spec (g := fun l => Bool.rec (motive := fun _ => Bool) true
    (f (Nat.add (Nat.shiftLeft (i / 64) 6) l)) (Nat.blt (Nat.add (Nat.shiftLeft (i / 64) 6) l) m))
    64 h1 (i % 64) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  simp only [e, Nat.blt_eq.mpr him] at h2
  exact h2

theorem posOK_sound {TB PB : List ℕ} {NT : ℕ} (h : posOK TB PB NT = true) :
    ∀ n < 15625, (posF PB n = 16383 → n = 0 ∨ (3125 ≤ n ∧ posF PB (n - n % 5) = 16383)) ∧
      (posF PB n ≠ 16383 → posF PB n < NT ∧ recF TB (posF PB n) 0 14 = n) := by
  intro n hn
  have h1 := allBelow_spec h n hn (Nat.lt_of_lt_of_le hn (by norm_num))
  rw [letB_eq, bIf_eq] at h1
  by_cases hq : posF PB n = 16383
  · have hb : Nat.beq (posF PB n) 16383 = true := by rw [hq]; rfl
    rw [if_pos hb, bIf_eq] at h1
    refine ⟨fun _ => ?_, fun h' => absurd hq h'⟩
    by_cases h0 : n = 0
    · exact Or.inl h0
    · have hb0 : ¬ Nat.beq n 0 = true := fun e => h0 (beq_eq e)
      rw [if_neg hb0] at h1
      obtain ⟨a1, a2⟩ := bAnd_true h1
      exact Or.inr ⟨Nat.le_of_ble_eq_true a1, beq_eq a2⟩
  · have hb : ¬ Nat.beq (posF PB n) 16383 = true := fun e => hq (beq_eq e)
    rw [if_neg hb] at h1
    obtain ⟨a1, a2⟩ := bAnd_true h1
    exact ⟨fun h' => absurd h' hq, fun _ => ⟨Nat.blt_eq.mp a1, beq_eq a2⟩⟩

theorem baseBlk_sound {C : BConsts} {G : ℕ → ℕ} {PB : List ℕ} {c : ℕ} (h : baseBlk C G PB c = true) :
    ∀ t < 25, posF PB (3125 * (1 + c / 25) + 5 * (25 * (c % 25) + t)) = 16383 →
      pow5F C (elF C G (3125 * (1 + c / 25) + 5 * (25 * (c % 25) + t))) ≠ C.ONEF := by
  intro t ht hpos
  have h1 := recB_spec (g := fun t => baseF C G PB
    (Nat.add (Nat.mul 3125 (Nat.add 1 (Nat.div c 25))) (Nat.mul 5 (Nat.add (Nat.mul 25 (Nat.mod c 25)) t))))
    25 h t ht
  change baseF C G PB (3125 * (1 + c / 25) + 5 * (25 * (c % 25) + t)) = true at h1
  unfold baseF at h1
  rw [bIf_eq, if_pos (by rw [hpos]; rfl)] at h1
  intro e
  rw [e, Nat.beq_refl] at h1
  exact absurd h1 (by decide)

end CFSG.KS.LyFive

end
