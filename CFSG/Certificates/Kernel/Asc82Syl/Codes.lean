module

public import Certificates.Data.Kernel.Asc82Syl.Defs
public import CFSG.Certificates.Kernel.Spor.Mat3Sound

public section

namespace CFSG.KS.Asc82Syl

open CFSG.KD.Asc82Syl CFSG.KS.Mat3 CFSG.KC.Ord CFSG.KC.Loop
open scoped Matrix

abbrev mat (X : Nat) : Matrix (Fin 6) (Fin 6) (ZMod 3) := mat3 6 36 X

theorem bAnd_a82 {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem recAnd_a82 (f : Nat → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true
      (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i)) n = true →
    ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := bAnd_a82 h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · exact recAnd_a82 f n h2 i hlt
    · exact h1

theorem allBelow_a82 {m hi : Nat} {f : Nat → Bool} (h : allBelow m hi f = true) (hm : m ≤ 64 * hi)
    (i : Nat) (him : i < m) : f i = true := by
  have h1 := recAnd_a82 (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h 6) l), ih2)) 64) hi h
    (i / 64) (by omega)
  have h2 := recAnd_a82 (fun l => (fun i => bIf(Nat.blt i m, f i, true))
    (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64 h1 (i % 64) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq, (rfl : (2 : Nat) ^ 6 = 64)]
    omega
  have hb : Nat.blt i m = true := Nat.blt_eq.mpr him
  dsimp only at h2
  rw [e, hb] at h2
  exact h2

theorem LO_eq : LO = 2 ^ 36 - 1 := rfl

theorem pw_eq (j : Nat) : pw j = 2 ^ j := by
  change 1 <<< j = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem MUL_sound {A B : Nat} (hc : constsK = true) (hA : Canon3 36 A) (hB : Canon3 36 B) :
    Canon3 36 (MUL A B) ∧ mat (MUL A B) = mat A * mat B :=
  mul3s_sound hc hA hB

theorem ONE_sound (hc : constsK = true) : Canon3 36 ONE ∧ mat ONE = 1 := one3_sound hc

theorem valid_iff {X : Nat} : valid3 36 LO X = true ↔ Canon3 36 X := valid3_iff LO_eq

theorem negK_testBit (X t : Nat) : (negK X).testBit t =
    (X.testBit (36 + t) || (decide (36 ≤ t) && (decide (t - 36 < 36) && X.testBit (t - 36)))) := by
  unfold negK
  rw [lor_eq3, shr_eq3, shl_eq3, land_eq3, Nat.testBit_or, Nat.testBit_shiftRight,
    Nat.testBit_shiftLeft, LO_eq, lo_bit]

theorem high_false {X t : Nat} (hX : Canon3 36 X) (ht : 72 ≤ t) : X.testBit t = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX.1 (Nat.pow_le_pow_right (by omega) ht))

theorem bv_swap : ∀ b1 b2 : Bool, (b1 && b2) = false → bv b2 b1 = -bv b1 b2 := by decide

theorem negK_bits {X : Nat} (hX : Canon3 36 X) :
    (∀ t < 36, (negK X).testBit t = X.testBit (36 + t)) ∧
    (∀ t < 36, (negK X).testBit (36 + t) = X.testBit t) ∧
    (∀ t, 72 ≤ t → (negK X).testBit t = false) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · rw [negK_testBit]
    simp [show ¬ 36 ≤ t by omega]
  · rw [negK_testBit, high_false hX (t := 36 + (36 + t)) (by omega)]
    simp [ht]
  · rw [negK_testBit, high_false hX (t := 36 + t) (by omega)]
    simp [show ¬ t - 36 < 36 by omega]

theorem negK_sound {X : Nat} (hX : Canon3 36 X) :
    Canon3 36 (negK X) ∧ mat (negK X) = -mat X ∧ negK (negK X) = X := by
  have hdj : ∀ t, (X.testBit t && X.testBit (36 + t)) = false := by
    intro t
    cases h : X.testBit t
    · rfl
    · rw [hX.2 t h]
      rfl
  obtain ⟨hlow, hmid, hhi⟩ := negK_bits hX
  have hc : Canon3 36 (negK X) := by
    refine ⟨Nat.lt_pow_two_of_testBit _ (fun t ht => hhi t (by omega)), fun t ht => ?_⟩
    by_cases h1 : t < 36
    · rw [hmid t h1]
      rw [hlow t h1] at ht
      have := hdj t
      rw [ht] at this
      simpa using this
    · exact hhi _ (by omega)
  refine ⟨hc, ?_, ?_⟩
  · funext i j
    have ht : 6 * i.val + j.val < 36 := idx_lt3 i.isLt j.isLt
    change bv _ _ = -bv _ _
    rw [hlow _ ht, hmid _ ht]
    exact bv_swap _ _ (hdj _)
  · obtain ⟨hlow', hmid', hhi'⟩ := negK_bits hc
    apply Nat.eq_of_testBit_eq
    intro t
    by_cases h1 : t < 36
    · rw [hlow' t h1, hmid t h1]
    · by_cases h2 : t < 72
      · have e : t = 36 + (t - 36) := by omega
        rw [e, hmid' _ (by omega), hlow _ (by omega)]
      · rw [hhi' t (by omega), high_false hX (by omega)]

theorem canonK_cases (X : Nat) : canonK X = X ∨ canonK X = negK X := by
  unfold canonK
  cases Nat.blt (negK X) X
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem eqC_sound {X Y : Nat} (hX : Canon3 36 X) (hY : Canon3 36 Y) (h : eqC X Y = true) :
    mat X = mat Y ∨ mat X = -mat Y := by
  have e : canonK X = canonK Y := Nat.eq_of_beq_eq_true h
  obtain ⟨-, hnX, -⟩ := negK_sound hX
  obtain ⟨-, hnY, hnnY⟩ := negK_sound hY
  rcases canonK_cases X with hx | hx <;> rcases canonK_cases Y with hy | hy <;> rw [hx, hy] at e
  · exact Or.inl (by rw [e])
  · exact Or.inr (by rw [e, hnY])
  · refine Or.inr ?_
    rw [← neg_neg (mat X), ← hnX, e]
  · left
    rw [← neg_neg (mat X), ← hnX, e, hnY, neg_neg]

theorem canonK_eq {X Y : Nat} (hX : Canon3 36 X) (hY : Canon3 36 Y)
    (h : mat X = mat Y ∨ mat X = -mat Y) : canonK X = canonK Y := by
  obtain ⟨hcY, hnY, hnnY⟩ := negK_sound hY
  rcases h with h | h
  · rw [mat3_inj (d := 6) (N := 36) rfl hX hY h]
  · have e : X = negK Y := mat3_inj (d := 6) (N := 36) rfl hX hcY (by
      change mat X = mat (negK Y)
      rw [h, hnY])
    subst e
    unfold canonK
    rw [hnnY]
    cases h1 : Nat.blt Y (negK Y) <;> cases h2 : Nat.blt (negK Y) Y
    · have a1 : ¬ Y < negK Y := fun hlt => by rw [Nat.blt_eq.mpr hlt] at h1; cases h1
      have a2 : ¬ negK Y < Y := fun hlt => by rw [Nat.blt_eq.mpr hlt] at h2; cases h2
      have : Y = negK Y := by omega
      change negK Y = Y
      rw [← this]
    · rfl
    · rfl
    · have := Nat.blt_eq.mp h1
      have := Nat.blt_eq.mp h2
      omega

theorem fld1_eq (X s : Nat) : Nat.land (Nat.shiftRight X s) 1 = (X.testBit s).toNat := by
  rw [land_eq3, shr_eq3, Nat.and_one_is_mod, Nat.toNat_testBit, Nat.shiftRight_eq_div_pow]

theorem bit_of_fld {X Y s t : Nat}
    (h : Nat.beq (Nat.land (Nat.shiftRight X s) 1) (Nat.land (Nat.shiftRight Y t) 1) = true) :
    X.testBit s = Y.testBit t := by
  have e := Nat.eq_of_beq_eq_true h
  rw [fld1_eq, fld1_eq] at e
  cases h1 : X.testBit s <;> cases h2 : Y.testBit t <;> rw [h1, h2] at e <;> first | rfl | cases e

theorem transK_at {A T : Nat} (h : transK A T = true) (t : Nat) (ht : t < 36) :
    T.testBit t = A.testBit (6 * (t % 6) + t / 6) ∧
      T.testBit (36 + t) = A.testBit (36 + (6 * (t % 6) + t / 6)) := by
  have hb := allBelow_a82 h (by decide) t ht
  obtain ⟨hb1, hb2⟩ := bAnd_a82 hb
  exact ⟨bit_of_fld hb1, bit_of_fld hb2⟩

theorem transK_sound {A T : Nat} (h : transK A T = true) : mat T = (mat A)ᵀ := by
  funext i j
  have ht : 6 * i.val + j.val < 36 := idx_lt3 i.isLt j.isLt
  obtain ⟨hb1, hb2⟩ := transK_at h _ ht
  have e1 : (6 * i.val + j.val) % 6 = j.val := (dm_eq3 j.isLt).2
  have e2 : (6 * i.val + j.val) / 6 = i.val := (dm_eq3 j.isLt).1
  rw [e1, e2] at hb1 hb2
  change bv _ _ = bv _ _
  rw [hb1, hb2]

theorem genK_sound {G : List (Nat × Nat)} {D : Nat} (hc : constsK = true) (hD : Canon3 36 D)
    (h : genK G D = true) : ∀ g ∈ G, Canon3 36 g.1 ∧
      ((mat g.1)ᵀ * mat D * mat g.1 = mat D ∨ (mat g.1)ᵀ * mat D * mat g.1 = -mat D) := by
  induction G with
  | nil => intro g hg; exact absurd hg List.not_mem_nil
  | cons g G ih =>
    obtain ⟨hv, h⟩ := bAnd_a82 h
    obtain ⟨hv2, h⟩ := bAnd_a82 h
    obtain ⟨htr, h⟩ := bAnd_a82 h
    obtain ⟨hs, h⟩ := bAnd_a82 h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · have hA : Canon3 36 x.1 := valid_iff.1 hv
      have hT : Canon3 36 x.2 := valid_iff.1 hv2
      have hTr := transK_sound htr
      obtain ⟨hTD, hTDm⟩ := MUL_sound hc hT hD
      obtain ⟨-, hP⟩ := MUL_sound hc hTD hA
      have hval : mat (MUL (MUL x.2 D) x.1) = (mat x.1)ᵀ * mat D * mat x.1 := by
        rw [hP, hTDm, hTr]
      refine ⟨hA, ?_⟩
      dsimp only at hs
      cases hb : Nat.beq (MUL (MUL x.2 D) x.1) D
      · rw [hb] at hs
        have e := Nat.eq_of_beq_eq_true hs
        right
        rw [← hval, e, (negK_sound hD).2.1]
      · left
        rw [← hval, Nat.eq_of_beq_eq_true hb]
    · exact ih h x hx

noncomputable def Wm (A : Nat → Matrix (Fin 6) (Fin 6) (ZMod 3)) : Nat → Nat → Matrix (Fin 6) (Fin 6) (ZMod 3)
  | 0, _ => 1
  | j + 1, e => Wm A j e * (if e.testBit j then A j else 1)

theorem Wm_zero (A : Nat → Matrix (Fin 6) (Fin 6) (ZMod 3)) (e : Nat) : Wm A 0 e = 1 := by
  simp only [Wm]

theorem Wm_succ (A : Nat → Matrix (Fin 6) (Fin 6) (ZMod 3)) (j e : Nat) :
    Wm A (j + 1) e = Wm A j e * (if e.testBit j then A j else 1) := by
  simp only [Wm]

theorem Wm_congr (A : Nat → Matrix (Fin 6) (Fin 6) (ZMod 3)) :
    ∀ j e e', (∀ i < j, e.testBit i = e'.testBit i) → Wm A j e = Wm A j e'
  | 0, _, _, _ => rfl
  | j + 1, e, e', h => by
    simp only [Wm]
    rw [Wm_congr A j e e' (fun i hi => h i (by omega)), h j (by omega)]

theorem enumL_sound {WP : Nat} : ∀ (L : List (Nat × Nat)) (j : Nat), j + L.length ≤ 10 →
    enumL WP L j = true → ∀ i < L.length, ∀ e < 2 ^ (j + i),
      wAt WP (e + 2 ^ (j + i)) = MUL (wAt WP e) (L.getD i (0, 0)).1
  | [], _, _, _, i, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | g :: L, j, hm, h, i, hi, e, he => by
    obtain ⟨h1, h2⟩ := bAnd_a82 h
    rcases i with _ | i
    · have hj : j ≤ 10 := by simp at hm; omega
      have hp : pw j ≤ 64 * 16 := by
        rw [pw_eq]
        calc 2 ^ j ≤ 2 ^ 10 := Nat.pow_le_pow_right (by omega) hj
          _ = 64 * 16 := rfl
      have := allBelow_a82 h1 hp e (by rw [pw_eq]; simpa using he)
      rw [pw_eq] at this
      exact Nat.eq_of_beq_eq_true this
    · have e1 : j + (i + 1) = j + 1 + i := by omega
      rw [e1] at he ⊢
      exact enumL_sound L (j + 1) (by simp at hm; omega) h2 i (by simpa using hi) e he

theorem enumK_sound {WP : Nat} {G : List (Nat × Nat)} (hc : constsK = true)
    (hG : ∀ g ∈ G, Canon3 36 g.1) (hm : G.length ≤ 10) (h : enumK WP G = true) :
    ∀ j ≤ G.length, ∀ e < 2 ^ j, Canon3 36 (wAt WP e) ∧
      mat (wAt WP e) = Wm (fun i => mat (G.getD i (0, 0)).1) j e := by
  obtain ⟨h0, h1⟩ := bAnd_a82 h
  have hstep := enumL_sound G 0 (by omega) h1
  intro j
  induction j with
  | zero =>
    intro _ e he
    have e0 : e = 0 := by simpa using he
    subst e0
    rw [Nat.eq_of_beq_eq_true h0]
    exact ⟨(ONE_sound hc).1, (ONE_sound hc).2⟩
  | succ j ih =>
    intro hj e he
    by_cases hlt : e < 2 ^ j
    · obtain ⟨hcan, hmat⟩ := ih (by omega) e hlt
      refine ⟨hcan, ?_⟩
      rw [hmat]
      simp only [Wm, Nat.testBit_lt_two_pow hlt]
      simp
    · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 ^ j := ⟨e - 2 ^ j, by omega⟩
      have he' : e' < 2 ^ j := by rw [Nat.pow_succ] at he; omega
      obtain ⟨hcan, hmat⟩ := ih (by omega) e' he'
      have hw := hstep j (by omega) e' (by simpa using he')
      rw [Nat.zero_add] at hw
      have hgj : G.getD j (0, 0) ∈ G := by
        have hjl : j < G.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
        exact List.getElem_mem hjl
      obtain ⟨hc2, hm2⟩ := MUL_sound hc hcan (hG _ hgj)
      rw [hw]
      refine ⟨hc2, ?_⟩
      have hb : (e' + 2 ^ j).testBit j = true := by
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow he']
        rfl
      have hcg : Wm (fun i => mat (G.getD i (0, 0)).1) j (e' + 2 ^ j) =
          Wm (fun i => mat (G.getD i (0, 0)).1) j e' :=
        Wm_congr _ j _ _ (fun i hi => by
          rw [Nat.add_comm]
          exact Nat.testBit_two_pow_add_gt hi e')
      rw [hm2, hmat, Wm.eq_2, hb, if_pos rfl, hcg]

end CFSG.KS.Asc82Syl

end
