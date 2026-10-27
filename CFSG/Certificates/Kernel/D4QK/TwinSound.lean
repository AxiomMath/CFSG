module

public import CFSG.Certificates.Kernel.S63K.EnumSound
public import Certificates.Data.Kernel.D4QK.Defs
public import CFSG.Quasithin.Background.Harris.R1.D4ModelCheck
public import CFSG.Monster.B.Co2.PermArr

public section

set_option exponentiation.threshold 600

namespace CFSG.KC.D4QK

open CFSG.KC.Enum CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.LargeExtraspecial.S63
open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native
open CFSG.Quasithin.Background.Harris.R1.D4Vert
open CFSG.KC.Co1B (mulWK)

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem notB_eq (b : Bool) : notB b = !b := by cases b <;> rfl

theorem bAnd_eq' (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIf_eq' (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = (if c then t else e) := by
  cases c <;> rfl

theorem nIf_eq' (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = (if c then t else e) := by
  cases c <;> rfl

theorem anyK_iff {n : Nat} {f : Nat → Bool} : anyK n f = true ↔ ∃ j < n, f j = true := by
  induction n with
  | zero =>
    exact ⟨fun h => absurd (h : false = true) Bool.false_ne_true,
      fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) (anyK n f) true (f n) = true ↔ _
    cases hf : f n
    · change anyK n f = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨j, hj, h⟩
        exact ⟨j, by omega, h⟩
      · rintro ⟨j, hj, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact ⟨j, hj, h⟩
        · rw [hf] at h
          exact absurd h Bool.false_ne_true
    · exact ⟨fun _ => ⟨n, Nat.lt_succ_self n, hf⟩, fun _ => rfl⟩

theorem allN_iff' {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  CFSG.KS.SporSch.M24.MatL.allN_iff

theorem mulWK_eq (A B : Nat) : mulR (unpackR 24 A) (unpackR 24 B) = unpackR 24 (mulWK A B) :=
  mulR_unpackR A B

theorem beq_eqM (A B : Nat) : (unpackR 24 A == unpackR 24 B) = eqM A B := by
  rw [beq_unpackR]
  rfl

theorem oneR_eqK (hone : oneK = idP) : oneR = unpackR 24 oneK := by
  rw [hone]
  exact oneR_eq

theorem powRows_eqK (hone : oneK = idP) (X : Nat) :
    ∀ e, powRows 24 (unpackR 24 X) e = unpackR 24 (powK X e)
  | 0 => oneR_eqK hone
  | e + 1 => by
    change mulR (powRows 24 (unpackR 24 X) e) (unpackR 24 X) = unpackR 24 (mulWK (powK X e) X)
    rw [powRows_eqK hone X e, mulWK_eq]

theorem eqM_one (hone : oneK = idP) (p : Nat) : eqM p oneK = decide (p % 2 ^ 576 = idP) := by
  unfold eqM
  rw [hone, Nat.mod_eq_of_lt idP_lt, Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

theorem ipL_eq (hone : oneK = idP) (X : Nat) : ∀ n p q, ipL X n p q = ipK X n p q
  | 0, _, _ => rfl
  | n + 1, p, q => by
    change Bool.rec (motive := fun _ => Nat) (ipL X n (mulWK p X) p) q (eqM p oneK) = ipK X (n + 1) p q
    rw [ipK, eqM_one hone]
    by_cases h : p % 2 ^ 576 = idP
    · rw [if_pos h, decide_eq_true h]
    · rw [if_neg h, decide_eq_false h]
      exact ipL_eq hone X n _ _

theorem invPow_eqK (hone : oneK = idP) (X : Nat) :
    invPow (unpackR 24 X) = unpackR 24 (ipL X 64 X oneK) := by
  rw [invPow_unpackR, ipL_eq hone, hone]

section Conj

variable {Z : Nat → Nat} {ZE : Nat}

theorem zPowA_get (hone : oneK = idP) (hz : zA = unpackR 24 ZE) {i : Nat} (hi : i < 8) :
    zPowA[i]! = unpackR 24 (powK ZE i) := by
  rw [getElem!_pos zPowA i (by simp [zPowA, hi]), ← powRows_eqK hone, ← hz]
  simp [zPowA]

theorem cjA_eq (hone : oneK = idP) (hz : zA = unpackR 24 ZE)
    (hZ : ∀ i < 7, unpackR 24 (Z i) = unpackR 24 (powK ZE i))
    (h7 : unpackR 24 (powK ZE 7) = unpackR 24 oneK) {i : Nat} (hi : i < 7) (U : Nat) :
    cjA i (unpackR 24 U) = unpackR 24 (cjK Z i U) := by
  unfold cjA cjK
  have e1 : zPowA[i]! = unpackR 24 (Z i) := by rw [zPowA_get hone hz (by omega), hZ i hi]
  have e2 : zPowA[7 - i]! = unpackR 24 (Z (Nat.mod (Nat.sub 7 i) 7)) := by
    rw [zPowA_get hone hz (by omega)]
    rcases Nat.eq_zero_or_pos i with rfl | h
    · change unpackR 24 (powK ZE 7) = unpackR 24 (Z 0)
      rw [h7, hZ 0 (by norm_num)]
      rfl
    · have e : Nat.mod (Nat.sub 7 i) 7 = 7 - i := Nat.mod_eq_of_lt (by change 7 - i < 7; omega)
      rw [e, hZ (7 - i) (by omega)]
  rw [e1, e2, mulWK_eq, mulWK_eq]

theorem phiArr_eq (hone : oneK = idP) (hz : zA = unpackR 24 ZE)
    (hZ : ∀ i < 7, unpackR 24 (Z i) = unpackR 24 (powK ZE i))
    (h7 : unpackR 24 (powK ZE 7) = unpackR 24 oneK) (U V : Nat) :
    phiArr (unpackR 24 U) (unpackR 24 V) =
      Array.ofFn (n := 14) fun j => unpackR 24 (phK Z U V j.val) := by
  unfold phiArr
  refine congrArg (fun f => Array.ofFn (n := 14) f) (funext fun j => ?_)
  unfold phK
  by_cases h : j.val < 7
  · have hb : Nat.blt j.val 7 = true := by rw [Nat.blt_eq]; exact h
    rw [if_pos h, cjA_eq hone hz hZ h7 h, hb]
  · have hb : Nat.blt j.val 7 = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
      exact h
    rw [if_neg h, cjA_eq hone hz hZ h7 (by omega), hb]
    rfl

end Conj

theorem ofFn_get (G : Nat → Nat) {i : Nat} (hi : i < 14) :
    (Array.ofFn (n := 14) fun j => unpackR 24 (G j.val))[i]! = unpackR 24 (G i) := by
  rw [getElem!_pos _ i (by simp [hi])]
  simp

theorem relValR_eq (hone : oneK = idP) (F FI : Nat → Nat) (r : List (Fin 14 × Bool)) :
    relValR (Array.ofFn (n := 14) fun j => unpackR 24 (F j.val))
        (Array.ofFn (n := 14) fun j => unpackR 24 (FI j.val)) r = unpackR 24 (relValK F FI r) := by
  induction r with
  | nil => exact oneR_eqK hone
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    unfold relValR at ih ⊢
    rw [List.foldr_cons, ih]
    change _ = unpackR 24 (strictN (relValK F FI r) fun x =>
      mulWK (Bool.rec (motive := fun _ => Nat) (FI a.val) (F a.val) b) x)
    rw [strictN_eq']
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [ofFn_get FI a.isLt, mulWK_eq]
    · simp only [if_true]
      rw [ofFn_get F a.isLt, mulWK_eq]

theorem relsOK_eq (hone : oneK = idP) (F FI : Nat → Nat) (rels : List (List (Fin 14 × Bool))) :
    relsOK (Array.ofFn (n := 14) fun j => unpackR 24 (F j.val))
        (Array.ofFn (n := 14) fun j => unpackR 24 (FI j.val)) rels = relsK F FI rels := by
  induction rels with
  | nil => rfl
  | cons r rs ih =>
    unfold relsOK at ih ⊢
    rw [List.all_cons, ih, relValR_eq hone, oneR_eqK hone, beq_eqM]
    change _ = Bool.rec (motive := fun _ => Bool) false (relsK F FI rs) (eqM (relValK F FI r) oneK)
    rw [bAnd_eq']

section Checks

variable {Z : Nat → Nat} {ZE : Nat}

theorem pr1_eq (hone : oneK = idP) (hz : zA = unpackR 24 ZE)
    (hZ : ∀ i < 7, unpackR 24 (Z i) = unpackR 24 (powK ZE i))
    (h7 : unpackR 24 (powK ZE 7) = unpackR 24 oneK) (X : Nat) :
    pr1 (unpackR 24 X) = pr1K Z qR1 X := by
  unfold pr1 pr1K
  rw [invPow_eqK hone, oneR_eqK hone, phiArr_eq hone hz hZ h7, phiArr_eq hone hz hZ h7,
    relsOK_eq hone, mulWK_eq, beq_eqM, strictB_eq', bAnd_eq', bIf_eq']
  cases eqM (mulWK X X) oneK <;> rfl

theorem pr2_eq (hone : oneK = idP) (hz : zA = unpackR 24 ZE)
    (hZ : ∀ i < 7, unpackR 24 (Z i) = unpackR 24 (powK ZE i))
    (h7 : unpackR 24 (powK ZE 7) = unpackR 24 oneK) (Y : Nat) :
    pr2 (unpackR 24 Y) = pr2K Z qR2 Y := by
  unfold pr2 pr2K
  rw [invPow_eqK hone, oneR_eqK hone, phiArr_eq hone hz hZ h7, phiArr_eq hone hz hZ h7,
    relsOK_eq hone, strictB_eq']

theorem any_elG (P : Nat → Nat) (N : Nat) (f : Array ℕ → Bool) :
    (ElG P N).any f = anyK N fun j => f (unpackR 24 (P j)) := by
  rw [Bool.eq_iff_iff, Array.any_eq_true, anyK_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    have hi' : i < N := by simpa [ElG] using hi
    refine ⟨i, hi', ?_⟩
    rw [← getElem!_pos (ElG P N) i hi, elG_get hi'] at h
    exact h
  · rintro ⟨i, hi, h⟩
    have hi' : i < (ElG P N).size := by simpa [ElG] using hi
    refine ⟨i, hi', ?_⟩
    rw [← getElem!_pos (ElG P N) i hi', elG_get hi]
    exact h

theorem all_elG (P : Nat → Nat) (N : Nat) (f : Array ℕ → Bool) :
    (ElG P N).all f = allN N fun j => f (unpackR 24 (P j)) := by
  rw [Bool.eq_iff_iff, Array.all_eq_true, allN_iff']
  constructor
  · intro h i hi
    have hi' : i < (ElG P N).size := by simpa [ElG] using hi
    have := h i hi'
    rwa [← getElem!_pos (ElG P N) i hi', elG_get hi] at this

  · intro h i hi
    have hi' : i < N := by simpa [ElG] using hi
    rw [← getElem!_pos (ElG P N) i hi, elG_get hi']
    exact h i hi'

theorem pairOK_eq (hone : oneK = idP) (hz : zA = unpackR 24 ZE)
    (hZ : ∀ i < 7, unpackR 24 (Z i) = unpackR 24 (powK ZE i))
    (h7 : unpackR 24 (powK ZE 7) = unpackR 24 oneK) {PK : Nat → Nat} {nk Y1 Y2 : Nat}
    (hy1 : y1A = unpackR 24 Y1) (hy2 : y2A = unpackR 24 Y2) (X Y : Nat) :
    CFSG.Quasithin.Background.Harris.R1.D4Vert.pairOK (ElG PK nk) (unpackR 24 X) (unpackR 24 Y) =
      pairOKK Z qR12 PK nk Y1 Y2 X Y := by
  unfold CFSG.Quasithin.Background.Harris.R1.D4Vert.pairOK pairOKK
  rw [invPow_eqK hone, invPow_eqK hone, phiArr_eq hone hz hZ h7, phiArr_eq hone hz hZ h7,
    relsOK_eq hone, strictB_eq', strictB_eq', any_elG, hy1, hy2, bIf_eq']
  have e : (anyK nk fun j => (mulR (unpackR 24 X) (unpackR 24 (PK j)) ==
        mulR (unpackR 24 (PK j)) (unpackR 24 Y1) &&
      mulR (unpackR 24 Y) (unpackR 24 (PK j)) == mulR (unpackR 24 (PK j)) (unpackR 24 Y2))) =
      anyK nk fun j => strictB (PK j) fun K =>
        Bool.rec (motive := fun _ => Bool) false (eqM (mulWK Y K) (mulWK K Y2))
          (eqM (mulWK X K) (mulWK K Y1)) := by
    refine congrArg (anyK nk) (funext fun j => ?_)
    rw [strictB_eq', bAnd_eq', mulWK_eq, mulWK_eq, mulWK_eq, mulWK_eq, beq_eqM, beq_eqM]
  rw [e]
  cases relsK (phK Z X Y) (phK Z (ipL X 64 X oneK) (ipL Y 64 Y oneK)) qR12 <;> rfl

theorem testBit_maskL (c : Nat → Bool) :
    ∀ n s j, (maskL c n s).testBit j = (s.testBit j || (decide (j < n) && c j))
  | 0, s, j => by
    change s.testBit j = _
    simp
  | n + 1, s, j => by
    change (strictN (Bool.rec (motive := fun _ => Nat) s
      (Nat.lor s (Nat.shiftLeft 1 n)) (c n)) (maskL c n)).testBit j = _
    rw [strictN_eq', testBit_maskL c n _ j]
    cases hc : c n
    · change (s.testBit j || (decide (j < n) && c j)) = _
      by_cases hj : j = n
      · subst hj
        simp [hc]
      · have : (j < n + 1) ↔ j < n := by omega
        simp [this]
    · change ((Nat.lor s (Nat.shiftLeft 1 n)).testBit j || (decide (j < n) && c j)) = _
      have e : Nat.lor s (Nat.shiftLeft 1 n) = s ||| 2 ^ n := by
        rw [← Nat.one_shiftLeft]
        rfl
      rw [e, Nat.testBit_or, Nat.testBit_two_pow]
      by_cases hj : j = n
      · subst hj
        simp [hc]
      · have : (j < n + 1) ↔ j < n := by omega
        simp [this, Ne.symm hj]

theorem bitK_eq (M j : Nat) : bitK M j = M.testBit j := by
  unfold bitK
  rw [Bool.eq_iff_iff, Nat.beq_eq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  change (M >>> j) &&& 1 = 1 ↔ _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem pairCheck_eq (hone : oneK = idP) (hz : zA = unpackR 24 ZE)
    (hZ : ∀ i < 7, unpackR 24 (Z i) = unpackR 24 (powK ZE i))
    (h7 : unpackR 24 (powK ZE 7) = unpackR 24 oneK) {P PK : Nat → Nat} {N nk Y1 Y2 : Nat}
    (hy1 : y1A = unpackR 24 Y1) (hy2 : y2A = unpackR 24 Y2) :
    pairCheck (ElG P N) (ElG PK nk) = pairCheckK Z qR1 qR2 qR12 P N PK nk Y1 Y2 := by
  have key : ∀ i < N, ∀ j < N, (maskK Z qR2 P N).testBit j = pr2K Z qR2 (P j) := by
    intro i _ j hj
    unfold maskK
    rw [testBit_maskL, strictB_eq']
    simp [hj]
  unfold pairCheck pairCheckK
  rw [strictB_eq', Bool.eq_iff_iff, Array.all_eq_true_iff_forall_mem, allN_iff']
  constructor
  · intro h i hi
    rw [strictB_eq', bIf_eq']
    split
    · rename_i h1
      rw [allN_iff']
      intro j hj
      rw [bIf_eq', bitK_eq, key i hi j hj]
      split
      · rename_i h2
        rw [strictB_eq', ← pairOK_eq hone hz hZ h7 hy1 hy2]
        have hm : unpackR 24 (P i) ∈ (ElG P N).filter pr1 := by
          rw [Array.mem_filter, pr1_eq hone hz hZ h7]
          exact ⟨Array.mem_ofFn.2 ⟨⟨i, hi⟩, rfl⟩, h1⟩
        have h3 := h _ hm
        rw [Array.all_eq_true_iff_forall_mem] at h3
        apply h3
        rw [Array.mem_filter, pr2_eq hone hz hZ h7]
        exact ⟨Array.mem_ofFn.2 ⟨⟨j, hj⟩, rfl⟩, h2⟩
      · rfl
    · rfl
  · intro h x hx
    rw [Array.mem_filter] at hx
    obtain ⟨hx, h1⟩ := hx
    obtain ⟨⟨i, hi⟩, rfl⟩ := Array.mem_ofFn.1 hx
    rw [pr1_eq hone hz hZ h7] at h1
    rw [Array.all_eq_true_iff_forall_mem]
    intro y hy
    rw [Array.mem_filter] at hy
    obtain ⟨hy, h2⟩ := hy
    obtain ⟨⟨j, hj⟩, rfl⟩ := Array.mem_ofFn.1 hy
    rw [pr2_eq hone hz hZ h7] at h2
    have hi' := h i hi
    rw [strictB_eq', bIf_eq', if_pos h1, allN_iff'] at hi'
    have hj' := hi' j hj
    rw [bIf_eq', bitK_eq, key i hi j hj, if_pos h2, strictB_eq'] at hj'
    change CFSG.Quasithin.Background.Harris.R1.D4Vert.pairOK (ElG PK nk) (unpackR 24 (P i))
      (unpackR 24 (P j)) = true
    rw [pairOK_eq hone hz hZ h7 hy1 hy2]
    exact hj'

theorem invOKT_eq (hone : oneK = idP) (P : Nat → Nat) (N : Nat) :
    invOKT (ElG P N) = invTK P N := by
  unfold invOKT invTK
  rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff, allN_iff']
  have hs : (ElG P N).size = N := by simp [ElG]
  rw [hs]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [elG_get hi, invPow_eqK hone, validR_unpackR, Bool.true_and, mulWK_eq, oneR_eqK hone,
    beq_eqM, strictB_eq']

theorem commCheck_eq (hz : zA = unpackR 24 ZE) (P : Nat → Nat) (N : Nat) :
    commCheck (ElG P N) = commK ZE P N := by
  unfold commCheck commK
  rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff, allN_iff']
  have hs : (ElG P N).size = N := by simp [ElG]
  rw [hs]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [elG_get hi, hz, mulWK_eq, mulWK_eq, beq_eqM, strictB_eq']

theorem cubeCheck_eq (hone : oneK = idP) {S SI : Nat} (hs0 : s0A = unpackR 24 S)
    (hs0i : s0iA = unpackR 24 SI) (P : Nat → Nat) (N : Nat) :
    cubeCheck (ElG P N) = cubeK S SI P N := by
  unfold cubeCheck cubeK
  rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff, allN_iff']
  have hs : (ElG P N).size = N := by simp [ElG]
  rw [hs]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [elG_get hi, hs0, hs0i, mulWK_eq, mulWK_eq, oneR_eqK hone, beq_eqM, beq_eqM, beq_eqM,
    beq_eqM, strictB_eq', bIf_eq', bIf_eq', bIf_eq']
  cases eqM (mulWK (mulWK (P i) (P i)) (P i)) oneK <;> cases eqM (P i) oneK <;>
    cases eqM (P i) S <;> cases eqM (P i) SI <;> rfl

theorem all_ofFn (G : Nat → Nat) (n : Nat) (f : Array ℕ → Bool) :
    (Array.ofFn (n := n) fun l => unpackR 24 (G l.val)).all f = allN n fun l => f (unpackR 24 (G l)) :=
  all_elG G n f

theorem commAll_eq (G : Nat → Nat) (ng X : Nat) :
    ((Array.ofFn (n := ng) fun l => unpackR 24 (G l.val)).all fun g =>
      mulR (unpackR 24 X) g == mulR g (unpackR 24 X)) = commAllK G ng X := by
  rw [all_ofFn]
  unfold commAllK
  refine congrArg (allN ng) (funext fun l => ?_)
  rw [mulWK_eq, mulWK_eq, beq_eqM, strictB_eq']

theorem centerCheck_eq (hone : oneK = idP) {G : Nat → Nat} {Z0 X0 : Nat}
    (hq : qGensA = Array.ofFn (n := 14) fun l => unpackR 24 (G l.val))
    (hz0 : z0R = unpackR 24 Z0) (hx0 : x0A = unpackR 24 X0) (P : Nat → Nat) (N : Nat) :
    centerCheck (ElG P N) = centerK G 14 Z0 X0 (mulWK Z0 X0) P N := by
  unfold centerCheck centerK
  rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff, allN_iff']
  have hs : (ElG P N).size = N := by simp [ElG]
  rw [hs]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [elG_get hi, hq, commAll_eq, hz0, hx0, mulWK_eq, oneR_eqK hone, beq_eqM, beq_eqM, beq_eqM,
    beq_eqM, strictB_eq', bIf_eq', bIf_eq', bIf_eq', bIf_eq']
  cases commAllK G 14 (P i) <;> cases eqM (P i) oneK <;> cases eqM (P i) Z0 <;>
    cases eqM (P i) X0 <;> cases eqM (P i) (mulWK Z0 X0) <;> rfl

theorem kcCheck_eq (hone : oneK = idP) {G : Nat → Nat}
    (hq : qGensA = Array.ofFn (n := 14) fun l => unpackR 24 (G l.val)) (P : Nat → Nat) (N : Nat) :
    kcCheck (ElG P N) = kcK G 14 P N := by
  unfold kcCheck kcK
  rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff, allN_iff']
  have hs : (ElG P N).size = N := by simp [ElG]
  rw [hs]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [elG_get hi, hq, commAll_eq, oneR_eqK hone, beq_eqM, strictB_eq', bIf_eq']
  cases commAllK G 14 (P i) <;> cases eqM (P i) oneK <;> rfl

end Checks

end CFSG.KC.D4QK

end
