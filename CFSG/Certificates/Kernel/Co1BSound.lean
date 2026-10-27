module

public import Certificates.Data.Kernel.Co1B
public import CFSG.Certificates.Kernel.Co1F2Sound
public import Certificates.Data.CFSGNative.Co1Schreier.Base
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylBridgeData
import CFSG.Certificates.Kernel.Co1BInvSound

public section

namespace CFSG.KC.Co1B

open CFSG.KC.Co1F2 CFSG.KLie.CT

theorem mul_unpack (A B : Nat) :
    CFSG.Sporadic.Co1Schreier.Native.mul (unpackR 24 A) (unpackR 24 B) = unpackR 24 (mulK A B) :=
  CFSG.KC.F2W.mulRows_unpackR 24 A B

theorem testBit_field (w P i b : Nat) :
    (P / 2 ^ (w * i) % 2 ^ w).testBit b = (decide (b < w) && P.testBit (w * i + b)) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm b]

theorem fields_eq_iff {w : Nat} (hw : 0 < w) (n P Q : Nat) :
    (∀ i < n, P / 2 ^ (w * i) % 2 ^ w = Q / 2 ^ (w * i) % 2 ^ w) ↔ P % 2 ^ (w * n) = Q % 2 ^ (w * n) := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hp : p < w * n
    · have hi : p / w < n := (Nat.div_lt_iff_lt_mul hw).2 (by rw [Nat.mul_comm]; exact hp)
      have hb := congrArg (fun x => x.testBit (p % w)) (h (p / w) hi)
      simp only [testBit_field, Nat.mod_lt p hw, decide_true, Bool.true_and, Nat.div_add_mod] at hb
      rw [hb]
    · simp [hp]
  · intro h i hi
    apply Nat.eq_of_testBit_eq
    intro b
    rw [testBit_field, testBit_field]
    by_cases hb : b < w
    · have hlt : w * i + b < w * n := by
        have : w * (i + 1) ≤ w * n := Nat.mul_le_mul_left w hi
        rw [Nat.mul_succ] at this
        omega
      have h2 := congrArg (fun x => x.testBit (w * i + b)) h
      simp only [Nat.testBit_mod_two_pow, hlt, decide_true, Bool.true_and] at h2
      rw [h2]
    · simp [hb]

set_option exponentiation.threshold 2048 in
theorem beq_unpack (A B : Nat) : (unpackR 24 A == unpackR 24 B) = eqK A B := by
  have h576 : Nat.shiftLeft 1 576 = 2 ^ (24 * 24) := by
    change 1 <<< 576 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  change _ = Nat.beq (A % Nat.shiftLeft 1 576) (B % Nat.shiftLeft 1 576)
  rw [h576]
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq, ← fields_eq_iff (by decide) 24 A B]
  constructor
  · intro h i hi
    have := congrArg (fun X : Array Nat => X[i]!) h
    simpa [unpackR, hi] using this
  · intro h
    exact congrArg (Array.ofFn (n := 24)) (funext fun i => h i.val i.isLt)

theorem word_sound (rs is : List Nat) (w : List Int) :
    CFSG.Sporadic.Co1Schreier.Native.word (rs.map (unpackR 24)) (is.map (unpackR 24)) w =
      unpackR 24 (wordK rs is w) := by
  have hone : CFSG.Sporadic.Co1Schreier.Native.one = unpackR 24 oneK := CFSG.KC.F2W.unpackR_idF.symm
  have hget : ∀ (l : List Nat) (i : Nat),
      (l.map (unpackR 24)).getD i (unpackR 24 oneK) = unpackR 24 (getL oneK l i) := by
    intro l
    induction l with
    | nil => intro i; rfl
    | cons a l ih =>
      intro i
      cases i with
      | zero => rfl
      | succ i => exact ih i
  have hlet : ∀ j, CFSG.Sporadic.Co1Schreier.Native.letter (rs.map (unpackR 24)) (is.map (unpackR 24)) j =
      unpackR 24 (letK rs is j) := by
    intro j
    rw [CFSG.Sporadic.Co1Schreier.Native.letter, hone]
    rcases j with (_ | n) | n
    · rw [ite_eq_right (by decide)]
      exact hget is 0
    · rw [ite_eq_left (c := 0 < Int.ofNat (n + 1)) (Int.ofNat_succ_pos n)]
      exact hget rs n
    · rw [ite_eq_right (c := 0 < Int.negSucc n) (Int.not_lt.2 (Int.le_of_lt (Int.negSucc_lt_zero n)))]
      exact hget is n
  have key : ∀ (w : List Int) (acc : Nat),
      w.foldl (fun acc j => CFSG.Sporadic.Co1Schreier.Native.mul acc
        (CFSG.Sporadic.Co1Schreier.Native.letter (rs.map (unpackR 24)) (is.map (unpackR 24)) j))
        (unpackR 24 acc) = unpackR 24 (wordFromK rs is w acc) := by
    intro w
    induction w with
    | nil => intro acc; rfl
    | cons j w ih =>
      intro acc
      rw [List.foldl_cons, hlet, mul_unpack, ih]
      change _ = unpackR 24 (CFSG.KC.Loop.strictN (mulK acc (letK rs is j)) (wordFromK rs is w))
      rw [CFSG.KC.F2W.strictN_eq]
  rw [CFSG.Sporadic.Co1Schreier.Native.word, hone]
  exact key w oneK

theorem inv_sound' {A AI : Nat} (h : andB (andB (canK A) (canK AI)) (Nat.beq (mulK A AI) oneK) = true) :
    CFSG.Sporadic.Co1Schreier.Native.inv (unpackR 24 A) = unpackR 24 AI := by
  have hb : Nat.beq (mulK A AI) oneK = true := by
    revert h
    cases andB (canK A) (canK AI) <;> simp [andB]
  exact CFSG.KC.F2W.inv_unpackR (Nat.eq_of_beq_eq_true hb)

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem getL_eq (x : Nat) : ∀ (L : List Nat) (i : Nat), getL x L i = L[i]?.getD x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => getL_eq x L i

theorem lenL_eq : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenL_eq L)

theorem takeK_eq : ∀ (l : List Nat) (n : Nat), takeK n l = l.take n
  | [], n => by cases n <;> rfl
  | _ :: _, 0 => rfl
  | x :: l, n + 1 => by
    change x :: takeK n l = _
    rw [takeK_eq l n]
    rfl

theorem prefixK_sound : ∀ (p l : List Nat), prefixK p l = true → ∃ t, l = p ++ t
  | [], l, _ => ⟨l, rfl⟩
  | _ :: _, [], h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | x :: p, y :: l, h => by
    change andB (Nat.beq x y) (prefixK p l) = true at h
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨t, rfl⟩ := prefixK_sound p l h2
    exact ⟨t, by rw [Nat.eq_of_beq_eq_true h1]; rfl⟩

theorem invsK_sound : ∀ (RS RIS : List Nat), invsK RS RIS = true →
    RS.length = RIS.length ∧ ∀ i (h1 : i < RS.length) (h2 : i < RIS.length),
      andB (andB (canK RS[i]) (canK RIS[i])) (Nat.beq (mulK RS[i] RIS[i]) oneK) = true
  | [], [], _ => ⟨rfl, fun _ h1 => absurd h1 (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | _ :: _, [], h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | m :: RS, mi :: RIS, h => by
    change andB (andB (canK m) (canK mi)) (andB (Nat.beq (mulK m mi) oneK) (invsK RS RIS)) = true at h
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨h3, h4⟩ := andB_true h2
    obtain ⟨hl, hi⟩ := invsK_sound RS RIS h4
    refine ⟨by rw [List.length_cons, List.length_cons, hl], fun i h1' h2' => ?_⟩
    cases i with
    | zero =>
      rw [List.getElem_cons_zero, List.getElem_cons_zero, h1, h3]
      rfl
    | succ i =>
      simp only [List.getElem_cons_succ]
      exact hi i (Nat.lt_of_succ_lt_succ h1') (Nat.lt_of_succ_lt_succ h2')

theorem stepsK_sound (RS RIS : List Nat) : ∀ (derivs : List (List Int)) (k : Nat),
    stepsK RS RIS derivs k = true → RS.length = k + derivs.length ∧
      ∀ j (hj : j < derivs.length),
        getL oneK RS (k + j) = wordK (takeK (k + j) RS) (takeK (k + j) RIS) derivs[j]
  | [], k, h => by
    change Nat.beq (lenL RS) k = true at h
    have := Nat.eq_of_beq_eq_true h
    rw [lenL_eq] at this
    exact ⟨by rw [this]; rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | w :: ds, k, h => by
    change andB (Nat.beq (getL oneK RS k) (wordK (takeK k RS) (takeK k RIS) w))
      (stepsK RS RIS ds (k + 1)) = true at h
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨hl, hs⟩ := stepsK_sound RS RIS ds (k + 1) h2
    refine ⟨by rw [hl, List.length_cons]; omega, fun j hj => ?_⟩
    cases j with
    | zero => exact Nat.eq_of_beq_eq_true h1
    | succ j =>
      have e : k + (j + 1) = k + 1 + j := by omega
      rw [e, List.getElem_cons_succ]
      exact hs j (Nat.lt_of_succ_lt_succ hj)

theorem one_eq : CFSG.Sporadic.Co1Schreier.Native.one = unpackR 24 oneK :=
  CFSG.KC.F2W.unpackR_idF.symm

theorem dag_fold (RS RIS : List Nat) (hl : RS.length = RIS.length)
    (hinv : ∀ i (h1 : i < RS.length) (h2 : i < RIS.length),
      andB (andB (canK RS[i]) (canK RIS[i])) (Nat.beq (mulK RS[i] RIS[i]) oneK) = true) :
    ∀ (derivs : List (List Int)) (k : Nat), stepsK RS RIS derivs k = true →
      derivs.foldl CFSG.Sporadic.Co1Schreier.Native.step
        ((RS.take k).map (unpackR 24), (RIS.take k).map (unpackR 24), true) =
      (RS.map (unpackR 24), RIS.map (unpackR 24), true)
  | [], k, h => by
    obtain ⟨hk, _⟩ := stepsK_sound RS RIS [] k h
    rw [List.length_nil, Nat.add_zero] at hk
    rw [List.foldl_nil, List.take_of_length_le (Nat.le_of_eq hk),
      List.take_of_length_le (by omega)]
  | w :: ds, k, h => by
    obtain ⟨hk, hs⟩ := stepsK_sound RS RIS (w :: ds) k h
    have h2 : stepsK RS RIS ds (k + 1) = true :=
      (andB_true (a := Nat.beq (getL oneK RS k) (wordK (takeK k RS) (takeK k RIS) w)) h).2
    have hkl : k < RS.length := by rw [hk, List.length_cons]; omega
    have hkl' : k < RIS.length := by rw [← hl]; exact hkl
    have hw : getL oneK RS k = wordK (takeK k RS) (takeK k RIS) w := hs 0 (by simp)
    rw [getL_eq, List.getElem?_eq_getElem hkl, Option.getD_some, takeK_eq, takeK_eq] at hw
    have hc := hinv k hkl hkl'
    have hi := inv_sound' hc
    have hm : mulK RS[k] RIS[k] = oneK := Nat.eq_of_beq_eq_true (andB_true hc).2
    have hstep : CFSG.Sporadic.Co1Schreier.Native.step
        ((RS.take k).map (unpackR 24), (RIS.take k).map (unpackR 24), true) w =
        ((RS.take (k + 1)).map (unpackR 24), (RIS.take (k + 1)).map (unpackR 24), true) := by
      change ((RS.take k).map (unpackR 24) ++
          [CFSG.Sporadic.Co1Schreier.Native.word ((RS.take k).map (unpackR 24))
            ((RIS.take k).map (unpackR 24)) w],
        (RIS.take k).map (unpackR 24) ++
          [CFSG.Sporadic.Co1Schreier.Native.inv (CFSG.Sporadic.Co1Schreier.Native.word
            ((RS.take k).map (unpackR 24)) ((RIS.take k).map (unpackR 24)) w)],
        (true && CFSG.Sporadic.Co1Schreier.Native.mul (CFSG.Sporadic.Co1Schreier.Native.word
            ((RS.take k).map (unpackR 24)) ((RIS.take k).map (unpackR 24)) w)
          (CFSG.Sporadic.Co1Schreier.Native.inv (CFSG.Sporadic.Co1Schreier.Native.word
            ((RS.take k).map (unpackR 24)) ((RIS.take k).map (unpackR 24)) w)) ==
          CFSG.Sporadic.Co1Schreier.Native.one)) = _
      rw [word_sound, ← hw, hi, mul_unpack, hm, ← one_eq, beq_self_eq_true, List.take_add_one,
        List.take_add_one, List.getElem?_eq_getElem hkl, List.getElem?_eq_getElem hkl']
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, Bool.true_and]
    rw [List.foldl_cons, hstep]
    exact dag_fold RS RIS hl hinv ds (k + 1) h2

theorem dag_sound {base : List Nat} {derivs : List (List Int)} {RS RIS : List Nat}
    (h : dagOK base derivs RS RIS = true) :
    CFSG.Sporadic.Co1Schreier.Native.dag (base.map (unpackR 24)) derivs =
      (RS.map (unpackR 24), RIS.map (unpackR 24), true) := by
  obtain ⟨hp, h'⟩ := andB_true h
  obtain ⟨hi, hs⟩ := andB_true h'
  obtain ⟨t, rfl⟩ := prefixK_sound base RS hp
  obtain ⟨hl, hinv⟩ := invsK_sound _ RIS hi
  rw [lenL_eq] at hs
  have hBR : base.length ≤ RIS.length := by rw [← hl, List.length_append]; omega
  have hbi : ∀ i (hi : i < base.length),
      CFSG.Sporadic.Co1Schreier.Native.inv (unpackR 24 base[i]) = unpackR 24 (RIS[i]'(by omega)) ∧
      CFSG.Sporadic.Co1Schreier.Native.mul (unpackR 24 base[i]) (unpackR 24 (RIS[i]'(by omega))) =
        CFSG.Sporadic.Co1Schreier.Native.one := by
    intro i hi
    have hc := hinv i (by rw [List.length_append]; omega) (by omega)
    rw [List.getElem_append_left hi] at hc
    refine ⟨inv_sound' hc, ?_⟩
    rw [mul_unpack, Nat.eq_of_beq_eq_true (andB_true hc).2, one_eq]
  have e1 : base.map (unpackR 24) = ((base ++ t).take base.length).map (unpackR 24) := by simp
  have e2 : (base.map (unpackR 24)).map CFSG.Sporadic.Co1Schreier.Native.inv =
      (RIS.take base.length).map (unpackR 24) := by
    apply List.ext_getElem (by simp; omega)
    intro i h1 _
    simp only [List.getElem_map, List.getElem_take]
    exact (hbi i (by simpa using h1)).1
  have e3 : ((base.map (unpackR 24)).all fun b => CFSG.Sporadic.Co1Schreier.Native.mul b
      (CFSG.Sporadic.Co1Schreier.Native.inv b) == CFSG.Sporadic.Co1Schreier.Native.one) = true := by
    rw [List.all_eq_true]
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    rw [(hbi i hi).1, (hbi i hi).2]
    exact beq_self_eq_true _
  rw [CFSG.Sporadic.Co1Schreier.Native.dag, e2, e3, e1]
  exact dag_fold _ RIS hl hinv derivs base.length hs

@[expose] def unpackP (P : Nat) : Array Nat := Array.ofFn (n := 240) fun i => P / 2 ^ (8 * i.val) % 256

set_option exponentiation.threshold 2048 in
theorem sh1920 :Nat.shiftLeft 1 1920 = 2 ^ (8 * 240) := by
  change 1 <<< 1920 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem pget_eq (P i : Nat) : pget P i = P / 2 ^ (8 * i) % 2 ^ 8 := by
  change (P >>> (8 * i)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem pget_lt (P i : Nat) : pget P i < 2 ^ 8 := by
  rw [pget_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos 8)

theorem unpackP_eq (P : Nat) : unpackP P = Array.ofFn (n := 240) fun i => pget P i.val := by
  simp only [unpackP, pget_eq, Nat.reducePow]

theorem unpackP_get_lt (P : Nat) {k : Nat} (hk : k < 240) : (unpackP P)[k]! = pget P k := by
  rw [unpackP_eq]
  simp [hk]

set_option exponentiation.threshold 2048 in
theorem unpackP_get{P : Nat} (hP : P < 2 ^ (8 * 240)) (k : Nat) : (unpackP P)[k]! = pget P k := by
  by_cases hk : k < 240
  · exact unpackP_get_lt P hk
  · rw [getElem!_neg _ _ (by rw [unpackP_eq, Array.size_ofFn]; exact hk), pget_eq,
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by decide) (by omega)))]
    rfl

theorem ppackN_eq (f : Nat → Nat) : ∀ n : Nat,
    Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul 8 i))) n =
      orN n fun i => f i <<< (8 * i)
  | 0 => rfl
  | n + 1 => by
    change Nat.lor _ (Nat.shiftLeft (f n) (Nat.mul 8 n)) = (f n <<< (8 * n)) ||| orN n _
    rw [ppackN_eq f n]
    exact Nat.or_comm _ _

theorem ppack_eq (f : Nat → Nat) : ppack f = orN 240 fun i => f i <<< (8 * i) := ppackN_eq f 240

theorem pget_ppack {f : Nat → Nat} (hf : ∀ i < 240, f i < 2 ^ 8) {i : Nat} (hi : i < 240) :
    pget (ppack f) i = f i := by
  rw [ppack_eq, pget_eq]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_field, CFSG.KC.F2W.testBit_orN_fields hf]
  by_cases hb : b < 8
  · have h1 : (8 * i + b) / 8 = i := by omega
    have h2 : (8 * i + b) % 8 = b := by omega
    have h3 : 8 * i + b < 8 * 240 := by omega
    rw [h1, h2, decide_eq_true hb, decide_eq_true h3, Bool.true_and, Bool.true_and]
  · rw [decide_eq_false hb, Bool.false_and,
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf i hi) (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem pcomp_eq (t u : Nat) : pcomp t u = ppack fun i => pget t (pget u i) := by
  simp only [pcomp, CFSG.KC.F2W.strictN_eq]

theorem pget_pcomp (t u : Nat) {i : Nat} (hi : i < 240) : pget (pcomp t u) i = pget t (pget u i) := by
  rw [pcomp_eq]
  exact pget_ppack (fun _ _ => pget_lt _ _) hi

theorem pget_pidK {i : Nat} (hi : i < 240) : pget pidK i = i :=
  pget_ppack (f := fun i => i) (fun _ h => Nat.lt_of_lt_of_le h (by decide)) hi

set_option exponentiation.threshold 2048 in
theorem pcomp_lt (t u : Nat) : pcomp t u < Nat.shiftLeft 1 1920 := by
  rw [pcomp_eq, ppack_eq, sh1920]
  exact CFSG.KC.F2W.orN_fields_lt fun _ _ => pget_lt _ _

theorem wordArr_aux (R : List Nat) : ∀ l : List Nat,
    (∀ r ∈ l, (CFSG.EvenSmallLie.OmegaEight.Weyl.reflArr r).toList =
      (List.range 240).map (pget (getL 0 R r))) →
    (∀ r ∈ l, ∀ i < 240, pget (getL 0 R r) i < 240) →
    CFSG.EvenSmallLie.OmegaEight.Weyl.wordArr l = unpackP (pword R l) ∧
      ∀ i < 240, pget (pword R l) i < 240
  | [], _, _ => by
    change CFSG.Monster.B.Co2.Native.idA 240 = unpackP pidK ∧ ∀ i < 240, pget pidK i < 240
    refine ⟨?_, fun i hi => by rw [pget_pidK hi]; exact hi⟩
    rw [CFSG.Monster.B.Co2.Native.idA, unpackP_eq]
    exact congrArg (Array.ofFn (n := 240)) (funext fun i => (pget_pidK i.isLt).symm)
  | r :: l, hR, hlt => by
    obtain ⟨ih1, ih2⟩ := wordArr_aux R l (fun r' h => hR r' (List.mem_cons_of_mem r h))
      (fun r' h => hlt r' (List.mem_cons_of_mem r h))
    have hT := hR r List.mem_cons_self
    have hTl := hlt r List.mem_cons_self
    have hTget : ∀ k < 240, (CFSG.EvenSmallLie.OmegaEight.Weyl.reflArr r)[k]! = pget (getL 0 R r) k :=
      fun k hk => by
        rw [← Array.getElem!_toList, hT]
        simp [hk]
    change CFSG.Monster.B.Co2.Native.compA 240 (CFSG.EvenSmallLie.OmegaEight.Weyl.reflArr r)
        (CFSG.EvenSmallLie.OmegaEight.Weyl.wordArr l) = unpackP (pcomp (getL 0 R r) (pword R l)) ∧
      ∀ i < 240, pget (pcomp (getL 0 R r) (pword R l)) i < 240
    refine ⟨?_, fun i hi => ?_⟩
    · rw [ih1, CFSG.Monster.B.Co2.Native.compA, unpackP_eq (pcomp _ _)]
      refine congrArg (Array.ofFn (n := 240)) (funext fun i => ?_)
      rw [unpackP_get_lt _ i.isLt, hTget _ (ih2 i i.isLt), pget_pcomp _ _ i.isLt]
    · rw [pget_pcomp _ _ hi]
      exact hTl _ (ih2 i hi)

theorem wordArr_sound (R : List Nat) (l : List Nat)
    (hR : ∀ r ∈ l, (CFSG.EvenSmallLie.OmegaEight.Weyl.reflArr r).toList =
      (List.range 240).map (pget (getL 0 R r)))
    (hlt : ∀ r ∈ l, ∀ i < 240, pget (getL 0 R r) i < 240) :
    CFSG.EvenSmallLie.OmegaEight.Weyl.wordArr l = unpackP (pword R l) :=
  (wordArr_aux R l hR hlt).1

theorem compA_sound {t : Nat} (u : Nat) (ht : t < Nat.shiftLeft 1 1920) :
    CFSG.Monster.B.Co2.Native.compA 240 (unpackP t) (unpackP u) = unpackP (pcomp t u) := by
  rw [sh1920] at ht
  rw [CFSG.Monster.B.Co2.Native.compA, unpackP_eq (pcomp t u)]
  refine congrArg (Array.ofFn (n := 240)) (funext fun i => ?_)
  rw [unpackP_get_lt u i.isLt, unpackP_get ht, pget_pcomp t u i.isLt]

theorem allLt_iff (p : Nat → Bool) : ∀ n : Nat,
    CFSG.Monster.B.Co2.Native.allLt n p = true ↔ ∀ i < n, p i = true
  | 0 => by simp [CFSG.Monster.B.Co2.Native.allLt]
  | n + 1 => by
    have ih := allLt_iff p n
    simp only [CFSG.Monster.B.Co2.Native.allLt, Nat.all_succ, Bool.and_eq_true] at ih ⊢
    rw [ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      by_cases hin : i < n
      · exact h i hin
      · have : i = n := by omega
        subst this
        exact hn
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem eqA_sound {t A : Nat} {a : Array Nat} (ht : t < Nat.shiftLeft 1 1920)
    (hA : A < Nat.shiftLeft 1 1920)
    (ha : a.toList = (List.range 240).map (pget A)) :
    CFSG.Monster.B.Co2.Native.eqA 240 (unpackP t) a = Nat.beq t A := by
  rw [sh1920] at ht hA
  have hai : ∀ i < 240, a[i]! = pget A i := fun i hi => by
    rw [← Array.getElem!_toList, ha]
    simp [hi]
  apply Bool.eq_iff_iff.2
  rw [Nat.beq_eq, CFSG.Monster.B.Co2.Native.eqA, allLt_iff]
  constructor
  · intro h
    have hfe : ∀ i < 240, t / 2 ^ (8 * i) % 2 ^ 8 = A / 2 ^ (8 * i) % 2 ^ 8 := fun i hi => by
      have := h i hi
      rw [unpackP_get_lt t hi, hai i hi, beq_iff_eq, pget_eq, pget_eq] at this
      exact this
    have := (fields_eq_iff (by decide) 240 t A).1 hfe
    rwa [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hA] at this
  · intro hEq i hi
    rw [unpackP_get_lt t hi, hai i hi, hEq]
    exact beq_self_eq_true _

end CFSG.KC.Co1B

end
