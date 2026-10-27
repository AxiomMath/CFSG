module

public import Certificates.Data.Kernel.FongPerm
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.FongPerm

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by
  cases y <;> rfl

theorem forceL_eq (l : List ℕ) (k : List ℕ → Bool) : forceL l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih =>
    change letB x (fun x => forceL l fun ys => k (x :: ys)) = _
    rw [letB_eq, ih]

theorem mulS_eq (n s t : ℕ) : mulS n s t = mul n s t := by
  simp only [mulS, letN_eq]

theorem powS_eq (n s k : ℕ) : powS n s k = pow n s k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change mulS n (powS n s k) s = mul n (pow n s k) s
    rw [mulS_eq, ih]

theorem getK_eq {α : Type} (l : List α) (d : α) (i : ℕ) : getK l d i = l.getD i d := by
  induction l generalizing i with
  | nil => simp [getK]
  | cons x l ih =>
    cases i with
    | zero => simp [getK]
    | succ i =>
      change getK l d i = _
      rw [ih]
      simp

theorem lenK_eq {α : Type} (l : List α) : lenK l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Nat.succ (lenK l) = _
    rw [ih]
    rfl

theorem allLK_eq {α : Type} (l : List α) (f : α → Bool) : allLK l f = l.all f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change (f x && allLK l f) = _
    rw [ih, List.all_cons]

theorem anyLK_eq {α : Type} (l : List α) (f : α → Bool) : anyLK l f = l.any f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change (f x || anyLK l f) = _
    rw [ih, List.any_cons]

theorem mapK_eq {α : Type} (f : α → ℕ) (l : List α) : mapK f l = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change f x :: mapK f l = _
    rw [ih, List.map_cons]

theorem appK_eq (l r : List ℕ) : appK l r = l ++ r := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change x :: appK l r = _
    rw [ih, List.cons_append]

theorem allN_eq (m : ℕ) (f : ℕ → Bool) : allN m f = (List.range m).all f :=
  Bool.eq_iff_iff.2 (by rw [allN_iff]; simp)

theorem beq_dec (a b : ℕ) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.2 (by rw [beq_iff]; simp)

theorem blt_dec (a b : ℕ) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.2 (by rw [blt_iff]; simp)

theorem clsIs_eq (o : Option (ℕ × ℕ)) (i : ℕ) :
    clsIs o i = decide (o.map Prod.snd = some i) := by
  cases o <;> simp [clsIs, beq_dec]

variable {n : ℕ}

theorem beq_code_dec (hn : n ≤ 32) (σ τ : Perm (Fin n)) :
    Nat.beq (code σ) (code τ) = decide (σ = τ) :=
  Bool.eq_iff_iff.2 (by rw [beq_code hn]; simp)

theorem selN_code (c : Bool) (a b : Perm (Fin n)) :
    selN c (code a) (code b) = code (if c then b else a) := by
  cases c <;> rfl

theorem code_lt (hn : n ≤ 32) (σ : Perm (Fin n)) : code σ < 2 ^ 160 := by
  rw [code_eq]
  calc E (vals σ) n < 32 ^ n := E_lt (vals_lt hn σ)
    _ ≤ 32 ^ 32 := Nat.pow_le_pow_right (by norm_num) hn
    _ = 2 ^ 160 := by norm_num

theorem evW_code (hn : n ≤ 32) (a b : Perm (Fin n)) (w : PW) :
    evW n (code a) (code b) w = code (evalPW a b w) := by
  induction w with
  | nil => exact code_one
  | cons h w ih =>
    obtain ⟨c, e⟩ := h
    change mulS n (powS n (selN c (code a) (code b)) e) (evW n (code a) (code b) w) = _
    rw [mulS_eq, powS_eq, ih, selN_code, code_pow hn, code_mul hn]
    rfl

theorem getK_code (L : List (Perm (Fin n))) (i : ℕ) :
    getK (L.map code) (one n) i = code (L.getD i 1) := by
  rw [getK_eq, code_one, List.getD_map]

theorem evI_code (hn : n ≤ 32) (L : List (Perm (Fin n))) (w : List (ℕ × ℕ)) :
    evI n (L.map code) w = code (evalIdx L w) := by
  induction w with
  | nil => exact code_one
  | cons h w ih =>
    obtain ⟨i, e⟩ := h
    change mulS n (powS n (getK (L.map code) (one n) i) e) (evI n (L.map code) w) = _
    rw [mulS_eq, powS_eq, ih, getK_code, code_pow hn, code_mul hn]
    rfl

theorem regsK_code (hn : n ≤ 32) (a b : Perm (Fin n)) (c : PGen) :
    regsK n (code a) (code b) c = (c.regs a b).map code := by
  simp [regsK, appK_eq, mapK_eq, PGen.regs, evW_code hn, Function.comp_def]

theorem prodK_code (hn : n ≤ 32) (S : ℕ → Perm (Fin n)) (l : List ℕ) :
    prodK n (fun k => code (S k)) l = code ((l.map S).prod) := by
  induction l with
  | nil => exact code_one
  | cons x l ih =>
    change mulS n (code (S x)) (prodK n (fun k => code (S k)) l) = _
    rw [mulS_eq, ih, code_mul hn, List.map_cons, List.prod_cons]

theorem checkBase_eq (hn : n ≤ 32) (a b : Perm (Fin n)) (c : PGen) :
    checkBaseK n (code a) (code b) c = PGen.checkBase a b c := by
  simp only [checkBaseK, PGen.checkBase, letB_eq, evW_code hn, allLK_eq, anyLK_eq, mulS_eq,
    powS_eq, code_pow hn, code_mul hn, code_one, beq_code_dec hn, mul_inv_eq_iff_eq_mul,
    decide_not]

theorem check_split (a b : Perm (Fin n)) (c : PGen) :
    PGen.check a b c = (PGen.checkBase a b c && decide (a = evalIdx (c.regs a b) c.wa) &&
      decide (b = evalIdx (c.regs a b) c.wb)) :=
  rfl

theorem checkK_eq (hn : n ≤ 32) (a b : Perm (Fin n)) (c : PGen) :
    checkK n (code a) (code b) c = PGen.check a b c := by
  rw [check_split, checkK, checkBase_eq hn, forceL_eq, regsK_code hn, evI_code hn, evI_code hn,
    beq_code_dec hn, beq_code_dec hn, Bool.and_assoc]

theorem lane_eq (P k : ℕ) : lane P k = P / 2 ^ (160 * k) % 2 ^ 160 := by
  have hm : (1461501637330902918203684832716283019655932542975 : ℕ) = 2 ^ 160 - 1 := by norm_num
  change (P >>> (160 * k)) &&& 1461501637330902918203684832716283019655932542975 = _
  rw [hm, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem digit_low (P y : ℕ) {k m : ℕ} (hk : k < m) :
    (P + y * 2 ^ (160 * m)) / 2 ^ (160 * k) % 2 ^ 160 = P / 2 ^ (160 * k) % 2 ^ 160 := by
  obtain ⟨d, rfl⟩ : ∃ d, m = k + 1 + d := ⟨m - k - 1, by omega⟩
  have e : y * 2 ^ (160 * (k + 1 + d)) = 2 ^ (160 * k) * (2 ^ 160 * (y * 2 ^ (160 * d))) := by
    rw [show 160 * (k + 1 + d) = 160 * k + 160 + 160 * d by ring, pow_add, pow_add]
    ring
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem digit_top (P y m : ℕ) (hP : P < 2 ^ (160 * m)) (hy : y < 2 ^ 160) :
    (P + y * 2 ^ (160 * m)) / 2 ^ (160 * m) % 2 ^ 160 = y := by
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hP, Nat.zero_add,
    Nat.mod_eq_of_lt hy]

theorem digit_bound (P y m : ℕ) (hP : P < 2 ^ (160 * m)) (hy : y < 2 ^ 160) :
    P + y * 2 ^ (160 * m) < 2 ^ (160 * (m + 1)) := by
  have e : 2 ^ (160 * (m + 1)) = 2 ^ 160 * 2 ^ (160 * m) := by
    rw [Nat.mul_succ, pow_add, Nat.mul_comm]
  rw [e]
  have h1 : (y + 1) * 2 ^ (160 * m) ≤ 2 ^ 160 * 2 ^ (160 * m) :=
    Nat.mul_le_mul_right _ hy
  calc P + y * 2 ^ (160 * m) < 2 ^ (160 * m) + y * 2 ^ (160 * m) := Nat.add_lt_add_right hP _
    _ = (y + 1) * 2 ^ (160 * m) := by ring
    _ ≤ _ := h1

theorem elemsAux_length (c : PSimple) (g1 g2 : Perm (Fin n)) (m : ℕ) :
    (c.elemsAux g1 g2 m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [PSimple.elemsAux, ih]

theorem elemsP_succ (c : PSimple) (g1 g2 m : ℕ) :
    elemsP n c g1 g2 (m + 1) = elemsP n c g1 g2 m +
      Bool.rec (motive := fun _ => ℕ)
        (mulS n (laneD n (elemsP n c g1 g2 m) m (getK c.par 0 m)) (selN (getK c.gen false m) g1 g2))
        (one n) (Nat.beq m 0) * 2 ^ (160 * m) := by
  have e : elemsP n c g1 g2 (m + 1) = letN (elemsP n c g1 g2 m) fun P => Nat.add P (Nat.shiftLeft
      (Bool.rec (motive := fun _ => Nat)
        (mulS n (laneD n P m (getK c.par (nat_lit 0) m)) (selN (getK c.gen false m) g1 g2))
        (one n) (Nat.beq m (nat_lit 0)))
      (Nat.mul (nat_lit 160) m)) := rfl
  rw [e, letN_eq]
  change _ + _ <<< (160 * m) = _
  rw [Nat.shiftLeft_eq]

theorem elemsP_spec (hn : n ≤ 32) (c : PSimple) (g1 g2 : Perm (Fin n)) (m : ℕ) :
    elemsP n c (code g1) (code g2) m < 2 ^ (160 * m) ∧
      ∀ k, laneD n (elemsP n c (code g1) (code g2) m) m k = code ((c.elemsAux g1 g2 m).getD k 1) := by
  induction m with
  | zero =>
    refine ⟨by norm_num [elemsP], fun k => ?_⟩
    simp [laneD, PSimple.elemsAux, code_one, blt_dec]
  | succ m ih =>
    obtain ⟨hb, hl⟩ := ih
    set P := elemsP n c (code g1) (code g2) m
    set s := c.elemsAux g1 g2 m
    have hlen : s.length = m := elemsAux_length c g1 g2 m
    set x : Perm (Fin n) := if m = 0 then 1 else
      s.getD (c.par.getD m 0) 1 * (if c.gen.getD m false then g2 else g1) with hx
    have hs : c.elemsAux g1 g2 (m + 1) = s ++ [x] := by
      simp only [PSimple.elemsAux, s, x]
    have hy : Bool.rec (motive := fun _ => ℕ)
        (mulS n (laneD n P m (getK c.par 0 m)) (selN (getK c.gen false m) (code g1) (code g2)))
        (one n) (Nat.beq m 0) = code x := by
      by_cases hm : m = 0
      · subst hm
        simp [x, code_one]
      · have hb0 : Nat.beq m 0 = false := by
          rw [beq_dec]
          simpa using hm
        rw [hb0]
        change mulS n _ _ = _
        rw [mulS_eq, hl, getK_eq, getK_eq, selN_code, code_mul hn]
        simp [x, hm]
    rw [elemsP_succ, hy]
    have hxl := code_lt hn x
    refine ⟨digit_bound P _ m hb hxl, fun k => ?_⟩
    rw [hs]
    simp only [laneD]
    rcases Nat.lt_trichotomy k m with h | rfl | h
    · have hk : Nat.blt k (m + 1) = true := blt_iff.2 (by omega)
      rw [hk]
      change lane _ k = _
      rw [lane_eq, digit_low P _ h, ← lane_eq]
      have := hl k
      have hkm : Nat.blt k m = true := blt_iff.2 h
      simp only [laneD, hkm] at this
      change lane P k = _ at this
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have hk : Nat.blt k (k + 1) = true := blt_iff.2 (by omega)
      rw [hk]
      change lane _ k = _
      rw [lane_eq, digit_top P _ k hb hxl, List.getD_append_right _ _ _ _ (by omega)]
      simp [hlen]
    · have hk : Nat.blt k (m + 1) = false := by
        rw [blt_dec]
        simp only [decide_eq_false_iff_not, not_lt]
        omega
      rw [hk, code_one]
      congr 1
      rw [List.getD_eq_default _ _ (by simp [hlen]; omega)]

theorem laneD_elems (hn : n ≤ 32) (c : PSimple) (g1 g2 : Perm (Fin n)) :
    laneD n (elemsP n c (code g1) (code g2) c.par.length) c.par.length =
      fun k => code ((c.elems g1 g2).getD k 1) :=
  funext (elemsP_spec hn c g1 g2 c.par.length).2

theorem check_match (o : Option (ℕ × ℕ)) (A : Bool) (B : ℕ → ℕ → Bool) :
    PSimple.check.match_1 (motive := fun _ => Bool) o (fun _ => A) B =
      Option.rec (motive := fun _ => Bool) A (fun p => B p.1 p.2) o := by
  rcases o with _ | ⟨u, i⟩ <;> rfl

theorem simpleK_eq (hn : n ≤ 32) (c : PSimple) (g1 g2 z : Perm (Fin n)) :
    simpleK n c (code g1) (code g2) (code z) = c.check g1 g2 z := by
  simp only [simpleK, letB_eq, lenK_eq]
  rw [laneD_elems hn]
  simp only [PSimple.check, rowK, ncK, allN_eq, allLK_eq, getK_eq, lenK_eq, mulS_eq, powS_eq,
    code_pow hn, code_mul hn, code_one, beq_code_dec hn, beq_dec, blt_dec, decide_not,
    prodK_code hn, clsIs_eq, Bool.decide_or, check_match]

theorem secK_eq (hn : n ≤ 32) (a b : Perm (Fin n)) (c : PSec) :
    secK n (code a) (code b) c = PSec.check canonPerm a b c := by
  rw [secK, PSec.check, checkBase_eq hn, forceL_eq, regsK_code hn]
  simp only [letB_eq, evI_code hn, evW_code hn, simpleK_eq hn, canonPerm_eq]

end CFSG.KC.FongPerm
