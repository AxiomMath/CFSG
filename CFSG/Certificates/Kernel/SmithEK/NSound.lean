module

public import Certificates.Data.Kernel.SmithEKN
public import CFSG.Certificates.Kernel.SmithEK.OSound

public section

namespace CFSG.SmithE.K

open CFSG.KC.Misc.O73 CFSG.KS.PK CFSG.KC.Misc

@[expose] noncomputable def ivUnpack (p : Nat) : Array Nat :=
  Array.ofFn (n := 21) fun k => at' 5 p k.val

theorem recAll2_iff (p q : Nat → Bool) (n : Nat) :
    Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && p k && q k) n = true ↔
      ∀ k < n, p k = true ∧ q k = true := by
  have e : ∀ n, Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && p k && q k) n =
      Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && (p k && q k)) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact (congrArg (fun b => b && p n && q n) ih).trans (Bool.and_assoc _ _ _)
  rw [e, recAll_iff]
  simp only [Bool.and_eq_true]

theorem recAll_false (p : Nat → Bool) (n : Nat) :
    Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && p k) n = false ↔
      ∃ k < n, p k = false := by
  rw [← Bool.not_eq_true, recAll_iff]
  constructor
  · intro h
    refine Classical.byContradiction fun hne => h fun k hk => ?_
    cases hpk : p k
    · exact absurd ⟨k, hk, hpk⟩ hne
    · rfl
  · rintro ⟨k, hk, hpk⟩ hall
    rw [hall k hk] at hpk
    exact Bool.noConfusion hpk

theorem ivBits_eq (m : Nat) (f : Nat → List Nat → List Nat) (t : List Nat) :
    ivBits m f t =
      (List.range 21).foldr (fun k t => if m.testBit k = true then f k t else t) t := by
  have key : ∀ n t, Nat.rec (motive := fun _ => List Nat → List Nat) (fun t => t)
      (fun k ih t => ih (bif bitK m k then f k t else t)) n t =
      (List.range n).foldr (fun k t => if m.testBit k = true then f k t else t) t := by
    intro n
    induction n with
    | zero => intro t; rfl
    | succ n ih =>
      intro t
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]
      refine (ih _).trans ?_
      rw [bitK_eq]
      cases m.testBit n <;> rfl
  unfold ivBits
  rw [letLN_eq]
  exact key 21 t

theorem ivBits_app (m : Nat) {f : Nat → List Nat → List Nat} (g : Nat → List Nat)
    (hf : ∀ k t, f k t = g k ++ t) (t : List Nat) :
    ivBits m f t =
      ((List.range 21).flatMap fun k => if m.testBit k = true then g k else []) ++ t := by
  rw [ivBits_eq]
  generalize List.range 21 = L
  induction L with
  | nil => rfl
  | cons k L ih =>
    rw [List.foldr_cons, ih, List.flatMap_cons, List.append_assoc]
    split <;> simp [hf]

theorem ivLow_eq (m : Nat) : ivLow m = ((List.range 21).find? fun z => m.testBit z).getD 0 := by
  have key : ∀ n, n ≤ 21 → Nat.rec (motive := fun _ => Nat) 0
      (fun k acc => bif bitK m (Nat.sub 20 k) then Nat.sub 20 k else acc) n =
      ((List.range' (21 - n) n).find? fun z => m.testBit z).getD 0 := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      have e : 21 - (n + 1) = 20 - n := by omega
      have e2 : 20 - n + 1 = 21 - n := by omega
      have ih' := ih (by omega)
      change (bif bitK m (20 - n) then 20 - n else Nat.rec (motive := fun _ => Nat) 0
        (fun k acc => bif bitK m (Nat.sub 20 k) then Nat.sub 20 k else acc) n) = _
      rw [ih', e, List.range'_succ, e2, bitK_eq, List.find?_cons]
      cases m.testBit (20 - n) <;> rfl
  unfold ivLow
  rw [key 21 (Nat.le_refl 21), List.range_eq_range']

theorem ivFind_congr {p q : Nat → Bool} : ∀ {l : List Nat}, (∀ x ∈ l, p x = q x) →
    l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.find?_cons, List.find?_cons, h x List.mem_cons_self,
      ivFind_congr fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem ivLm_sound {CP S2 LI LM : Nat} (h : ivLm CP S2 LI LM = true) {a b : Nat} (ha : a < 21)
    (hb : b < 21) : at' 6 LI (21 * a + b) < 42 ∧
      ∀ z < 21, (ivLn LI LM a b).testBit z = ivP CP S2 z a b := by
  unfold ivLm at h
  rw [recAll_iff] at h
  have h2 := h a ha
  rw [recAll2_iff] at h2
  obtain ⟨h3, h4⟩ := h2 b hb
  rw [recAll_iff] at h4
  rw [Nat.blt_eq] at h3
  refine ⟨h3, fun z hz => ?_⟩
  have h5 := h4 z hz
  rw [beq_iff_eq, bitK_eq] at h5
  exact h5

theorem ivMp_sound {LM MP : Nat} (h : ivMp LM MP = true) {i j : Nat} (hi : i < 42) (hj : j < 42) :
    at' 5 MP (42 * i + j) = ivLow (at' 21 LM i &&& at' 21 LM j) := by
  unfold ivMp at h
  rw [recAll_iff] at h
  have h2 := h i hi
  rw [recAll_iff] at h2
  exact Nat.eq_of_beq_eq_true (h2 j hj)

theorem ivMeet_eq {CP S2 LI LM MP : Nat} (hlm : ivLm CP S2 LI LM = true) (hmp : ivMp LM MP = true)
    {a b c d : Nat} (ha : a < 21) (hb : b < 21) (hc : c < 21) (hd : d < 21) :
    ivMeet LI MP a b c d =
      ((List.range 21).find? fun z => ivP CP S2 z a b && ivP CP S2 z c d).getD 0 := by
  obtain ⟨h1, h2⟩ := ivLm_sound hlm ha hb
  obtain ⟨h3, h4⟩ := ivLm_sound hlm hc hd
  refine (ivMp_sound hmp h1 h3).trans ?_
  rw [ivLow_eq]
  congr 1
  refine ivFind_congr fun z hz => ?_
  have hz' := List.mem_range.1 hz
  rw [Nat.testBit_and]
  exact congr (congrArg (· && ·) (h2 z hz')) (h4 z hz')

theorem at'_foldr (w : Nat) : ∀ (l : List Nat), (∀ x ∈ l, x < 2 ^ w) → ∀ k,
    at' w (l.foldr (fun x acc => x + 2 ^ w * acc) 0) k = l.getD k 0
  | [], _, k => by
    rw [at'_eq]
    exact fd_zero _ _
  | x :: l, h, k => by
    have hx : x < 2 ^ w := h x List.mem_cons_self
    have e : (x :: l).foldr (fun x acc => x + 2 ^ w * acc) 0 =
        x + l.foldr (fun x acc => x + 2 ^ w * acc) 0 * 2 ^ w := by
      rw [List.foldr_cons, Nat.mul_comm]
    rw [at'_eq, e]
    cases k with
    | zero => rw [fd_cons_zero hx, List.getD_cons_zero]
    | succ k =>
      rw [fd_cons hx, ← at'_eq, at'_foldr w l (fun y hy => h y (List.mem_cons_of_mem _ hy)) k,
        List.getD_cons_succ]

theorem ivPack_eq : ∀ l : List Nat, ivPack l = l.foldr (fun x acc => x + 2 ^ 5 * acc) 0
  | [] => rfl
  | x :: l => by
    rw [List.foldr_cons, ← ivPack_eq l]
    rfl

theorem at'_ivPack {l : List Nat} (h : ∀ x ∈ l, x < 32) (k : Nat) :
    at' 5 (ivPack l) k = l.getD k 0 := by
  rw [ivPack_eq]
  exact at'_foldr 5 l h k

theorem ivUnpack_ivPack {l : List Nat} (hl : l.length = 21) (h : ∀ x ∈ l, x < 32) :
    ivUnpack (ivPack l) = l.toArray := by
  unfold ivUnpack
  refine Array.ext (by simp [hl]) fun k hk _ => ?_
  rw [Array.getElem_ofFn, at'_ivPack h, List.getElem_toArray, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem]
  rfl

theorem ivGet_eq : ∀ (l : List Nat) (k : Nat), ivGet l k = l.getD k 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: l, k + 1 => by
    rw [List.getD_cons_succ, ← ivGet_eq l k]
    rfl

theorem ivBack_of_inv {l : List Nat} (h : ∀ k < 21, l.getD (l.getD k 0) 0 = k) :
    ivBack l = true := by
  unfold ivBack
  simp only [ivGet_eq, h 0 (by omega), h 1 (by omega), h 4 (by omega), h 10 (by omega),
    h 3 (by omega), Nat.beq_refl, Bool.and_self]

theorem testBit_orRec (f : Nat → Nat) (n j : Nat) :
    (Nat.rec (motive := fun _ => Nat) 0
      (fun k acc => Nat.lor acc (Nat.shiftLeft 1 (f k))) n).testBit j = true ↔
      ∃ k < n, f k = j := by
  induction n with
  | zero =>
    change (0 : Nat).testBit j = true ↔ _
    simp
  | succ n ih =>
    change ((Nat.rec (motive := fun _ => Nat) 0
      (fun k acc => Nat.lor acc (Nat.shiftLeft 1 (f k))) n) ||| (1 <<< f n)).testBit j
      = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_iff]
    constructor
    · rintro (⟨k, hk, h⟩ | h)
      · exact ⟨k, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact Or.inl ⟨k, hk, h⟩
      · exact Or.inr h

theorem ivInv_iff {CP : Nat} {l : List Nat} (hlt : ∀ x ∈ l, x < 21) :
    ivInv CP (ivPack l) = true ↔ (∀ k < 21, l.getD (l.getD k 0) 0 = k) ∧
      (∃ k < 21, l.getD k 0 ≠ k) ∧
      ∀ k < 21, ivAmat CP (ivPack l) (at' 9 CP k) = at' 9 CP (l.getD k 0) := by
  have hp : ∀ k, at' 5 (ivPack l) k = l.getD k 0 :=
    at'_ivPack fun x hx => by have := hlt x hx; omega
  have hlt' : ∀ k < 21, l.getD k 0 < 21 := by
    intro k _
    rw [List.getD_eq_getElem?_getD]
    cases h : l[k]? with
    | none => simp
    | some x => exact hlt x (List.mem_of_getElem? h)
  have hbf : ∀ x y : Nat, Nat.beq x y = false ↔ ¬x = y := fun x y => by
    rw [← Bool.not_eq_true, Nat.beq_eq]
  unfold ivInv
  rw [letB_eq]
  simp only [Bool.and_eq_true, Bool.not_eq_true', recAll_iff, recAll_false, hp, Nat.beq_eq,
    Nat.blt_eq, hbf, ne_eq]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩
    exact ⟨h1, h2, h5⟩
  · rintro ⟨h1, h2, h5⟩
    refine ⟨⟨⟨⟨h1, h2⟩, hlt'⟩, ?_⟩, h5⟩
    apply Nat.eq_of_testBit_eq
    intro j
    have e : (2097151 : Nat) = 2 ^ 21 - 1 := by decide
    rw [e, Nat.testBit_two_pow_sub_one]
    by_cases hj : j < 21
    · rw [decide_eq_true hj, testBit_orRec]
      exact ⟨l.getD j 0, hlt' j hj, h1 j hj⟩
    · rw [decide_eq_false hj, Bool.eq_false_iff, Ne, testBit_orRec]
      rintro ⟨k, hk, rfl⟩
      exact hj (hlt' k hk)

theorem ivBits_app' (m : Nat) (g : Nat → List Nat) (t : List Nat) :
    ivBits m (fun k t => g k ++ t) t =
      ((List.range 21).flatMap fun k => if m.testBit k = true then g k else []) ++ t :=
  ivBits_app m g (fun _ _ => rfl) t

theorem ivGrp_leaf (CP : Nat) (l t : List Nat) :
    (bif ivBack l then (bif ivInv CP (ivPack l) then ivPack l :: t else t) else t) =
      (if (ivBack l && ivInv CP (ivPack l)) = true then [ivPack l] else []) ++ t := by
  cases ivBack l <;> cases ivInv CP (ivPack l) <;> rfl

theorem ivGrp_eq (CP LI LM MP y0 : Nat) : ivGrp CP LI LM MP y0 [] =
    (List.range 21).flatMap fun y1 =>
      if (Nat.xor ivAll (Nat.shiftLeft 1 y0)).testBit y1 = true then
      (List.range 21).flatMap fun y2 =>
        if (Nat.xor ivAll (ivLn LI LM y0 y1)).testBit y2 = true then
        (List.range 21).flatMap fun y3 =>
          if (Nat.xor ivAll (Nat.lor (ivLn LI LM y0 y1)
              (Nat.lor (ivLn LI LM y0 y2) (ivLn LI LM y1 y2)))).testBit y3 = true then
          (List.range 21).flatMap fun y4 =>
            if (Nat.land (Nat.xor (ivLn LI LM y0 y1) (Nat.lor (Nat.shiftLeft 1 y0)
                (Nat.shiftLeft 1 y1))) (Nat.xor ivAll (ivLn LI LM y2 y3))).testBit y4 = true then
              (if (ivBack (ivList LI MP y0 y1 y2 y3 y4) &&
                  ivInv CP (ivPack (ivList LI MP y0 y1 y2 y3 y4))) = true then
                [ivPack (ivList LI MP y0 y1 y2 y3 y4)] else [])
            else []
          else []
        else []
      else [] := by
  unfold ivGrp
  simp only [letLN_eq, ivGrp_leaf, ivBits_app', List.append_nil]

end CFSG.SmithE.K
