module

public import Certificates.Data.Kernel.Misc.L52
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KC.L52

open CFSG.Quasithin.H13.KGE64 CFSG.KD.L52

def Rep (L : List Bool) (X : ℕ) : Prop := ∀ i < 5, ∀ j < 5, m5 L i j = X.testBit (5 * i + j)

theorem all_congr' {α : Type} {f g : α → Bool} :
    ∀ (L : List α), (∀ x ∈ L, f x = g x) → L.all f = L.all g
  | [], _ => rfl
  | a :: L, h => by
    rw [List.all_cons, List.all_cons, h a (by simp),
      all_congr' L (fun x hx => h x (by simp [hx]))]

theorem map_rel {α β γ : Type} {R : β → γ → Prop} {f : α → β} {g : α → γ}
    (h : ∀ x, R (f x) (g x)) : ∀ L : List α, List.Forall₂ R (L.map f) (L.map g)
  | [] => .nil
  | a :: L => .cons (h a) (map_rel h L)

theorem filter_rel {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, R a b → p a = q b) :
    ∀ {L : List α} {M : List β}, List.Forall₂ R L M → List.Forall₂ R (L.filter p) (M.filter q)
  | _, _, .nil => .nil
  | _, _, .cons (a := a) (b := b) h t => by
    rw [List.filter_cons, List.filter_cons, hpq a b h]
    split
    · exact .cons h (filter_rel hpq t)
    · exact filter_rel hpq t

theorem all_rel {α β : Type} {R : α → β → Prop} {f : α → Bool} {g : β → Bool}
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {L : List α} {M : List β}, List.Forall₂ R L M → L.all f = M.all g
  | _, _, .nil => rfl
  | _, _, .cons (a := a) (b := b) h t => by
    rw [List.all_cons, List.all_cons, hfg a b h, all_rel hfg t]

theorem testBit_pkR (f : ℕ → Bool) : ∀ n p, (pkR f n).testBit p = (decide (p < n) && f p)
  | 0, p => by
    change (0 : ℕ).testBit p = _
    simp
  | n + 1, p => by
    change ((pkR f n) ||| (bif f n then 1 <<< n else 0)).testBit p = _
    rw [Nat.testBit_or, testBit_pkR f n p]
    have e : (bif f n then 1 <<< n else 0).testBit p = (f n && decide (n = p)) := by
      cases f n
      · simp
      · simp [Nat.shiftLeft_eq, Nat.testBit_two_pow]
    rw [e]
    by_cases hp : p = n
    · subst hp
      simp
    · have h1 : decide (p < n + 1) = decide (p < n) := by
        apply Bool.eq_iff_iff.2
        simp only [decide_eq_true_eq]
        omega
      have h2 : decide (n = p) = false := by simp [Ne.symm hp]
      rw [h1, h2, Bool.and_false, Bool.or_false]

theorem testBit_pkF (f : ℕ → Bool) {p : ℕ} (hp : p < 25) : (pkF f).testBit p = f p := by
  rw [pkF, testBit_pkR, decide_eq_true hp, Bool.true_and]

theorem m5_map (f : ℕ → Bool) {i j : ℕ} (hi : i < 5) (hj : j < 5) :
    m5 ((List.range 25).map f) i j = f (5 * i + j) := by
  have hp : 5 * i + j < 25 := by omega
  simp [m5, List.getD_eq_getElem?_getD, hp]

theorem rep_map (f : ℕ → Bool) : Rep ((List.range 25).map f) (pkF f) := by
  intro i hi j hj
  rw [m5_map f hi hj, testBit_pkF f (by omega)]

theorem rep_nil : Rep [] 0 := by
  intro i _ j _
  simp [m5]

theorem testBit_31 (j : ℕ) : Nat.testBit 31 j = decide (j < 5) := by
  have h := Nat.testBit_two_pow_sub_one 5 j
  simpa using h

theorem lor_eq (a b : ℕ) : Nat.lor a b = a ||| b := rfl
theorem xor_eq (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
theorem land_eq (a b : ℕ) : Nat.land a b = a &&& b := rfl
theorem shiftLeft_eq' (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl
theorem shiftRight_eq' (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl

theorem testBit_selN (A i k B j : ℕ) :
    (selN A i k B).testBit j = (decide (j < 5) && A.testBit (5 * i + k) && B.testBit (5 * k + j)) := by
  unfold selN rowN
  simp only [Nat.add_eq, Nat.mul_eq, land_eq, shiftRight_eq']
  cases A.testBit (5 * i + k)
  · simp
  · simp only [cond_true, Nat.testBit_and, Nat.testBit_shiftRight, testBit_31, Bool.and_true]
    rw [Bool.and_comm]

theorem mMulN_bit (X Y : ℕ) {i j : ℕ} (hi : i < 5) (hj : j < 5) :
    (mMulN X Y).testBit (5 * i + j) =
      ((X.testBit (5 * i + 0) && Y.testBit (5 * 0 + j)) ^^
        (X.testBit (5 * i + 1) && Y.testBit (5 * 1 + j)) ^^
        (X.testBit (5 * i + 2) && Y.testBit (5 * 2 + j)) ^^
        (X.testBit (5 * i + 3) && Y.testBit (5 * 3 + j)) ^^
        (X.testBit (5 * i + 4) && Y.testBit (5 * 4 + j))) := by
  interval_cases i <;> interval_cases j <;>
    simp only [mMulN, prodRowN, lor_eq, xor_eq, shiftLeft_eq', Nat.testBit_or, Nat.testBit_xor,
      Nat.testBit_shiftLeft, testBit_selN] <;> simp

theorem rep_mMul {A B : List Bool} {X Y : ℕ} (hA : Rep A X) (hB : Rep B Y) :
    Rep (mMul A B) (mMulN X Y) := by
  intro i hi j hj
  rw [mMul, m5_map _ hi hj, mMulN_bit X Y hi hj]
  have hp1 : (5 * i + j) / 5 = i := by omega
  have hp2 : (5 * i + j) % 5 = j := by omega
  simp only [hp1, hp2]
  rw [hA i hi 0 (by norm_num), hA i hi 1 (by norm_num), hA i hi 2 (by norm_num),
    hA i hi 3 (by norm_num), hA i hi 4 (by norm_num), hB 0 (by norm_num) j hj,
    hB 1 (by norm_num) j hj, hB 2 (by norm_num) j hj, hB 3 (by norm_num) j hj,
    hB 4 (by norm_num) j hj]

theorem rep_mId : Rep mId mIdN := rep_map _

theorem rep_mPow {A : List Bool} {X : ℕ} (hA : Rep A X) : ∀ k, Rep (mPow A k) (mPowN X k)
  | 0 => rep_mId
  | k + 1 => rep_mMul hA (rep_mPow hA k)

theorem rep_ofCode (l : List Bool) : Rep (ofCode l) (ofCodeN l) := rep_map _

theorem rep_l52Y (j : ℕ) : Rep (l52Y j) (l52YN j) := rep_map _

theorem rep_mEq {A B : List Bool} {X Y : ℕ} (hA : Rep A X) (hB : Rep B Y) :
    mEq A B = mEqN X Y := by
  unfold mEq mEqN
  refine all_congr' _ fun i hi => all_congr' _ fun j hj => ?_
  rw [List.mem_range] at hi hj
  rw [hA i hi j hj, hB i hi j hj]

theorem rep_isUT {A : List Bool} {X : ℕ} (hA : Rep A X) : isUT A = isUTN X := by
  unfold isUT isUTN
  refine all_congr' _ fun i hi => all_congr' _ fun j hj => ?_
  rw [List.mem_range] at hi hj
  rw [hA i hi j hj]

def RepL (pw : List (List Bool)) (pwN : List ℕ) : Prop := ∀ i, Rep (pw.getD i []) (pwN.getD i 0)

theorem rep_pw {g : ℕ → List Bool} {gN : ℕ → ℕ} (h : ∀ m, Rep (g m) (gN m)) :
    RepL ((List.range 8).map g) ((List.range 8).map gN) := by
  intro i
  rcases Nat.lt_or_ge i 8 with hi | hi
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    exact h i
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simpa using hi), List.getElem?_eq_none (by simpa using hi),
      Option.getD_none, Option.getD_none]
    exact rep_nil

theorem rep_cj5 {pw : List (List Bool)} {pwN : List ℕ} (hp : RepL pw pwN) {a : List Bool} {X : ℕ}
    (ha : Rep a X) (i : ℕ) : Rep (cj5 pw a i) (cj5N pwN X i) :=
  rep_mMul (rep_mMul (hp i) ha) (hp (7 - i))

theorem condA5_eq {pw : List (List Bool)} {pwN : List ℕ} (hp : RepL pw pwN) {a : List Bool}
    {X : ℕ} (ha : Rep a X) : condA5 pw a = condA5N pwN X := by
  unfold condA5 condA5N
  rw [rep_mEq ha rep_mId, rep_mEq (rep_mMul ha ha) rep_mId,
    rep_mEq (rep_mMul (rep_mMul (rep_cj5 hp ha 3) (rep_cj5 hp ha 1)) ha) rep_mId]

theorem condB5_eq {pw : List (List Bool)} {pwN : List ℕ} (hp : RepL pw pwN) {b : List Bool}
    {Y : ℕ} (hb : Rep b Y) : condB5 pw b = condB5N pwN Y := by
  unfold condB5 condB5N
  rw [rep_mEq hb rep_mId, rep_mEq (rep_mMul hb hb) rep_mId,
    rep_mEq (rep_mMul (rep_mMul (rep_cj5 hp hb 3) (rep_cj5 hp hb 2)) hb) rep_mId]

theorem commAll5_eq {pw : List (List Bool)} {pwN : List ℕ} (hp : RepL pw pwN) {a b : List Bool}
    {X Y : ℕ} (ha : Rep a X) (hb : Rep b Y) : commAll5 pw a b = commAll5N pwN X Y := by
  unfold commAll5 commAll5N
  refine all_congr' _ fun i _ => all_congr' _ fun j _ => ?_
  exact rep_mEq (rep_mMul (rep_cj5 hp ha i) (rep_cj5 hp hb j))
    (rep_mMul (rep_cj5 hp hb j) (rep_cj5 hp ha i))

theorem l52CheckY_eq {y : List Bool} {Y : ℕ} (hy : Rep y Y) : l52CheckY y = l52CheckYN Y := by
  unfold l52CheckY l52CheckYN
  refine all_congr' _ fun k _ => ?_
  unfold l52StepN
  have hp : RepL ((List.range 8).map (mPow (mPow y k))) ((List.range 8).map (mPowN (mPowN Y k))) :=
    rep_pw fun m => rep_mPow (rep_mPow hy k) m
  have hc := filter_rel (p := fun u => (List.range' 1 6).all fun i =>
      isUT (cj5 ((List.range 8).map (mPow (mPow y k))) u i))
    (q := fun u => (List.range' 1 6).all fun i =>
      isUTN (cj5N ((List.range 8).map (mPowN (mPowN Y k))) u i))
    (fun a X ha => all_congr' _ fun i _ => rep_isUT (rep_cj5 hp ha i))
    (map_rel rep_ofCode (bools 10))
  exact all_rel (fun a X ha => all_rel (fun b Y hb => by rw [commAll5_eq hp ha hb])
      (filter_rel (fun b Y hb => condB5_eq hp hb) hc))
    (filter_rel (fun a X ha => condA5_eq hp ha) hc)

theorem l52Check_eq : l52Check = l52CheckN := by
  unfold l52Check l52CheckN
  refine all_congr' _ fun j _ => ?_
  rw [rep_mEq (rep_mPow (rep_l52Y j) 7) rep_mId, l52CheckY_eq (rep_l52Y j)]

end CFSG.KC.L52

end
