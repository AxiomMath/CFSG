module

public import Certificates.Data.Kernel.SmithEKE
public import CFSG.LargeExtraspecial.S14SMKE23aCheck
public import CFSG.Certificates.Kernel.SmithL6KWedge
public import CFSG.Certificates.Kernel.SmithEK.SpanSound

public section

namespace CFSG.SmithE.K

open CFSG.SmithE

theorem c8ap_eq (A : List Nat) (x : Nat) : c8ap A x = applyL A x := by
  induction A generalizing x with
  | nil => rfl
  | cons c l ih =>
    have e : c8ap (c :: l) x = c * (x % 2) ^^^ c8ap l (x / 2) := rfl
    have e2 : applyL (c :: l) x = (if x.testBit 0 then c else 0) ^^^ applyL l (x / 2) := rfl
    rw [e, e2, ih]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [Nat.testBit_zero, h]

theorem c8ap_xor (A : List Nat) (a b : Nat) : c8ap A (a ^^^ b) = c8ap A a ^^^ c8ap A b := by
  simp only [c8ap_eq, applyL_xor]

theorem applyCols_arr (X : Array Nat) (c : Nat) : applyCols X c = c8ap X.toList c := by
  rw [c8ap_eq, ← applyCols_toArray, Array.toArray_toList]

theorem arr_get (a : Array Nat) (i : Nat) : a[i]! = a.toList.getD i 0 := by
  rw [← getElem!_toArray, Array.toArray_toList]

theorem arr_contains (a : Array Nat) (s : Nat) : a.contains s = a.toList.contains s := by
  rw [Bool.eq_iff_iff]
  simp

theorem commuteB_toArray (A B : List Nat) : commuteB A.toArray B.toArray = c8comm A B := by
  unfold commuteB c8comm
  simp only [getElem!_toArray, applyCols_arr, List.toList_toArray]

theorem zip_map_self (f : Nat → List Nat) :
    ∀ l : List Nat, l.zip (l.map f) = l.map fun r => (r, f r)
  | [] => rfl
  | r :: l => by
    rw [List.map_cons, List.zip_cons_cons, zip_map_self f l, List.map_cons]

theorem c8_split {c : Nat} (hc : c < 2 ^ 20) : (c &&& 255) ^^^ (c &&& 1048320) = c := by
  rw [← Nat.and_xor_distrib_left, (by decide : (255 ^^^ 1048320 : Nat) = 2 ^ 20 - 1),
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hc]

theorem xorAdd_zero {F : Nat → Nat} (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b) : F 0 = 0 := by
  have h := hF 0 0
  rw [Nat.xor_self] at h
  rw [h, Nat.xor_self]

theorem c8_low {F : Nat → Nat} (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b)
    (h8 : ∀ m < 8, F (2 ^ m) = 2 ^ m) : ∀ c < 2 ^ 20, F (c &&& 255) = c &&& 255 := by
  refine CFSG.SmithL6.K.xorAdd_ext (F := fun c => F (c &&& 255)) (G := fun c => c &&& 255)
    (fun a b => by simp only [Nat.and_xor_distrib_right, hF])
    (fun a b => Nat.and_xor_distrib_right) 20 fun m hm => ?_
  have key : ∀ m < 20, (2 ^ m &&& 255 = 2 ^ m ∧ m < 8) ∨ 2 ^ m &&& 255 = 0 := by
    decide
  rcases key m hm with ⟨h1, h2⟩ | h1
  · simp only [h1]
    exact h8 m h2
  · simp only [h1]
    exact xorAdd_zero hF

theorem c8_high (c : Nat) :
    c &&& 1048320 = 256 * ((c &&& 1048320) / 256) ∧ (c &&& 1048320) / 256 < 4096 := by
  have h1 : (c &&& 1048320) % 256 = 0 := by
    have e : (1048320 : Nat) &&& (2 ^ 8 - 1) = 0 := by decide
    rw [(by decide : (256 : Nat) = 2 ^ 8), ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc, e,
      Nat.and_zero]
  have h2 : c &&& 1048320 ≤ 1048320 := Nat.and_le_right
  omega

theorem c8_lt_iff {c : Nat} (hc : c < 2 ^ 20) : c < 256 ↔ c &&& 1048320 = 0 := by
  constructor
  · intro h
    have e : c &&& 255 = c := by
      rw [(by decide : (255 : Nat) = 2 ^ 8 - 1), Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt h]
    rw [← e, Nat.and_assoc, (by decide : (255 &&& 1048320 : Nat) = 0), Nat.and_zero]
  · intro h
    have e := c8_split hc
    rw [h, Nat.xor_zero] at e
    rw [← e]
    exact lt_of_le_of_lt Nat.and_le_right (by decide)

theorem c8_xor_cancel {a x y : Nat} (h : a ^^^ x = a ^^^ y) : x = y := by
  have := congrArg (a ^^^ ·) h
  simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this
  exact this

theorem c8_fix_iff {F : Nat → Nat} (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b)
    (h8 : ∀ m < 8, F (2 ^ m) = 2 ^ m) {c : Nat} (hc : c < 2 ^ 20) :
    F c = c ↔ F (c &&& 1048320) = c &&& 1048320 := by
  have e : F c = (c &&& 255) ^^^ F (c &&& 1048320) := by
    conv_lhs => rw [← c8_split hc]
    rw [hF, c8_low hF h8 c hc]
  rw [e]
  constructor
  · intro h
    conv_rhs at h => rw [← c8_split hc]
    exact c8_xor_cancel h
  · intro h
    rw [h]
    exact c8_split hc

theorem c8_fixed {F G : Nat → Nat} (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b)
    (hG : ∀ a b, G (a ^^^ b) = G a ^^^ G b) (hF8 : ∀ m < 8, F (2 ^ m) = 2 ^ m)
    (hG8 : ∀ m < 8, G (2 ^ m) = 2 ^ m)
    (hlow : ∀ j < 4096, (F (256 * j) = 256 * j ∧ G (256 * j) = 256 * j) ↔ j = 0)
    {c : Nat} (hc : c < 2 ^ 20) : (F c = c ∧ G c = c) ↔ c < 256 := by
  obtain ⟨hr, hj⟩ := c8_high c
  rw [c8_fix_iff hF hF8 hc, c8_fix_iff hG hG8 hc, c8_lt_iff hc, hr, hlow _ hj]
  omega

theorem rig_low {A : List Nat} (h8 : ∀ m < 8, c8ap A (2 ^ m) = 2 ^ m) {e : Nat}
    (he : e < 2 ^ 20) :
    c8ap A e ^^^ e =
      c8ap A (256 * ((e &&& 1048320) / 256)) ^^^ 256 * ((e &&& 1048320) / 256) := by
  rw [← (c8_high e).1]
  conv_lhs => rw [← c8_split he]
  rw [c8ap_xor, c8_low (c8ap_xor A) h8 e he]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases (e &&& 255).testBit i <;> cases (c8ap A (e &&& 1048320)).testBit i <;>
    cases (e &&& 1048320).testBit i <;> rfl

section Cols

variable {C : List (List Nat)} (hC : ∀ k, tvArr[k]! = (C.getD k []).toArray)
include hC

theorem ap_tv (k x : Nat) : applyCols tvArr[k]! x = c8ap (C.getD k []) x := by
  rw [hC, applyCols_arr, List.toList_toArray]

theorem comm_tv (j k : Nat) : commuteB tvArr[j]! tvArr[k]! = c8comm (C.getD j []) (C.getD k []) := by
  rw [hC, hC, commuteB_toArray]

theorem chkC8Pts_of (h : c8PtsK (C.getD 0 []) (C.getD 1 []) (c8Q C) = true) :
    chkC8Pts = true := by
  unfold c8PtsK c8Q at h
  rw [List.all_map] at h
  simp only [Bool.and_eq_true, List.all_eq_true, Function.comp_apply, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨hs, hlt⟩, hq⟩ := h
  unfold chkC8Pts
  rw [← Array.all_toList]
  simp only [comm_tv hC, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨hs, fun r hr => ⟨⟨hlt r hr, (hq r hr).1⟩, (hq r hr).2⟩⟩

theorem chkC8Fix_of (h : c8FixK (C.getD 0 []) (C.getD 1 []) = true) : chkC8Fix = true := by
  unfold c8FixK at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_range] at h
  obtain ⟨hb, hl⟩ := h
  have hlow : ∀ j < 4096, (c8ap (C.getD 0 []) (256 * j) = 256 * j ∧
      c8ap (C.getD 1 []) (256 * j) = 256 * j) ↔ j = 0 := by
    intro j hj
    have e := hl j hj
    rw [Bool.eq_iff_iff] at e
    simpa using e
  unfold chkC8Fix
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq, ap_tv hC]
  intro c hc
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact c8_fixed (c8ap_xor _) (c8ap_xor _) (fun m hm => (hb m hm).1) (fun m hm => (hb m hm).2)
    hlow hc

omit hC in
theorem c8RestrK_get {A B : List Nat} {R : List (Nat × List Nat)} :
    ∀ (l : List (List Nat)) (s : Nat), c8RestrK A B R l s = true →
      ∀ k < l.length, c8RestrB A B R (s + k) (l.getD k []) = true
  | [], _, _, k, hk => absurd hk (by simp)
  | T :: l, s, h, k, hk => by
    have e : c8RestrK A B R (T :: l) s = (c8RestrB A B R s T && c8RestrK A B R l (s + 1)) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases k with _ | k
    · simpa using h.1
    · have h2 := c8RestrK_get l (s + 1) h.2 k (by simpa using hk)
      rw [(by omega : s + 1 + k = s + (k + 1))] at h2
      simpa using h2

theorem chkC8Restr_of (hL : C.length = 693)
    (h : c8RestrK (C.getD 0 []) (C.getD 1 []) (c8R (c8Q C)) C 0 = true) : chkC8Restr = true := by
  have hw := c8RestrK_get C 0 h
  unfold chkC8Restr
  rw [List.all_eq_true]
  intro s hs
  have hs' := List.mem_range.mp hs
  have hb := hw s (by omega)
  rw [Nat.zero_add] at hb
  unfold c8RestrB c8R c8Q at hb
  rw [zip_map_self, List.all_map] at hb
  simp only [Function.comp_def] at hb
  simp only [← Array.all_toList, hC, getElem!_toArray, commuteB_toArray]
  exact hb

theorem c8Step_eq (s x : Nat) : c8Step s x = c8StepK (C.getD 0 []) (c8Q C) s x := by
  have e : (c8Q C).getD (s / 2) (C.getD 0 []) = C.getD (c8Pts.toList.getD (s / 2) 0) [] := by
    unfold c8Q
    rw [List.getD_map]
  unfold c8Step c8StepK
  rw [e, arr_get, ap_tv hC]

theorem chkC8Irr_of (h : c8IrrK (C.getD 0 []) (c8Q C) = true) : chkC8Irr = true := by
  have hp : c8Path = c8PathK (C.getD 0 []) (c8Q C) := by
    funext p x
    unfold c8Path c8PathK
    simp only [c8Step_eq hC]
  unfold c8IrrK at h
  unfold chkC8Irr
  rw [hp]
  exact h

theorem chkRigid_of (h8 : ∀ m < 8, c8ap (C.getD 0 []) (2 ^ m) = 2 ^ m)
    (h1 : c8RigK (C.getD 0 []) (rigS.map fun s => C.getD s []) = true)
    (h2 : c8Rig2K (C.getD 0 []) C = true) : chkRigid = true := by
  have hw : ∀ u x, tvWordApply u x = c8Word C u x := by
    intro u x
    unfold tvWordApply c8Word
    simp only [ap_tv hC]
  have hr : ∀ e, rigW e = c8ap (C.getD 0 []) e ^^^ e := by
    intro e
    unfold rigW
    rw [ap_tv hC]
  unfold c8RigK at h1
  simp only [List.all_map, Function.comp_def, List.all_eq_true, List.mem_range] at h1
  unfold c8Rig2K at h2
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨⟨⟨⟨g1, g2⟩, g4⟩, g5⟩, g6⟩, g7⟩ := h2
  unfold chkRigid
  simp only [hr, hw, ap_tv hC, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨g1, ?_⟩, ?_⟩, g4⟩, g5⟩, ?_⟩, ?_⟩
  · simpa only [arr_contains] using g2
  · rw [List.all_eq_true]
    intro e he
    have he' := List.mem_range.mp he
    rw [rig_low h8 he']
    exact h1 _ (c8_high e).2
  · rw [← Array.all_toList]
    simpa only [arr_contains] using g6
  · simpa only [applyCols_arr, Array.toList_append, Array.toList_map, arr_get] using g7

end Cols

end CFSG.SmithE.K
