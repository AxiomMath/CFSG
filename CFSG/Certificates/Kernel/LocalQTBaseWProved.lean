module

public import Certificates.Data.Kernel.LocalQT.BaseW
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public import CFSG.Certificates.Kernel.LocalQTBfsKSound

public section

namespace CFSG.KC.LQT.BW.Pf

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem impB_eq (a b : Bool) : impB a b = (!a || b) := by cases a <;> rfl

theorem letLs_eq (y : Nat) (k : Nat → List Nat) : letLs y k = k y := by cases y <;> rfl

theorem letE_eq (y : Nat) (k : Nat → ES) : letE y k = k y := by cases y <;> rfl

theorem lenA_eq {α : Type} (l : List α) : lenA l = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have e : lenA (x :: t) = lenA t + 1 := rfl
    rw [e, ih]
    rfl

theorem allL_eq (l : List Nat) (f : Nat → Bool) : allL l f = l.all f := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have e : allL (x :: t) f = andB (f x) (allL t f) := rfl
    rw [e, ih, andB_eq, List.all_cons]

theorem anyL_eq (l : List Nat) (f : Nat → Bool) : anyL l f = l.any f := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have e : anyL (x :: t) f = orB (f x) (anyL t f) := rfl
    rw [e, ih, orB_eq, List.any_cons]

theorem allA_eq {α : Type} (l : List α) (f : α → Bool) : allA l f = l.all f := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have e : allA (x :: t) f = andB (f x) (allA t f) := rfl
    rw [e, ih, andB_eq, List.all_cons]

theorem allLL_eq (l : List (List Nat)) (f : List Nat → Bool) : allLL l f = l.all f := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have e : allLL (x :: t) f = andB (f x) (allLL t f) := rfl
    rw [e, ih, andB_eq, List.all_cons]

theorem allBs_cons (b : Bool) (l : List Bool) : allBs (b :: l) = (b && allBs l) := by
  have e : allBs (b :: l) = andB b (allBs l) := rfl
  rw [e, andB_eq]

theorem allBs_nil : allBs [] = true := rfl

theorem appK_eq (a b : List Nat) : appK a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons x t ih =>
    have e : appK (x :: t) b = x :: appK t b := rfl
    rw [e, ih]
    rfl

theorem flatK_eq (cs : List (List Nat)) : flatK cs = cs.flatten := by
  induction cs with
  | nil => rfl
  | cons c t ih =>
    have e : flatK (c :: t) = appK c (flatK t) := rfl
    rw [e, ih, appK_eq, List.flatten_cons]

theorem takeK_eq : ∀ (m : Nat) (l : List Nat), takeK m l = l.take m
  | _, [] => by cases ‹Nat› <;> rfl
  | 0, _ :: _ => rfl
  | m + 1, x :: t => by
    change x :: takeK m t = _
    rw [takeK_eq m t]
    rfl

theorem dropK_eq : ∀ (m : Nat) (l : List Nat), dropK m l = l.drop m
  | _, [] => by cases ‹Nat› <;> rfl
  | 0, _ :: _ => rfl
  | m + 1, _ :: t => by
    change dropK m t = _
    rw [dropK_eq m t]
    rfl

theorem revOn_eq {α : Type} : ∀ (l acc : List α), revOn l acc = l.reverse ++ acc
  | [], _ => rfl
  | x :: t, acc => by
    change revOn t (x :: acc) = _
    rw [revOn_eq t, List.reverse_cons, List.append_assoc]
    rfl

theorem eqL_iff : ∀ (l m : List Nat), eqL l m = true ↔ l = m
  | [], [] => by simp [eqL]
  | [], _ :: _ => by simp [eqL]
  | _ :: _, [] => by simp [eqL]
  | x :: t, y :: u => by
    change andB (Nat.beq x y) (eqL t u) = true ↔ _
    rw [P.andB_iff, P.beq_iff, eqL_iff t u, List.cons.injEq]

theorem eqLW_iff (l m : List Nat) : eqLW l m = true ↔ l = m := eqL_iff l m

theorem getK_eq : ∀ (l : List Nat) (i : Nat), getK l i = l.getD i 0
  | [], _ => rfl
  | x :: t, i => by
    change Bool.rec (motive := fun _ => Nat) (getK t (Nat.sub i 1)) x (Nat.beq i 0) = _
    cases i with
    | zero => rfl
    | succ i =>
      have e : Nat.beq (i + 1) 0 = false := rfl
      rw [e]
      dsimp only
      rw [getK_eq t, List.getD_cons_succ]
      rfl

theorem tabL_spec {n : Nat} {l : List Nat} (h : tabL n l = true) :
    l.length = n ∧ ∀ v ∈ l, v < n := by
  rw [tabL, andB_eq, Bool.and_eq_true, allL_eq, lenA_eq, List.all_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, fun v hv => by simpa using h.2 v hv⟩

theorem imgW_eq (w s i : Nat) : imgW w s i = (s >>> (w * i)) &&& (2 ^ w - 1) := by
  have e : Nat.shiftLeft 1 w = 2 ^ w := by
    change 1 <<< w = 2 ^ w
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [imgW, e]
  rfl

theorem testBit_imgW (w s i j : Nat) :
    (imgW w s i).testBit j = (decide (j < w) && s.testBit (w * i + j)) := by
  rw [imgW_eq, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem imgW_lt (w s i : Nat) : imgW w s i < 2 ^ w := by
  rw [imgW_eq]
  have h1 : (s >>> (w * i)) &&& (2 ^ w - 1) ≤ 2 ^ w - 1 := Nat.and_le_right
  have h2 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  omega

theorem testBit_lt {x w j : Nat} (hx : x < 2 ^ w) (hj : w ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hj))

theorem imgW_codeK {w : Nat} : ∀ (l : List Nat), (∀ x ∈ l, x < 2 ^ w) →
    ∀ i < l.length, imgW w (codeK w l) i = l.getD i 0
  | [], _, i, hi => by simp at hi
  | x :: t, hl, i, hi => by
    have e : codeK w (x :: t) = 2 ^ w * codeK w t + x := by
      change Nat.add x (Nat.shiftLeft (codeK w t) w) = _
      change x + (codeK w t <<< w) = _
      rw [Nat.shiftLeft_eq, Nat.add_comm, Nat.mul_comm]
    have hx : x < 2 ^ w := hl x (List.mem_cons_self ..)
    apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_imgW, e, Nat.testBit_two_pow_mul_add _ hx]
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero]
      by_cases hj : j < w
      · simp [hj]
      · simp [hj, testBit_lt (j := j) hx (by omega)]
    | succ i =>
      simp only [List.getD_cons_succ]
      have ih := imgW_codeK t (fun y hy => hl y (List.mem_cons_of_mem _ hy)) i
        (by simpa using hi)
      rw [← ih, testBit_imgW]
      have h1 : ¬ w * (i + 1) + j < w := by
        have : w ≤ w * (i + 1) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have h2 : w * (i + 1) + j - w = w * i + j := by
        rw [Nat.mul_succ]
        omega
      simp [h1, h2]

theorem testBit_ofFnW (w : Nat) (g : Nat → Nat) (p : Nat) : ∀ m,
    (ofFnW m w g).testBit p =
      (List.range m).any fun j => decide (w * j ≤ p) && (g j).testBit (p - w * j)
  | 0 => by
    have e : ofFnW 0 w g = 0 := rfl
    rw [e]
    simp
  | m + 1 => by
    have e : ofFnW (m + 1) w g = ofFnW m w g ||| (g m <<< (w * m)) := rfl
    rw [e, Nat.testBit_or, testBit_ofFnW w g p m, List.range_succ, List.any_append,
      Nat.testBit_shiftLeft]
    simp

theorem imgW_ofFnW {n w : Nat} {g : Nat → Nat} (hg : ∀ j < n, g j < 2 ^ w) {i : Nat}
    (hi : i < n) : imgW w (ofFnW n w g) i = g i := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_imgW, testBit_ofFnW]
  by_cases hq : q < w
  · simp only [hq, decide_true, Bool.true_and]
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨j, hj, hle, hb⟩
      have hlt : w * i + q - w * j < w := by
        apply Nat.lt_of_not_le
        intro hc
        rw [testBit_lt (hg j hj) hc] at hb
        exact absurd hb (by decide)
      have hji : j = i := by
        rcases Nat.lt_trichotomy j i with h | h | h
        · have : w * (j + 1) ≤ w * i := Nat.mul_le_mul_left _ h
          rw [Nat.mul_succ] at this
          omega
        · exact h
        · have : w * (i + 1) ≤ w * j := Nat.mul_le_mul_left _ h
          rw [Nat.mul_succ] at this
          omega
      subst hji
      have e : w * j + q - w * j = q := by omega
      rwa [e] at hb
    · intro hb
      refine ⟨i, hi, by omega, ?_⟩
      have e : w * i + q - w * i = q := by omega
      rwa [e]
  · rw [testBit_lt (j := q) (hg i hi) (by omega)]
    simp [hq]

@[expose] def Rep (n w c : Nat) (t : Array Nat) : Prop :=
  t.size = n ∧ ∀ i < n, img t i < n ∧ imgW w c i = img t i

theorem rep_codeK {n w : Nat} (hw : n ≤ 2 ^ w) {l : List Nat} (h : tabL n l = true) :
    Rep n w (codeK w l) l.toArray := by
  obtain ⟨h1, h2⟩ := tabL_spec h
  refine ⟨by simpa using h1, fun i hi => ?_⟩
  have e : img l.toArray i = l.getD i 0 := by
    rw [img, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  rw [e, imgW_codeK l (fun x hx => Nat.lt_of_lt_of_le (h2 x hx) hw) i (by omega)]
  refine ⟨?_, rfl⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact h2 _ (List.getElem_mem _)

theorem img_compArr {n : Nat} {s t : Array Nat} (hs : s.size = n) (ht : t.size = n)
    (htl : ∀ i < n, img t i < n) {i : Nat} (hi : i < n) :
    img (compArr s t) i = img s (img t i) := by
  have e1 : img t i = t[i] := by
    rw [img, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]
  have hti := htl i hi
  rw [e1] at hti ⊢
  rw [img, Array.getD_eq_getD_getElem?, compArr, Array.getElem?_map,
    Array.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some,
    getElem!_pos s t[i] (by omega), img, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by omega), Option.getD_some]

theorem rep_mul {n w : Nat} {c d : Nat} {s t : Array Nat} (hc : Rep n w c s)
    (hd : Rep n w d t) : Rep n w (mulW n w c d) (compArr s t) := by
  obtain ⟨hs1, hs2⟩ := hc
  obtain ⟨ht1, ht2⟩ := hd
  refine ⟨by simp [compArr, ht1], fun i hi => ?_⟩
  rw [img_compArr hs1 ht1 (fun j hj => (ht2 j hj).1) hi]
  refine ⟨(hs2 _ (ht2 i hi).1).1, ?_⟩
  rw [mulW, imgW_ofFnW (fun j _ => imgW_lt _ _ _) hi, (ht2 i hi).2, (hs2 _ (ht2 i hi).1).2]

theorem rep_inv {n w : Nat} {c d : Nat} {s t : Array Nat} (hc : Rep n w c s) (hd : Rep n w d t)
    (hw : n ≤ 2 ^ w) (h : mulW n w d c = oneW n w) : ∀ q < n, img t (img s q) = q := by
  intro q hq
  have e := congrArg (fun x => imgW w x q) h
  simp only [mulW, oneW] at e
  rw [imgW_ofFnW (fun j _ => imgW_lt _ _ _) hq, imgW_ofFnW (fun j hj => by omega) hq,
    (hc.2 q hq).2, (hd.2 _ (hc.2 q hq).1).2] at e
  exact e

theorem nodeK_cons_lt (y : Nat) (acc : List Nat) {j : Nat} (hj : j < acc.length) :
    nodeK (y :: acc) j = nodeK acc j := by
  rw [nodeK, nodeK, getK_eq, getK_eq, lenA_eq, lenA_eq, List.length_cons]
  have e : acc.length + 1 - 1 - j = (acc.length - 1 - j) + 1 := by omega
  change (y :: acc).getD (Nat.sub (Nat.sub (acc.length + 1) 1) j) 0 = acc.getD (Nat.sub (Nat.sub acc.length 1) j) 0
  rw [show Nat.sub (Nat.sub (acc.length + 1) 1) j = acc.length + 1 - 1 - j from rfl, e,
    List.getD_cons_succ]
  rfl

theorem nodeK_cons_len (y : Nat) (acc : List Nat) : nodeK (y :: acc) acc.length = y := by
  rw [nodeK, getK_eq, lenA_eq, List.length_cons]
  change (y :: acc).getD (acc.length + 1 - 1 - acc.length) 0 = y
  rw [show acc.length + 1 - 1 - acc.length = 0 by omega]
  rfl

@[expose] noncomputable def slpGo (mf : Nat → Nat → Nat) : List (Nat × Nat) → List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun p _ ih acc => letLs (mf (nodeK acc p.1) (nodeK acc p.2)) fun y => ih (List.cons y acc))

theorem slpW_eq (n w a b : Nat) (prog : List (Nat × Nat)) :
    slpW n w a b prog = slpGo (mulW n w) prog [b, a] := rfl

theorem slpGo_cons (mf : Nat → Nat → Nat) (p : Nat × Nat) (l : List (Nat × Nat)) (acc : List Nat) :
    slpGo mf (p :: l) acc = slpGo mf l (mf (nodeK acc p.1) (nodeK acc p.2) :: acc) := by
  have e : slpGo mf (p :: l) acc =
      letLs (mf (nodeK acc p.1) (nodeK acc p.2)) fun y => slpGo mf l (y :: acc) := rfl
  rw [e, letLs_eq]

theorem slpOKK_spec' (prog : List (Nat × Nat)) (m : Nat) (h : slpOKK prog m = true) :
    slpValidAux prog m = true := by
  induction prog generalizing m with
  | nil => simp [slpValidAux]
  | cons p rest ih =>
    have h' : andB (andB (Nat.blt p.1 m) (Nat.blt p.2 m)) (slpOKK rest (Nat.succ m)) = true := h
    simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq] at h'
    simp only [slpValidAux, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨h'.1.1, h'.1.2⟩, ih (m + 1) h'.2⟩

theorem slpGo_rep {n w : Nat} (hw : n ≤ 2 ^ w) : ∀ (l : List (Nat × Nat)) (acc : List Nat)
    (arr : Array (Array Nat)), acc.length = arr.size →
    (∀ j < arr.size, Rep n w (nodeK acc j) arr[j]!) → slpValidAux l arr.size = true →
    (slpGo (mulW n w) l acc).length = (l.foldl slpStepA arr).size ∧
      ∀ j < (l.foldl slpStepA arr).size,
        Rep n w (nodeK (slpGo (mulW n w) l acc) j) (l.foldl slpStepA arr)[j]!
  | [], acc, arr, hl, ha, _ => ⟨hl, ha⟩
  | p :: l, acc, arr, hl, ha, hv => by
    rw [slpValidAux, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hp1, hp2⟩, hv⟩ := hv
    rw [slpGo_cons, List.foldl_cons]
    have hs : (slpStepA arr p).size = arr.size + 1 := by simp [slpStepA]
    apply slpGo_rep hw l
    · simp [hs, hl]
    · intro j hj
      rw [hs] at hj
      unfold slpStepA
      rcases Nat.lt_or_ge j arr.size with hjk | hjk
      · rw [nodeK_cons_lt _ _ (by omega), getElem!_pos _ j (by simp; omega),
          Array.getElem_push_lt hjk, ← getElem!_pos arr j hjk]
        exact ha j hjk
      · have e : j = arr.size := by omega
        subst e
        rw [← hl, nodeK_cons_len, hl, getElem!_pos _ arr.size (by simp), Array.getElem_push_eq]
        exact rep_mul (ha _ hp1) (ha _ hp2)
    · rw [hs]
      exact hv

theorem slpW_rep {n w : Nat} (hw : n ≤ 2 ^ w) {ta tb : List Nat} (ha : tabL n ta = true)
    (hb : tabL n tb = true) {prog : List (Nat × Nat)} (hv : slpOKK prog 2 = true) :
    lenA (slpW n w (codeK w ta) (codeK w tb) prog) =
        (slpTabsA ta.toArray tb.toArray prog).size ∧
      ∀ j < (slpTabsA ta.toArray tb.toArray prog).size,
        Rep n w (nodeK (slpW n w (codeK w ta) (codeK w tb) prog) j)
          (slpTabsA ta.toArray tb.toArray prog)[j]! := by
  rw [lenA_eq, slpW_eq, slpTabsA]
  apply slpGo_rep hw prog [codeK w tb, codeK w ta] #[ta.toArray, tb.toArray] rfl
  · intro j hj
    rcases j with _ | _ | j
    · exact rep_codeK hw ha
    · exact rep_codeK hw hb
    · simp at hj
  · exact slpOKK_spec' prog 2 hv

theorem imgsW_eq (w g : Nat) : ∀ l : List Nat, imgsW w g l = l.map (imgW w g)
  | [] => rfl
  | x :: t => by
    change letLs (imgW w g x) (fun y => y :: imgsW w g t) = _
    rw [letLs_eq, imgsW_eq w g t, List.map_cons]

theorem imgsW_rep {n w g : Nat} {s : Array Nat} (hg : Rep n w g s) {l : List Nat}
    (hl : ∀ x ∈ l, x < n) : imgsW w g l = applyTab s l := by
  rw [imgsW_eq, applyTab]
  exact List.map_congr_left fun x hx => (hg.2 x (hl x hx)).2

theorem applyTab_lt {n w g : Nat} {s : Array Nat} (hs : Rep n w g s) {l : List Nat}
    (hl : ∀ x ∈ l, x < n) : ∀ x ∈ applyTab s l, x < n := by
  intro x hx
  rw [applyTab, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (hs.2 y (hl y hy)).1

theorem ptsW_eq {n w : Nat} {B : List Nat} (hB : ∀ b ∈ B, b < n) :
    ∀ {Gc : List Nat} {G : List (Array Nat)}, List.Forall₂ (fun c s => Rep n w c s) Gc G →
      ptsW w B Gc = ptsOf B G := by
  intro Gc G hG
  have key : ∀ {Gc : List Nat} {G : List (Array Nat)},
      List.Forall₂ (fun c s => Rep n w c s) Gc G →
      List.rec (motive := fun _ => List (List Nat)) [] (fun g _ ih => List.cons (imgsW w g B) ih)
        Gc = G.map fun s => B.map (img s) := by
    intro Gc G hG
    induction hG with
    | nil => rfl
    | @cons c s _ _ hr _ ih =>
      rw [List.map_cons, ← ih]
      have e : List.map (img s) B = applyTab s B := rfl
      rw [e, ← imgsW_rep hr hB]
  rw [ptsW, appK_eq, flatK_eq, key hG, ptsOf, List.flatMap_def]

theorem codeK_inj {w : Nat} {l m : List Nat} (hl : ∀ x ∈ l, x < 2 ^ w) (hm : ∀ x ∈ m, x < 2 ^ w)
    (hlen : l.length = m.length) (h : codeK w l = codeK w m) : l = m := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have e1 := imgW_codeK l hl i h1
  have e2 := imgW_codeK m hm i h2
  rw [h, e2] at e1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at e1
  exact e1.symm

theorem foldl_digits_inj {n : Nat} : ∀ (l m : List Nat) (a b : Nat), (∀ x ∈ l, x < n) →
    (∀ x ∈ m, x < n) → l.length = m.length →
    l.foldl (fun acc q => acc * n + q) a = m.foldl (fun acc q => acc * n + q) b → a = b ∧ l = m
  | [], [], a, b, _, _, _, h => ⟨h, rfl⟩
  | [], _ :: _, _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, hlen, _ => by simp at hlen
  | x :: l, y :: m, a, b, hl, hm, hlen, h => by
    rw [List.foldl_cons, List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := foldl_digits_inj l m (a * n + x) (b * n + y)
      (fun z hz => hl z (List.mem_cons_of_mem _ hz)) (fun z hz => hm z (List.mem_cons_of_mem _ hz))
      (by simpa using hlen) h
    have hx := hl x (List.mem_cons_self ..)
    have hy := hm y (List.mem_cons_self ..)
    have hxy : x = y := by
      have e1 : (a * n + x) % n = x := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
      have e2 : (b * n + y) % n = y := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
      rw [← e1, ← e2, h1]
    subst hxy
    have hab : a = b := by
      have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hx
      have e1 : (a * n + x) / n = a := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hx, Nat.zero_add]
      have e2 : (b * n + x) / n = b := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hx, Nat.zero_add]
      rw [← e1, ← e2, h1]
    exact ⟨hab, by rw [h2]⟩

@[expose] def Val (n L : Nat) (T : List Nat) : Prop := T.length = L ∧ ∀ x ∈ T, x < n

theorem take_lt {n : Nat} {T : List Nat} (h : ∀ x ∈ T, x < n) (r : Nat) : ∀ x ∈ T.take r, x < n :=
  fun x hx => h x (List.mem_of_mem_take hx)

theorem keyW_eq_iff {n w L nb : Nat} (hw : n ≤ 2 ^ w) {T U : List Nat} (hT : Val n L T)
    (hU : Val n L U) : keyW w nb T = keyW w nb U ↔ T.take nb = U.take nb := by
  rw [keyW, keyW, takeK_eq, takeK_eq]
  refine ⟨fun h => codeK_inj (fun x hx => Nat.lt_of_lt_of_le (take_lt hT.2 nb x hx) hw)
    (fun x hx => Nat.lt_of_lt_of_le (take_lt hU.2 nb x hx) hw) (by simp [hT.1, hU.1]) h,
    fun h => by rw [h]⟩

theorem keyNat_eq_iff {n L nb : Nat} {T U : List Nat} (hT : Val n L T) (hU : Val n L U) :
    keyNat n nb T = keyNat n nb U ↔ T.take nb = U.take nb := by
  rw [keyNat, keyNat]
  exact ⟨fun h => (foldl_digits_inj _ _ 0 0 (take_lt hT.2 nb) (take_lt hU.2 nb)
    (by simp [hT.1, hU.1]) h).2, fun h => by rw [h]⟩

theorem keyW_iff_keyNat {n w L nb : Nat} (hw : n ≤ 2 ^ w) {T U : List Nat} (hT : Val n L T)
    (hU : Val n L U) : keyW w nb T = keyW w nb U ↔ keyNat n nb T = keyNat n nb U := by
  rw [keyW_eq_iff hw hT hU, keyNat_eq_iff hT hU]

@[expose] def memKT : TT → Nat → Prop
  | .lf, _ => False
  | .nd l k _ _ r, x => memKT l x ∨ x = k ∨ memKT r x

@[expose] def OrdT : TT → Prop
  | .lf => True
  | .nd l k _ _ r => OrdT l ∧ OrdT r ∧ (∀ y, memKT l y → ltR y k) ∧ (∀ y, memKT r y → ltR k y)

@[expose] noncomputable def memG (lt : Nat → Nat → Bool) (t : TT) (x : Nat) : Bool :=
  TT.rec (motive := fun _ => Bool) false
    (fun _ k _ _ _ ihl ihr => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) ihr ihl (lt x k)) true (Nat.beq x k)) t

@[expose] noncomputable def idxG (lt : Nat → Nat → Bool) (t : TT) (x : Nat) : Nat :=
  TT.rec (motive := fun _ => Nat) 0
    (fun _ k v _ _ ihl ihr => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) ihr ihl (lt x k)) v (Nat.beq x k)) t

@[expose] noncomputable def tabG (lt : Nat → Nat → Bool) (t : TT) (x : Nat) : List Nat :=
  TT.rec (motive := fun _ => List Nat) []
    (fun _ k _ T _ ihl ihr => Bool.rec (motive := fun _ => List Nat)
      (Bool.rec (motive := fun _ => List Nat) ihr ihl (lt x k)) T (Nat.beq x k)) t

@[expose] noncomputable def insG (lt : Nat → Nat → Bool) (t : TT) (x v : Nat) (T : List Nat) : TT :=
  TT.rec (motive := fun _ => TT) (TT.nd TT.lf x v T TT.lf)
    (fun l k u U r ihl ihr => Bool.rec (motive := fun _ => TT)
      (Bool.rec (motive := fun _ => TT) (TT.nd l k u U ihr) (TT.nd ihl k u U r) (lt x k))
      (TT.nd l k u U r) (Nat.beq x k)) t

theorem memTT_eq (t : TT) (x : Nat) : memTT t x = memG ltK t x := by
  delta memTT memG
  rfl

theorem idxTT_eq (t : TT) (x : Nat) : idxTT t x = idxG ltK t x := by
  delta idxTT idxG
  rfl

theorem tabTT_eq (t : TT) (x : Nat) : tabTT t x = tabG ltK t x := by
  delta tabTT tabG
  rfl

theorem insTT_eq (t : TT) (x v : Nat) (T : List Nat) : insTT t x v T = insG ltK t x v T := by
  delta insTT insG
  rfl

section Gen

variable {lt : Nat → Nat → Bool} (hlt : ∀ x y, lt x y = true ↔ ltR x y)

theorem memG_nd (l : TT) (k v : Nat) (T : List Nat) (r : TT) (x : Nat) :
    memG lt (.nd l k v T r) x = Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (memG lt r x) (memG lt l x) (lt x k)) true
        (Nat.beq x k) :=
  rfl

theorem idxG_nd (l : TT) (k v : Nat) (T : List Nat) (r : TT) (x : Nat) :
    idxG lt (.nd l k v T r) x = Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (idxG lt r x) (idxG lt l x) (lt x k)) v (Nat.beq x k) :=
  rfl

theorem tabG_nd (l : TT) (k v : Nat) (T : List Nat) (r : TT) (x : Nat) :
    tabG lt (.nd l k v T r) x = Bool.rec (motive := fun _ => List Nat)
      (Bool.rec (motive := fun _ => List Nat) (tabG lt r x) (tabG lt l x) (lt x k)) T
        (Nat.beq x k) :=
  rfl

theorem insG_nd (l : TT) (k u : Nat) (U : List Nat) (r : TT) (x v : Nat) (T : List Nat) :
    insG lt (.nd l k u U r) x v T = Bool.rec (motive := fun _ => TT)
      (Bool.rec (motive := fun _ => TT) (TT.nd l k u U (insG lt r x v T))
        (TT.nd (insG lt l x v T) k u U r) (lt x k)) (TT.nd l k u U r) (Nat.beq x k) :=
  rfl

theorem insG_lf (x v : Nat) (T : List Nat) : insG lt .lf x v T = .nd .lf x v T .lf := rfl

include hlt in
theorem ltG_false {x y : Nat} (h : ¬ ltR x y) : lt x y = false :=
  Bool.eq_false_iff.2 fun e => h ((hlt x y).1 e)

include hlt in
theorem memG_iff : ∀ {t : TT}, OrdT t → ∀ x, (memG lt t x = true ↔ memKT t x)
  | .lf, _, x => by simp [memG, memKT]
  | .nd l k v T r, ho, x => by
    obtain ⟨ol, orr, bl, br⟩ := ho
    rw [memG_nd]
    by_cases hxk : x = k
    · rw [P.beq_iff.2 hxk]
      simp [memKT, hxk]
    · rw [beq_false hxk]
      dsimp only
      by_cases hl : ltR x k
      · rw [(hlt x k).2 hl]
        dsimp only
        rw [memG_iff ol x]
        simp only [memKT]
        constructor
        · exact fun h => Or.inl h
        · rintro (h | h | h)
          · exact h
          · exact absurd h hxk
          · exact absurd (br x h) (ltR_asymm hl)
      · rw [ltG_false hlt hl]
        dsimp only
        rw [memG_iff orr x]
        simp only [memKT]
        constructor
        · exact fun h => Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact absurd (bl x h) hl
          · exact absurd h hxk
          · exact h

include hlt in
theorem mem_insG (x v : Nat) (T : List Nat) (y : Nat) :
    ∀ t : TT, memKT (insG lt t x v T) y ↔ y = x ∨ memKT t y
  | .lf => by
    rw [insG_lf]
    simp [memKT]
  | .nd l k u U r => by
    rw [insG_nd]
    by_cases hxk : x = k
    · rw [P.beq_iff.2 hxk]
      dsimp only
      simp only [memKT]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact Or.inr (Or.inl hxk)
        · exact h
    · rw [beq_false hxk]
      dsimp only
      by_cases hl : ltR x k
      · rw [(hlt x k).2 hl]
        dsimp only
        simp only [memKT, mem_insG x v T y l]
        tauto
      · rw [ltG_false hlt hl]
        dsimp only
        simp only [memKT, mem_insG x v T y r]
        tauto

include hlt in
theorem ord_insG (x v : Nat) (T : List Nat) : ∀ {t : TT}, OrdT t → OrdT (insG lt t x v T)
  | .lf, _ => by
    rw [insG_lf]
    simp [OrdT, memKT]
  | .nd l k u U r, ho => by
    obtain ⟨ol, orr, bl, br⟩ := ho
    rw [insG_nd]
    by_cases hxk : x = k
    · rw [P.beq_iff.2 hxk]
      exact ⟨ol, orr, bl, br⟩
    · rw [beq_false hxk]
      dsimp only
      by_cases hl : ltR x k
      · rw [(hlt x k).2 hl]
        dsimp only
        refine ⟨ord_insG x v T ol, orr, fun y hy => ?_, br⟩
        rcases (mem_insG hlt x v T y l).1 hy with rfl | hy
        · exact hl
        · exact bl y hy
      · rw [ltG_false hlt hl]
        dsimp only
        refine ⟨ol, ord_insG x v T orr, bl, fun y hy => ?_⟩
        rcases (mem_insG hlt x v T y r).1 hy with rfl | hy
        · exact ltR_total hxk hl
        · exact br y hy

theorem look_insG_self (x v : Nat) (T : List Nat) : ∀ {t : TT}, ¬ memKT t x →
    idxG lt (insG lt t x v T) x = v ∧ tabG lt (insG lt t x v T) x = T
  | .lf, _ => by
    rw [insG_lf, idxG_nd, tabG_nd, P.beq_iff.2 rfl]
    exact ⟨rfl, rfl⟩
  | .nd l k u U r, hm => by
    have hxk : x ≠ k := fun e => hm (Or.inr (Or.inl e))
    rw [insG_nd, beq_false hxk]
    dsimp only
    cases hc : lt x k
    · dsimp only
      rw [idxG_nd, tabG_nd, beq_false hxk, hc]
      exact look_insG_self x v T (fun h => hm (Or.inr (Or.inr h)))
    · dsimp only
      rw [idxG_nd, tabG_nd, beq_false hxk, hc]
      exact look_insG_self x v T (fun h => hm (Or.inl h))

theorem look_insG_ne (x v : Nat) (T : List Nat) {y : Nat} (hyx : y ≠ x) : ∀ t : TT,
    idxG lt (insG lt t x v T) y = idxG lt t y ∧ tabG lt (insG lt t x v T) y = tabG lt t y
  | .lf => by
    rw [insG_lf, idxG_nd, tabG_nd, beq_false hyx]
    cases lt y x <;> exact ⟨rfl, rfl⟩
  | .nd l k u U r => by
    rw [insG_nd]
    by_cases hxk : x = k
    · rw [P.beq_iff.2 hxk]
      exact ⟨rfl, rfl⟩
    · rw [beq_false hxk]
      dsimp only
      cases hc : lt x k
      · dsimp only
        rw [idxG_nd, tabG_nd, idxG_nd, tabG_nd]
        by_cases hyk : y = k
        · rw [P.beq_iff.2 hyk]
          exact ⟨rfl, rfl⟩
        · rw [beq_false hyk]
          dsimp only
          cases lt y k
          · exact look_insG_ne x v T hyx r
          · exact ⟨rfl, rfl⟩
      · dsimp only
        rw [idxG_nd, tabG_nd, idxG_nd, tabG_nd]
        by_cases hyk : y = k
        · rw [P.beq_iff.2 hyk]
          exact ⟨rfl, rfl⟩
        · rw [beq_false hyk]
          dsimp only
          cases lt y k
          · exact ⟨rfl, rfl⟩
          · exact look_insG_ne x v T hyx l

end Gen

theorem arr_getL (A : Array (List Nat)) (i : Nat) : A[i]! = A.toList.getD i [] := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    List.getD_eq_getElem?_getD]
  rfl

theorem arr_getN (A : Array Nat) (i : Nat) : A[i]! = A.toList.getD i 0 := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    List.getD_eq_getElem?_getD]
  rfl

theorem getD_append_left {α : Type} {l new : List α} {d : α} {i : Nat} (hi : i < l.length) :
    (l ++ new).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_len {α : Type} (l : List α) (x : α) (d : α) : (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem getD_mem {α : Type} {l : List α} {d : α} {i : Nat} (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem _

abbrev St := Array (List Nat) × Array Nat × Std.HashMap Nat Nat

@[expose] noncomputable def bodyB (n r i : Nat) (T : List Nat) (acc : St) (s : Array Nat) : St :=
  if acc.2.2.contains (keyNat n r (applyTab s T)) then acc
  else (acc.1.push (applyTab s T), acc.2.1.push i,
    acc.2.2.insert (keyNat n r (applyTab s T)) acc.1.size)

theorem bfsLoopB_succ (n r : Nat) (G : List (Array Nat)) (f i : Nat) (st : St) :
    bfsLoopB n r G (f + 1) i st = if i < st.1.size then
      bfsLoopB n r G f (i + 1) (G.foldl (bodyB n r i st.1[i]!) st) else st := by
  rw [bfsLoopB]
  rfl

theorem bfsLoopB_stop (n r : Nat) (G : List (Array Nat)) (f : Nat) (st : St) :
    bfsLoopB n r G f st.1.size st = st := by
  cases f with
  | zero => rfl
  | succ f => rw [bfsLoopB_succ, ite_eq_right (Nat.lt_irrefl _)]

@[expose] noncomputable def newE (i : Nat) (st : ES) (key : Nat) (c : List Nat) : ES :=
  ES.mk (insTT st.kt key st.cnt c) (st.cnt + 1) (c :: st.rev) (i :: st.par) (st.cnt :: st.cl)
    (c :: st.fr) st.ok

@[expose] noncomputable def foundE (st : ES) (key : Nat) (c : List Nat) : ES :=
  ES.mk st.kt st.cnt st.rev st.par (idxTT st.kt key :: st.cl) st.fr
    (st.ok && eqLW (tabTT st.kt key) c)

theorem kidsW_nil (w nb : Nat) (app : Nat → List Nat → List Nat) (i : Nat) (T : List Nat)
    (st : ES) : kidsW w nb app [] i T st = st := rfl

theorem kidsW_cons (w nb : Nat) (app : Nat → List Nat → List Nat) (s : Nat) (G : List Nat)
    (i : Nat) (T : List Nat) (st : ES) : kidsW w nb app (s :: G) i T st =
      kidsW w nb app G i T (if memTT st.kt (keyW w nb (app s T)) = true
        then foundE st (keyW w nb (app s T)) (app s T)
        else newE i st (keyW w nb (app s T)) (app s T)) := by
  have e : kidsW w nb app (s :: G) i T st = letE (keyW w nb (app s T)) fun key =>
      kidsW w nb app G i T (Bool.rec (motive := fun _ => ES)
        (letE (Nat.succ st.cnt) fun cnt' =>
          ES.mk (insTT st.kt key st.cnt (app s T)) cnt' (List.cons (app s T) st.rev)
            (List.cons i st.par) (List.cons st.cnt st.cl) (List.cons (app s T) st.fr) st.ok)
        (letE (idxTT st.kt key) fun j =>
          Bool.rec (motive := fun _ => ES)
            (ES.mk st.kt st.cnt st.rev st.par (List.cons j st.cl) st.fr false)
            (ES.mk st.kt st.cnt st.rev st.par (List.cons j st.cl) st.fr st.ok)
            (eqLW (tabTT st.kt key) (app s T)))
        (memTT st.kt key)) := rfl
  rw [e, letE_eq]
  congr 1
  cases memTT st.kt (keyW w nb (app s T))
  · simp only [Bool.false_eq_true, ite_false]
    rw [letE_eq]
    rfl
  · simp only [ite_true]
    rw [letE_eq]
    unfold foundE
    cases eqLW (tabTT st.kt (keyW w nb (app s T))) (app s T) <;> cases st.ok <;> rfl

@[expose] noncomputable def clfix (gi : Nat) (st' : ES) : ES :=
  ES.mk st'.kt st'.cnt st'.rev st'.par (zerosOn gi st'.cl) st'.fr st'.ok

theorem roundW_nil (w nb gi : Nat) (app : Nat → List Nat → List Nat) (G : List Nat) (i : Nat)
    (st : ES) : roundW w nb gi app G [] i st = st := rfl

theorem roundW_cons (w nb gi : Nat) (app : Nat → List Nat → List Nat) (G : List Nat)
    (T : List Nat) (F : List (List Nat)) (i : Nat) (st : ES) :
    roundW w nb gi app G (T :: F) i st = roundW w nb gi app G F (i + 1)
      (clfix gi (kidsW w nb app G i T st)) := by
  have e : roundW w nb gi app G (T :: F) i st = letE (Nat.succ i) fun i' =>
      roundW w nb gi app G F i'
      ((fun (st' : ES) => ES.mk st'.kt st'.cnt st'.rev st'.par (zerosOn gi st'.cl) st'.fr st'.ok)
        (kidsW w nb app G i T st)) := rfl
  rw [e, letE_eq]
  rfl

section Sim

variable {n w nb L : Nat} {G : List (Array Nat)}

@[expose] def Corr (n w nb L : Nat) (G : List (Array Nat)) (es : ES) (S : St) : Prop :=
  S.1.toList = es.rev.reverse ∧ S.2.1.toList = es.par.reverse ∧ es.cnt = S.1.size ∧
  S.2.1.size = S.1.size ∧ (∀ T ∈ S.1.toList, Val n L T) ∧
  OrdT es.kt ∧ (∀ y, memKT es.kt y ↔ ∃ i < S.1.size, keyW w nb S.1[i]! = y) ∧
  (∀ i < S.1.size, idxG ltK es.kt (keyW w nb S.1[i]!) = i ∧
    tabG ltK es.kt (keyW w nb S.1[i]!) = S.1[i]!) ∧
  (∀ y, S.2.2.contains y = true ↔ ∃ i < S.1.size, keyNat n nb S.1[i]! = y) ∧
  (∀ i < S.1.size, S.2.2.getD (keyNat n nb S.1[i]!) 0 = i) ∧
  (∀ i < S.1.size, 0 < i → S.2.1[i]! < i ∧ ∃ s ∈ G, S.1[i]! = applyTab s S.1[S.2.1[i]!]!)

theorem val_get {S : St} (hv : ∀ T ∈ S.1.toList, Val n L T) {i : Nat} (hi : i < S.1.size) :
    Val n L S.1[i]! := by
  rw [arr_getL]
  exact hv _ (getD_mem (by simpa using hi))

@[expose] def Ext (S S' : St) (new : List (List Nat)) : Prop := S'.1.toList = S.1.toList ++ new

theorem ext_size {S S' : St} {new : List (List Nat)} (h : Ext S S' new) :
    S'.1.size = S.1.size + new.length := by
  have := congrArg List.length h
  simpa using this

theorem ext_get {S S' : St} {new : List (List Nat)} (h : Ext S S' new) {i : Nat}
    (hi : i < S.1.size) : S'.1[i]! = S.1[i]! := by
  rw [arr_getL, arr_getL, h, getD_append_left (by simpa using hi)]

theorem ext_trans {S S' S'' : St} {a b : List (List Nat)} (h1 : Ext S S' a) (h2 : Ext S' S'' b) :
    Ext S S'' (a ++ b) := by
  unfold Ext at *
  rw [h2, h1, List.append_assoc]

theorem step_corr (hw : n ≤ 2 ^ w) {es : ES} {S : St} (hc : Corr n w nb L G es S) {i : Nat}
    (hi : i < S.1.size) {g : Nat} {s : Array Nat} (hg : Rep n w g s) (hsG : s ∈ G) :
    Corr n w nb L G
      (if memTT es.kt (keyW w nb (imgsW w g S.1[i]!)) = true
        then foundE es (keyW w nb (imgsW w g S.1[i]!)) (imgsW w g S.1[i]!)
        else newE i es (keyW w nb (imgsW w g S.1[i]!)) (imgsW w g S.1[i]!))
      (bodyB n nb i S.1[i]! S s) ∧
    ∃ new, Ext S (bodyB n nb i S.1[i]! S s) new ∧
      (if memTT es.kt (keyW w nb (imgsW w g S.1[i]!)) = true
        then foundE es (keyW w nb (imgsW w g S.1[i]!)) (imgsW w g S.1[i]!)
        else newE i es (keyW w nb (imgsW w g S.1[i]!)) (imgsW w g S.1[i]!)).fr =
          new.reverse ++ es.fr ∧
      ((if memTT es.kt (keyW w nb (imgsW w g S.1[i]!)) = true
        then foundE es (keyW w nb (imgsW w g S.1[i]!)) (imgsW w g S.1[i]!)
        else newE i es (keyW w nb (imgsW w g S.1[i]!)) (imgsW w g S.1[i]!)).ok = true →
        es.ok = true ∧ ∃ j < (bodyB n nb i S.1[i]! S s).1.size,
          (bodyB n nb i S.1[i]! S s).1[j]! = applyTab s S.1[i]!) := by
  obtain ⟨hr, hp, hcnt, hps, hv, ho, hm, hl, hmc, hmg, hpar⟩ := hc
  have hT := val_get hv hi
  have hcv : Val n L (applyTab s S.1[i]!) :=
    ⟨by rw [applyTab, List.length_map]; exact hT.1, applyTab_lt hg hT.2⟩
  rw [imgsW_rep hg hT.2]
  generalize hcdef : applyTab s S.1[i]! = c at hcv
  have hiff : memTT es.kt (keyW w nb c) = true ↔ S.2.2.contains (keyNat n nb c) = true := by
    rw [memTT_eq, memG_iff ltK_iff ho, hm, hmc]
    constructor
    · rintro ⟨j, hj, e⟩
      exact ⟨j, hj, (keyW_iff_keyNat hw (val_get hv hj) hcv).1 e⟩
    · rintro ⟨j, hj, e⟩
      exact ⟨j, hj, (keyW_iff_keyNat hw (val_get hv hj) hcv).2 e⟩
  unfold bodyB
  rw [hcdef]
  by_cases hfound : memTT es.kt (keyW w nb c) = true
  · rw [ite_eq_left hfound, ite_eq_left (hiff.1 hfound)]
    refine ⟨⟨hr, hp, hcnt, hps, hv, ho, hm, hl, hmc, hmg, hpar⟩, [], by simp [Ext], by simp [foundE],
      fun hok => ?_⟩
    simp only [foundE, Bool.and_eq_true] at hok
    refine ⟨hok.1, ?_⟩
    obtain ⟨j, hj, e⟩ := (hm _).1 ((memG_iff ltK_iff ho _).1 (by rwa [memTT_eq] at hfound))
    refine ⟨j, hj, ?_⟩
    have := (hl j hj).2
    rw [e, ← tabTT_eq, (eqLW_iff _ _).1 hok.2] at this
    exact this.symm
  · rw [ite_eq_right hfound, ite_eq_right (fun h => hfound (hiff.2 h))]
    have hnot : ¬ memKT es.kt (keyW w nb c) := fun h =>
      hfound (by rw [memTT_eq]; exact (memG_iff ltK_iff ho _).2 h)
    have hnotN : ∀ j < S.1.size, keyNat n nb S.1[j]! ≠ keyNat n nb c := fun j hj e =>
      hfound (hiff.2 ((hmc _).2 ⟨j, hj, e⟩))
    have hnotW : ∀ j < S.1.size, keyW w nb S.1[j]! ≠ keyW w nb c := fun j hj e =>
      hnot ((hm _).2 ⟨j, hj, e⟩)
    have hext : Ext S (S.1.push c, S.2.1.push i, S.2.2.insert (keyNat n nb c) S.1.size) [c] := by
      simp [Ext]
    have hgetS : ∀ j < S.1.size, (S.1.push c)[j]! = S.1[j]! := fun j hj => ext_get hext hj
    have hgetN : (S.1.push c)[S.1.size]! = c := by
      rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, [c], hext, by simp [newE], fun hok => ?_⟩
    · simp [newE, hr]
    · simp [newE, hp]
    · simp [newE, hcnt]
    · simp [hps]
    · intro T hT'
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hT'
      rcases hT' with hT' | rfl
      · exact hv T hT'
      · exact hcv
    · simp only [newE]
      rw [insTT_eq]
      exact ord_insG ltK_iff _ _ _ ho
    · intro y
      simp only [newE]
      rw [insTT_eq, mem_insG ltK_iff, hm]
      constructor
      · rintro (rfl | ⟨j, hj, e⟩)
        · exact ⟨S.1.size, by simp, by rw [hgetN]⟩
        · exact ⟨j, by simp; omega, by rw [hgetS j hj, e]⟩
      · rintro ⟨j, hj, e⟩
        simp only [Array.size_push] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inr ⟨j, hj, by rw [← hgetS j hj, e]⟩
        · exact Or.inl (by rw [← e, hgetN])
    · intro j hj
      simp only [newE]
      rw [insTT_eq]
      simp only [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hgetS j hj, (look_insG_ne _ _ _ (hnotW j hj) _).1, (look_insG_ne _ _ _ (hnotW j hj) _).2]
        exact hl j hj
      · rw [hgetN, (look_insG_self _ _ _ hnot).1, (look_insG_self _ _ _ hnot).2, hcnt]
        exact ⟨rfl, rfl⟩
    · intro y
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hmc]
      constructor
      · rintro (rfl | ⟨j, hj, e⟩)
        · exact ⟨S.1.size, by simp, by rw [hgetN]⟩
        · exact ⟨j, by simp; omega, by rw [hgetS j hj, e]⟩
      · rintro ⟨j, hj, e⟩
        simp only [Array.size_push] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inr ⟨j, hj, by rw [← hgetS j hj, e]⟩
        · exact Or.inl (by rw [← e, hgetN])
    · intro j hj
      rw [Std.HashMap.getD_insert]
      simp only [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hgetS j hj, ite_eq_right (by rw [beq_iff_eq]; exact fun e => hnotN j hj e.symm)]
        exact hmg j hj
      · rw [hgetN, ite_eq_left (by rw [beq_iff_eq])]
    · intro j hj hj0
      simp only [Array.size_push] at hj
      have hpget : ∀ k < S.1.size, (S.2.1.push i)[k]! = S.2.1[k]! := by
        intro k hk
        rw [arr_getN, arr_getN, Array.toList_push, getD_append_left (by simp; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · obtain ⟨h1, s', hs', h2⟩ := hpar j hj hj0
        rw [hpget j hj, hgetS j hj, hgetS _ (by omega)]
        exact ⟨h1, s', hs', h2⟩
      · have e : (S.2.1.push i)[S.1.size]! = i := by
          rw [arr_getN, Array.toList_push, ← hps]
          rw [show S.2.1.size = S.2.1.toList.length by simp, getD_append_len]
        rw [e, hgetN, hgetS i hi, ← hcdef]
        exact ⟨hi, s, hsG, rfl⟩
    · exact ⟨by simpa [newE] using hok, S.1.size, by simp, by rw [hgetN]⟩

theorem kids_corr (hw : n ≤ 2 ^ w) {T : List Nat} {i : Nat} : ∀ (Gp : List (Nat × Array Nat))
    (es : ES) (S : St), (∀ p ∈ Gp, Rep n w p.1 p.2 ∧ p.2 ∈ G) → Corr n w nb L G es S →
    i < S.1.size → S.1[i]! = T →
    Corr n w nb L G (kidsW w nb (imgsW w) (Gp.map Prod.fst) i T es)
      ((Gp.map Prod.snd).foldl (bodyB n nb i T) S) ∧
    ∃ new, Ext S ((Gp.map Prod.snd).foldl (bodyB n nb i T) S) new ∧
      (kidsW w nb (imgsW w) (Gp.map Prod.fst) i T es).fr = new.reverse ++ es.fr ∧
      ((kidsW w nb (imgsW w) (Gp.map Prod.fst) i T es).ok = true → es.ok = true ∧
        ∀ p ∈ Gp, ∃ j < ((Gp.map Prod.snd).foldl (bodyB n nb i T) S).1.size,
          ((Gp.map Prod.snd).foldl (bodyB n nb i T) S).1[j]! = applyTab p.2 T)
  | [], es, S, _, hc, _, _ => ⟨hc, [], by simp [Ext], by simp [kidsW_nil], fun h =>
      ⟨by simpa [kidsW_nil] using h, fun p hp => by simp at hp⟩⟩
  | p :: Gp, es, S, hG, hc, hi, hT => by
    rw [List.map_cons, List.map_cons, kidsW_cons, List.foldl_cons]
    have hp := hG p (List.mem_cons_self ..)
    obtain ⟨hc1, new1, he1, hf1, hok1⟩ := step_corr hw hc hi hp.1 hp.2
    rw [hT] at hc1 he1 hf1 hok1
    have hi1 : i < (bodyB n nb i T S p.2).1.size := by rw [ext_size he1]; omega
    have hT1 : (bodyB n nb i T S p.2).1[i]! = T := by rw [ext_get he1 hi, hT]
    obtain ⟨hc2, new2, he2, hf2, hok2⟩ := kids_corr hw Gp _ _
      (fun q hq => hG q (List.mem_cons_of_mem _ hq)) hc1 hi1 hT1
    refine ⟨hc2, new1 ++ new2, ext_trans he1 he2, by rw [hf2, hf1, List.reverse_append,
      List.append_assoc], fun hok => ?_⟩
    obtain ⟨h1, h2⟩ := hok2 hok
    obtain ⟨h3, j, hj, h4⟩ := hok1 h1
    refine ⟨h3, fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · refine ⟨j, by rw [ext_size he2]; omega, ?_⟩
      rw [ext_get he2 hj, h4]
    · exact h2 q hq

theorem round_corr (hw : n ≤ 2 ^ w) {gi : Nat} {Gp : List (Nat × Array Nat)}
    (hG : ∀ p ∈ Gp, Rep n w p.1 p.2 ∧ p.2 ∈ G) (hGs : Gp.map Prod.snd = G) :
    ∀ (F : List (List Nat)) (i : Nat) (es : ES) (S : St), Corr n w nb L G es S →
    (∀ t < F.length, i + t < S.1.size ∧ S.1[i + t]! = F.getD t []) →
    ∃ S', Corr n w nb L G (roundW w nb gi (imgsW w) (Gp.map Prod.fst) F i es) S' ∧
      (∀ f, bfsLoopB n nb G (F.length + f) i S = bfsLoopB n nb G f (i + F.length) S') ∧
      ∃ new, Ext S S' new ∧
        (roundW w nb gi (imgsW w) (Gp.map Prod.fst) F i es).fr = new.reverse ++ es.fr ∧
        ((roundW w nb gi (imgsW w) (Gp.map Prod.fst) F i es).ok = true → es.ok = true ∧
          ∀ t < F.length, ∀ s ∈ G, ∃ j < S'.1.size, S'.1[j]! = applyTab s S'.1[i + t]!)
  | [], i, es, S, hc, _ => ⟨S, hc, fun f => by simp, [], by simp [Ext], by simp [roundW_nil],
      fun h => ⟨by simpa [roundW_nil] using h, fun t ht => by simp at ht⟩⟩
  | T :: F, i, es, S, hc, hF => by
    rw [roundW_cons]
    have h0 := hF 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    obtain ⟨hc1, new1, he1, hf1, hok1⟩ := kids_corr (L := L) hw Gp es S hG hc h0.1 h0.2
    rw [hGs] at hc1 he1 hok1
    have hF1 : ∀ t < F.length, i + 1 + t < (G.foldl (bodyB n nb i T) S).1.size ∧
        (G.foldl (bodyB n nb i T) S).1[i + 1 + t]! = F.getD t [] := by
      intro t ht
      have := hF (t + 1) (by simp; omega)
      rw [List.getD_cons_succ, show i + (t + 1) = i + 1 + t by omega] at this
      exact ⟨by rw [ext_size he1]; omega, by rw [ext_get he1 this.1, this.2]⟩
    obtain ⟨S2, hc2, hb2, new2, he2, hf2, hok2⟩ := round_corr hw hG hGs F (i + 1)
      (clfix gi (kidsW w nb (imgsW w) (Gp.map Prod.fst) i T es)) _ hc1 hF1
    refine ⟨S2, hc2, fun f => ?_, new1 ++ new2, ext_trans he1 he2, ?_, fun hok => ?_⟩
    · rw [List.length_cons, show F.length + 1 + f = (F.length + f) + 1 by omega, bfsLoopB_succ,
        ite_eq_left h0.1, h0.2, hb2, show i + 1 + F.length = i + (F.length + 1) by omega]
    · rw [hf2]
      change new2.reverse ++ (kidsW w nb (imgsW w) (Gp.map Prod.fst) i T es).fr = _
      rw [hf1, List.reverse_append, List.append_assoc]
    · obtain ⟨h1, h2⟩ := hok2 hok
      obtain ⟨h3, h4⟩ := hok1 h1
      refine ⟨h3, fun t ht s hs => ?_⟩
      cases t with
      | zero =>
        rw [← hGs] at hs
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
        obtain ⟨j, hj, e⟩ := h4 p hp
        refine ⟨j, by rw [ext_size he2]; omega, ?_⟩
        rw [ext_get he2 hj, e, Nat.add_zero, ext_get (ext_trans he1 he2) h0.1, h0.2]
      | succ t =>
        have := h2 t (by simpa using ht) s hs
        rwa [show i + 1 + t = i + (t + 1) by omega] at this

@[expose] noncomputable def S0 (n nb : Nat) (o : List Nat) : St :=
  (#[o], #[0], (∅ : Std.HashMap Nat Nat).insert (keyNat n nb o) 0)

theorem enumW_zero (w nb gi : Nat) (app : Nat → List Nat → List Nat) (Gc o : List Nat) :
    enumW w nb gi app Gc o 0 = (ES.mk (insTT TT.lf (keyW w nb o) 0 o) 1 [o] [0] [] [] true, 0, [o]) :=
  rfl

theorem enumW_succ (w nb gi : Nat) (app : Nat → List Nat → List Nat) (Gc o : List Nat) (dd : Nat)
    (st : ES) (i : Nat) (F : List (List Nat)) (h : enumW w nb gi app Gc o dd = (st, i, F)) :
    enumW w nb gi app Gc o (dd + 1) =
      ((fun (st' : ES) => (ES.mk st'.kt st'.cnt st'.rev st'.par st'.cl [] st'.ok, st.cnt,
          revOn st'.fr []))
        (roundW w nb gi app Gc F i (ES.mk st.kt st.cnt st.rev st.par st.cl [] st.ok))) := by
  have e : enumW w nb gi app Gc o (dd + 1) =
      Prod.rec (motive := fun _ => ES × Nat × List (List Nat)) (fun st p =>
        Prod.rec (motive := fun _ => ES × Nat × List (List Nat)) (fun i F =>
          (fun (st' : ES) => Prod.mk (ES.mk st'.kt st'.cnt st'.rev st'.par st'.cl [] st'.ok)
              (Prod.mk st.cnt (revOn st'.fr [])))
            (roundW w nb gi app Gc F i (ES.mk st.kt st.cnt st.rev st.par st.cl [] st.ok))) p)
        (enumW w nb gi app Gc o dd) := rfl
  rw [e, h]

theorem enum_corr (hw : n ≤ 2 ^ w) {gi : Nat} {Gp : List (Nat × Array Nat)}
    (hG : ∀ p ∈ Gp, Rep n w p.1 p.2 ∧ p.2 ∈ G) (hGs : Gp.map Prod.snd = G) {o : List Nat}
    (ho : Val n L o) : ∀ dd, ∃ S,
      Corr n w nb L G (enumW w nb gi (imgsW w) (Gp.map Prod.fst) o dd).1 S ∧
      (∀ f, bfsLoopB n nb G ((enumW w nb gi (imgsW w) (Gp.map Prod.fst) o dd).2.1 + f) 0
          (S0 n nb o) =
        bfsLoopB n nb G f (enumW w nb gi (imgsW w) (Gp.map Prod.fst) o dd).2.1 S) ∧
      (enumW w nb gi (imgsW w) (Gp.map Prod.fst) o dd).2.2 =
        S.1.toList.drop (enumW w nb gi (imgsW w) (Gp.map Prod.fst) o dd).2.1 ∧
      (enumW w nb gi (imgsW w) (Gp.map Prod.fst) o dd).2.1 ≤ S.1.size ∧
      ((enumW w nb gi (imgsW w) (Gp.map Prod.fst) o dd).1.ok = true →
        ∀ j < (enumW w nb gi (imgsW w) (Gp.map Prod.fst) o dd).2.1, ∀ s ∈ G,
          ∃ k < S.1.size, S.1[k]! = applyTab s S.1[j]!) ∧
      ∃ new, Ext (S0 n nb o) S new
  | 0 => by
    rw [enumW_zero]
    have hget : ∀ i < (S0 n nb o).1.size, (S0 n nb o).1[i]! = o := by
      intro i hi
      have hi0 : i = 0 := by simpa [S0] using hi
      subst hi0
      rfl
    have hsz : (S0 n nb o).1.size = 1 := rfl
    refine ⟨S0 n nb o, ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun f => by simp, by
      simp [S0], by simp [S0], fun _ j hj => by simp at hj, [], by simp [Ext]⟩
    · intro T hT
      simp only [S0, List.mem_singleton] at hT
      rw [hT]
      exact ho
    · change OrdT (insTT TT.lf (keyW w nb o) 0 o)
      rw [insTT_eq]
      exact ord_insG ltK_iff _ _ _ trivial
    · intro y
      change memKT (insTT TT.lf (keyW w nb o) 0 o) y ↔ _
      rw [insTT_eq, mem_insG ltK_iff]
      simp only [memKT, or_false, hsz]
      constructor
      · rintro rfl
        exact ⟨0, by omega, by rw [hget 0 (by rw [hsz]; omega)]⟩
      · rintro ⟨i, hi, rfl⟩
        rw [hget i (by rw [hsz]; omega)]
    · intro i hi
      change idxG ltK (insTT TT.lf (keyW w nb o) 0 o) _ = i ∧
        tabG ltK (insTT TT.lf (keyW w nb o) 0 o) _ = _
      have hn : ¬ memKT TT.lf (keyW w nb o) := fun h => h
      rw [hget i hi, insTT_eq, (look_insG_self _ _ _ hn).1, (look_insG_self _ _ _ hn).2]
      rw [hsz] at hi
      exact ⟨by omega, rfl⟩
    · intro y
      simp only [S0, Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
        beq_iff_eq]
      constructor
      · rintro rfl
        exact ⟨0, by simp, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        rfl
    · intro i hi
      rw [hget i hi]
      simp only [S0, Std.HashMap.getD_insert, beq_self_eq_true, ite_true]
      rw [hsz] at hi
      omega
    · intro i hi hi0
      rw [hsz] at hi
      omega
  | dd + 1 => by
    obtain ⟨S, hc, hb, hF, hle, hok, new0, he0⟩ := enum_corr hw hG hGs ho dd
    rcases hE : enumW w nb gi (imgsW w) (Gp.map Prod.fst) o dd with ⟨st, i, F⟩
    rw [hE] at hc hb hF hle hok
    dsimp only at hc hb hF hle hok
    rw [enumW_succ w nb gi (imgsW w) (Gp.map Prod.fst) o dd st i F hE]
    have hc0 : Corr n w nb L G (ES.mk st.kt st.cnt st.rev st.par st.cl [] st.ok) S := hc
    have hFi : ∀ t < F.length, i + t < S.1.size ∧ S.1[i + t]! = F.getD t [] := by
      intro t ht
      rw [hF] at ht ⊢
      simp only [List.length_drop, Array.length_toList] at ht
      refine ⟨by omega, ?_⟩
      rw [arr_getL, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
    obtain ⟨S', hc', hb', new, he, hf, hok'⟩ := round_corr (gi := gi) hw hG hGs F i _ S hc0 hFi
    have hlen : i + F.length = S.1.size := by
      rw [hF, List.length_drop, Array.length_toList]
      omega
    have hcnt : st.cnt = S.1.size := hc.2.2.1
    refine ⟨S', hc', fun f => ?_, ?_, ?_, fun hk j hj s hs => ?_, new0 ++ new, ext_trans he0 he⟩
    · dsimp only
      rw [hcnt, ← hlen, Nat.add_assoc, hb, hb', hlen]
    · dsimp only
      rw [revOn_eq, List.append_nil, hf, List.append_nil, List.reverse_reverse, hcnt, he,
        List.drop_left' (by simp)]
    · dsimp only
      rw [ext_size he, hcnt]
      omega
    · dsimp only at hk hj
      obtain ⟨h1, h2⟩ := hok' hk
      rw [hcnt] at hj
      rcases Nat.lt_or_ge j i with hji | hji
      · obtain ⟨k, hk, e⟩ := hok h1 j hji s hs
        refine ⟨k, by rw [ext_size he]; omega, ?_⟩
        rw [ext_get he hk, ext_get he (by omega), e]
      · have := h2 (j - i) (by omega) s hs
        rwa [show i + (j - i) = j by omega] at this

end Sim

theorem push_fold {β : Type} (h : β → Nat) : ∀ (H : List β) (acc : Array Nat),
    (H.foldl (fun acc' s => acc'.push (h s)) acc).toList = acc.toList ++ H.map h
  | [], acc => by simp
  | s :: H, acc => by
    rw [List.foldl_cons, push_fold h H, Array.toList_push, List.map_cons, List.append_assoc]
    rfl

theorem cl_fold {β : Type} (H : List β) (h : Nat → β → Nat) : ∀ m : Nat,
    ((List.range m).foldl (fun acc i => H.foldl (fun acc' s => acc'.push (h i s)) acc)
      (#[] : Array Nat)).toList = (List.range m).flatMap fun i => H.map (h i)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, push_fold,
      cl_fold H h m, List.flatMap_append, List.flatMap_singleton]

theorem flatMap_getD {β : Type} [Inhabited β] (H : List β) (h : Nat → β → Nat) : ∀ m : Nat,
    ((List.range m).flatMap fun i => H.map (h i)).length = m * H.length ∧
    ∀ i < m, ∀ j < H.length,
      ((List.range m).flatMap fun i => H.map (h i)).getD (i * H.length + j) 0 = h i H[j]!
  | 0 => by simp
  | m + 1 => by
    obtain ⟨h1, h2⟩ := flatMap_getD H h m
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine ⟨by rw [List.length_append, h1, List.length_map, Nat.succ_mul], fun i hi j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · have hlt : i * H.length + j < m * H.length := by
        have : (i + 1) * H.length ≤ m * H.length := Nat.mul_le_mul_right _ hi
        rw [Nat.succ_mul] at this
        omega
      rw [getD_append_left (by rw [h1]; exact hlt), h2 i hi j hj]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h1]; omega), h1,
        Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
        Option.getD_some, getElem!_pos H j hj]

theorem closed_inv {n : Nat} {s si : Array Nat} (hinv : ∀ q < n, img si (img s q) = q) {A : List (List Nat)} (hA : ∀ T ∈ A, ∀ x ∈ T, x < n)
    (hcl : ∀ T ∈ A, applyTab s T ∈ A) : ∀ T ∈ A, applyTab si T ∈ A := by
  classical
  have hback : ∀ U ∈ A, applyTab si (applyTab s U) = U := by
    intro U hU
    rw [applyTab, applyTab, List.map_map]
    conv_rhs => rw [← List.map_id U]
    exact List.map_congr_left fun x hx => hinv x (hA U hU x hx)
  have hinj : Set.InjOn (applyTab s) (A.toFinset : Set (List Nat)) := by
    intro U hU V hV e
    have hU' : U ∈ A := by simpa using hU
    have hV' : V ∈ A := by simpa using hV
    rw [← hback U hU', ← hback V hV', e]
  have hsub : A.toFinset.image (applyTab s) ⊆ A.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨U, hU, rfl⟩ := hx
    rw [List.mem_toFinset] at hU ⊢
    exact hcl U hU
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])
  intro T hT
  have hT' : T ∈ A.toFinset.image (applyTab s) := by rw [heq]; simpa using hT
  rw [Finset.mem_image] at hT'
  obtain ⟨U, hU, rfl⟩ := hT'
  rw [List.mem_toFinset] at hU
  rw [hback U hU]
  exact hU

@[expose] noncomputable def comLoop (nb : Nat) (app : Nat → List Nat → List Nat) (T0 : List Nat) :
    List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun g _ ih rest => andB (eqLW (takeK nb rest) (app g T0)) (ih (dropK nb rest)))

theorem comW_eq (nb : Nat) (app : Nat → List Nat → List Nat) (G T : List Nat) :
    comW nb app G T = comLoop nb app (takeK nb T) G (dropK nb T) := rfl

theorem comLoop_true {n w nb : Nat} {T0 : List Nat} (hT0 : ∀ x ∈ T0, x < n)
    (hl0 : T0.length = nb) : ∀ (Gp : List (Nat × Array Nat)) (rest : List Nat),
    (∀ p ∈ Gp, Rep n w p.1 p.2) → nb * Gp.length ≤ rest.length →
    (∀ t < Gp.length, ∀ j < nb, rest.getD (nb * t + j) 0 = img (Gp.getD t (0, #[])).2 (T0.getD j 0)) →
    comLoop nb (imgsW w) T0 (Gp.map Prod.fst) rest = true
  | [], _, _, _, _ => rfl
  | p :: Gp, rest, hG, hlen, hc => by
    change andB (eqLW (takeK nb rest) (imgsW w p.1 T0))
      (comLoop nb (imgsW w) T0 (Gp.map Prod.fst) (dropK nb rest)) = true
    have hp := hG p (List.mem_cons_self ..)
    rw [andB_eq, Bool.and_eq_true, eqLW_iff, takeK_eq, dropK_eq, imgsW_rep hp hT0]
    simp only [List.length_cons, Nat.mul_succ] at hlen
    refine ⟨?_, comLoop_true hT0 hl0 Gp _ (fun q hq => hG q (List.mem_cons_of_mem _ hq))
      (by rw [List.length_drop]; omega) fun t ht j hj => ?_⟩
    · apply List.ext_getElem (by simp [applyTab, hl0]; omega)
      intro j h1 h2
      have hj : j < nb := by simp at h1; omega
      have e := hc 0 (by simp) j hj
      rw [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
      simp only [applyTab, List.getElem_map, List.getElem_take]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at e
      exact e
    · have e := hc (t + 1) (by simp; omega) j hj
      rw [List.getD_cons_succ, show nb * (t + 1) + j = nb + (nb * t + j) by rw [Nat.mul_succ]; omega]
        at e
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
      exact e

theorem fstN_eq (R : List Nat) : ∀ qp : List (Nat × Nat), fstN R qp = qp.map fun p => nodeK R p.1
  | [] => rfl
  | p :: qp => by
    change nodeK R p.1 :: fstN R qp = _
    rw [fstN_eq R qp, List.map_cons]

theorem enumOK_spec {k fuel : Nat} {E : ES × Nat × List (List Nat)} (h : enumOK k fuel E = true) :
    E.2.2 = [] ∧ E.1.cnt ≤ fuel ∧ E.1.cnt = 2 ^ k ∧ E.1.ok = true := by
  rw [enumOK] at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3, h4⟩
  revert h1
  cases E.2.2 with
  | nil => exact fun _ => rfl
  | cons _ _ => exact fun h => absurd h Bool.false_ne_true

theorem isEnt_spec {w nb : Nat} {t : TT} {c : List Nat} (h : isEnt w nb t c = true) :
    memTT t (keyW w nb c) = true ∧ tabTT t (keyW w nb c) = c := by
  rw [isEnt, P.letB_eq, andB_eq, Bool.and_eq_true, eqLW_iff] at h
  exact h

theorem forall2_pairs {n w : Nat} : ∀ (Gp : List (Nat × Array Nat)), (∀ p ∈ Gp, Rep n w p.1 p.2) →
    List.Forall₂ (fun c s => Rep n w c s) (Gp.map Prod.fst) (Gp.map Prod.snd)
  | [], _ => List.Forall₂.nil
  | p :: Gp, h => List.Forall₂.cons (h p (List.mem_cons_self ..))
      (forall2_pairs Gp fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem getBang_append_left {G Gi : List (Array Nat)} {j : Nat} (hj : j < G.length) :
    (G ++ Gi)[j]! = G[j]! := by
  rw [getElem!_pos (G ++ Gi) j (by simp; omega), getElem!_pos G j hj, List.getElem_append_left hj]

theorem getBang_append_right {G Gi : List (Array Nat)} {j : Nat} (hj : j < Gi.length) :
    (G ++ Gi)[G.length + j]! = Gi[j]! := by
  rw [getElem!_pos (G ++ Gi) _ (by simp; omega), getElem!_pos Gi j hj,
    List.getElem_append_right (by omega)]
  congr 1
  omega

theorem mem_idx {A : Array (List Nat)} {T : List Nat} (h : T ∈ A.toList) :
    ∃ k < A.size, A[k]! = T := by
  obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.1 h
  refine ⟨k, by simpa using hk, ?_⟩
  rw [arr_getL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, e]

theorem get_mem {A : Array (List Nat)} {k : Nat} (hk : k < A.size) : A[k]! ∈ A.toList := by
  rw [arr_getL]
  exact getD_mem (by simpa using hk)

theorem ent_of_corr {n w nb L : Nat} {G : List (Array Nat)} {es : ES} {S : St}
    (hc : Corr n w nb L G es S) {c : List Nat} (h : isEnt w nb es.kt c = true) : c ∈ S.1.toList := by
  obtain ⟨-, -, -, -, -, ho, hm, hl, -⟩ := hc
  obtain ⟨h1, h2⟩ := isEnt_spec h
  rw [memTT_eq, memG_iff ltK_iff ho, hm] at h1
  obtain ⟨i, hi, e⟩ := h1
  have := (hl i hi).2
  rw [e, ← tabTT_eq, h2] at this
  rw [this]
  exact get_mem hi

theorem keys_nodup {n w nb L : Nat} (hw : n ≤ 2 ^ w) {G : List (Array Nat)} {es : ES} {S : St}
    (hc : Corr n w nb L G es S) : (S.1.toList.map (keyNat n nb)).Nodup := by
  obtain ⟨-, -, -, -, hv, -, -, hl, -⟩ := hc
  rw [List.nodup_iff_eq_of_getElem_eq]
  intro i j hi hj e
  simp only [List.length_map, Array.length_toList] at hi hj
  simp only [List.getElem_map, Array.getElem_toList] at e
  rw [← getElem!_pos S.1 i hi, ← getElem!_pos S.1 j hj] at e
  have e' := (keyW_iff_keyNat hw (val_get hv hi) (val_get hv hj)).2 e
  rw [← (hl i hi).1, ← (hl j hj).1, e']

theorem conj_rep {n w : Nat} {cz cg cgi : Nat} {z g gi : Array Nat} (hz : Rep n w cz z)
    (hg : Rep n w cg g) (hgi : Rep n w cgi gi) {p : Nat} (hp : p < n) :
    cjW w cz cg cgi p = conjImg z g gi p := by
  rw [cjW, conjImg, (hg.2 p hp).2, (hz.2 _ (hg.2 p hp).1).2, (hgi.2 _ (hz.2 _ (hg.2 p hp).1).1).2]

theorem conj_lt {n w : Nat} {cz cg cgi : Nat} {z g gi : Array Nat} (hz : Rep n w cz z)
    (hg : Rep n w cg g) (hgi : Rep n w cgi gi) {p : Nat} (hp : p < n) : conjImg z g gi p < n :=
  (hgi.2 _ (hz.2 _ (hg.2 p hp).1).1).1

theorem conj_tab {n w : Nat} {cz cg cgi : Nat} {z g gi : Array Nat} (hz : Rep n w cz z)
    (hg : Rep n w cg g) (hgi : Rep n w cgi gi) {o : List Nat} (ho : ∀ x ∈ o, x < n) :
    imgsW w cgi (imgsW w cz (imgsW w cg o)) = o.map (conjImg z g gi) := by
  rw [imgsW_rep hg ho, imgsW_rep hz (applyTab_lt hg ho),
    imgsW_rep hgi (applyTab_lt hz (applyTab_lt hg ho))]
  simp only [applyTab, List.map_map]
  rfl

end CFSG.KC.LQT.BW.Pf

end

public section

namespace CFSG.KC.LQT.BW

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.LQT.BW.Pf

theorem baseW_sound_proved {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat)
    (prog qp : List (Nat × Nat)) (zn gn gin hn hin k fuel d : Nat)
    (h : baseWK n w B ta tb prog qp zn gn gin hn hin k fuel d = true) :
    BaseCertS n B (slpTabsA ta.toArray tb.toArray prog) qp zn gn gin hn hin
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 k := by
  rw [baseWK, andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨hta, htb, hso, hR⟩ := h
  obtain ⟨hlen, hrep⟩ := slpW_rep hw hta htb hso
  generalize slpTabsA ta.toArray tb.toArray prog = T at hlen hrep ⊢
  generalize slpW n w (codeK w ta) (codeK w tb) prog = R at hlen hrep hR
  rw [baseWR, andB_eq, andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true] at hR
  obtain ⟨hqp, hbd, hg, hh, hQ⟩ := hR
  rw [qpW, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, allA_eq, allA_eq, allL_eq,
    List.all_eq_true, List.all_eq_true, List.all_eq_true] at hqp
  obtain ⟨hq1, hq2, hB⟩ := hqp
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true, Nat.blt_eq, hlen] at hbd
  obtain ⟨hzn, hgn, hgin, hhn, hhin⟩ := hbd
  have hq1' : ∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size := by
    intro p hp
    have := hq1 p hp
    rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, hlen] at this
    exact this
  have hB' : ∀ b ∈ B, b < n := fun b hb => by simpa using hB b hb
  set G := qp.map fun p => T[p.1]! with hGdef
  set Gi := qp.map fun p => T[p.2]! with hGidef
  set Gp := qp.map fun p => (nodeK R p.1, T[p.1]!) with hGpdef
  have hGp : ∀ p ∈ Gp, Rep n w p.1 p.2 ∧ p.2 ∈ G := by
    intro p hp
    rw [hGpdef, List.mem_map] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact ⟨hrep a.1 (hq1' a ha).1, List.mem_map.2 ⟨a, ha, rfl⟩⟩
  have hGs : Gp.map Prod.snd = G := by rw [hGpdef, hGdef, List.map_map]; rfl
  have hfst : fstN R qp = Gp.map Prod.fst := by rw [fstN_eq, hGpdef, List.map_map]; rfl
  have hGrep : ∀ s ∈ G, ∃ c, Rep n w c s := by
    intro s hs
    rw [← hGs, List.mem_map] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact ⟨p.1, (hGp p hp).1⟩
  have hpts : ptsW w B (fstN R qp) = ptsOf B G := by
    rw [hfst, ptsW_eq hB' (forall2_pairs Gp fun p hp => (hGp p hp).1), hGs]
  have hov : Val n (ptsOf B G).length (ptsOf B G) := by
    refine ⟨rfl, fun x hx => ?_⟩
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact hB' x hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨c, hc⟩ := hGrep s hs
      exact (hc.2 b (hB' b hb)).1
  rw [baseWQ, hpts, hfst, lenA_eq, lenA_eq] at hQ
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hQ
  obtain ⟨hE, hcom, hcg, hch, hnc⟩ := hQ
  obtain ⟨S, hc, hb, hF, hle, hok, new0, he0⟩ :=
    enum_corr (nb := B.length) (L := (ptsOf B G).length) (gi := qp.length) hw hGp hGs hov d
  generalize enumW w B.length qp.length (imgsW w) (Gp.map Prod.fst) (ptsOf B G) d = E
    at hE hcom hcg hch hc hb hF hle hok
  obtain ⟨hE1, hE2, hE3, hE4⟩ := enumOK_spec hE
  have hcnt : E.1.cnt = S.1.size := hc.2.2.1
  have hiS : E.2.1 = S.1.size := by
    rw [hE1] at hF
    have : S.1.toList.length ≤ E.2.1 := List.drop_eq_nil_iff.1 hF.symm
    simp at this
    omega
  have hloop : bfsLoopB n B.length G fuel 0 (S0 n B.length (ptsOf B G)) = S := by
    have := hb (fuel - E.2.1)
    rw [show E.2.1 + (fuel - E.2.1) = fuel by omega, hiS, bfsLoopB_stop] at this
    exact this
  unfold S0 at hloop
  have hbe : bfsEnumB n B G Gi fuel = (S.1, S.2.1, (List.range S.1.size).foldl (fun acc i =>
      (G ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0)) acc) #[]) := by
    simp only [bfsEnumB, hloop]
  rw [hbe]
  dsimp only
  have hc' := hc
  obtain ⟨hr, -, -, hps, hv, -, -, -, -, hmg, hpar⟩ := hc'
  have hGl : G.length = qp.length := by rw [hGdef, List.length_map]
  have hGil : Gi.length = qp.length := by rw [hGidef, List.length_map]
  have hGj : ∀ j (hj : j < qp.length), G[j]! = T[qp[j].1]! := by
    intro j hj
    rw [getElem!_pos G j (by omega)]
    simp only [hGdef, List.getElem_map]
  have hGij : ∀ j (hj : j < qp.length), Gi[j]! = T[qp[j].2]! := by
    intro j hj
    rw [getElem!_pos Gi j (by omega)]
    simp only [hGidef, List.getElem_map]
  have hinvq : ∀ a ∈ qp, ∀ q < n, img T[a.2]! (img T[a.1]! q) = q := fun a ha =>
    rep_inv (hrep a.1 (hq1' a ha).1) (hrep a.2 (hq1' a ha).2) hw
      (Nat.eq_of_beq_eq_true (by simpa using hq2 a ha))
  have hokc := hok hE4
  rw [hiS] at hokc
  have hclget : ∀ i < S.1.size, ∀ j < (G ++ Gi).length,
      ((List.range S.1.size).foldl (fun acc i => (G ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0)) acc)
        (#[] : Array Nat))[i * (G.length + Gi.length) + j]! =
      S.2.2.getD (keyNat n B.length (applyTab (G ++ Gi)[j]! S.1[i]!)) 0 := by
    intro i hi j hj
    rw [arr_getN, cl_fold, ← List.length_append]
    exact (flatMap_getD (G ++ Gi) _ S.1.size).2 i hi j hj
  have hidx : ∀ i < S.1.size, ∀ {s : Array Nat} {k' : Nat}, k' < S.1.size →
      S.1[k']! = applyTab s S.1[i]! →
      S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0 = k' := by
    intro i _ s k' hk' e
    rw [← e]
    exact hmg k' hk'
  unfold BaseCertS
  refine ⟨fun p hp => hq1' p hp, hzn, hgn, hgin, hhn, hhin, ?_⟩
  have hm1 : (qp.map fun p => (T[p.1]!, T[p.2]!)).map Prod.fst = G := by
    rw [List.map_map, hGdef]
    rfl
  have hm2 : (qp.map fun p => (T[p.1]!, T[p.2]!)).map Prod.snd = Gi := by
    rw [List.map_map, hGidef]
    rfl
  unfold BaseCert
  rw [hm1, hm2]
  refine ⟨?_, rep_inv (hrep gn hgn) (hrep gin hgin) hw (Nat.eq_of_beq_eq_true hg),
    rep_inv (hrep hn hhn) (hrep hin hhin) hw (Nat.eq_of_beq_eq_true hh), ?_,
    by rw [← hcnt]; exact hE3, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq
    rw [List.mem_map] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact hinvq a ha q hq
  · refine ⟨by rw [ext_size he0]; simp [S0], by rw [ext_get he0 (by simp [S0])]; rfl, hps,
      hpar, keys_nodup hw hc, fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · have hjq : j < qp.length := by omega
      have hs : G[j]! ∈ G := by rw [getElem!_pos G j hj]; exact List.getElem_mem _
      obtain ⟨k', hk', e⟩ := hokc i hi _ hs
      rw [hclget i hi j (by simp; omega), getBang_append_left hj, hidx i hi hk' e]
      exact ⟨hk', e⟩
    · have hjq : j < qp.length := by omega
      have hmem : applyTab Gi[j]! S.1[i]! ∈ S.1.toList := by
        apply closed_inv (s := G[j]!) (n := n)
        · intro q hq
          rw [hGj j hjq, hGij j hjq]
          exact hinvq _ (List.getElem_mem _) q hq
        · exact fun U hU => (hv U hU).2
        · intro U hU
          obtain ⟨i', hi', rfl⟩ := mem_idx hU
          have hs : G[j]! ∈ G := by rw [getElem!_pos G j (by omega)]; exact List.getElem_mem _
          obtain ⟨k', hk', e⟩ := hokc i' hi' _ hs
          rw [← e]
          exact get_mem hk'
        · exact get_mem hi
      obtain ⟨k', hk', e⟩ := mem_idx hmem
      rw [Nat.add_assoc, hclget i hi _ (by simp; omega), getBang_append_right hj,
        hidx i hi hk' e]
      exact ⟨hk', e⟩
  · intro T' hT' hcond
    have hT'v : Val n (ptsOf B G).length T' := hv T' hT'
    have hrev : T' ∈ E.1.rev := by
      rw [hr, List.mem_reverse] at hT'
      exact hT'
    rw [allLL_eq, List.all_eq_true] at hcom
    have := hcom T' hrev
    rw [impB_eq, Bool.or_eq_true, Bool.not_eq_true'] at this
    have hL : (ptsOf B G).length = B.length + B.length * Gp.length := by
      simp [ptsOf, List.length_flatMap, hGpdef, hGdef, Function.comp_def, List.map_const',
        List.sum_replicate, Nat.mul_comm]
    have hcw : comW B.length (imgsW w) (Gp.map Prod.fst) T' = true := by
      rw [comW_eq, takeK_eq, dropK_eq]
      apply comLoop_true (fun x hx => hT'v.2 x (List.mem_of_mem_take hx))
        (by rw [List.length_take, hT'v.1, hL]; omega) Gp _ (fun p hp => (hGp p hp).1)
        (by rw [List.length_drop, hT'v.1, hL]; omega)
      intro t ht j hj
      have hGpt : (Gp.getD t (0, #[])).2 = G.getD t #[] := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hGpdef, hGdef,
          List.getElem?_map, List.getElem?_map]
        cases qp[t]? <;> rfl
      rw [hGpt, List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD (l := List.take _ _), List.getElem?_take_of_lt hj,
        ← List.getD_eq_getElem?_getD, show B.length + (B.length * t + j) =
          B.length * (1 + t) + j by rw [Nat.mul_add, Nat.mul_one]; omega]
      exact hcond t (by rw [hGl]; rw [hGpdef, List.length_map] at ht; exact ht) j hj
    rcases this with h1 | h1
    · rw [hcw] at h1
      exact absurd h1 (by decide)
    · rw [orB_eq, Bool.or_eq_true, eqLW_iff, eqLW_iff, imgsW_rep (hrep zn hzn) hov.2] at h1
      exact h1
  · rw [← conj_tab (hrep zn hzn) (hrep gn hgn) (hrep gin hgin) hov.2]
    exact ent_of_corr hc hcg
  · rw [← conj_tab (hrep zn hzn) (hrep hn hhn) (hrep hin hhin) hov.2]
    exact ent_of_corr hc hch
  · rw [anyL_eq, List.any_eq_true] at hnc
    obtain ⟨b, hb, hne⟩ := hnc
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hb
    refine ⟨j, hj, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    have hbn := hB' _ hb
    rw [notB_eq, Bool.not_eq_true', ← Bool.not_eq_true, P.beq_iff,
      conj_rep (hrep zn hzn) (hrep hn hhn) (hrep hin hhin) hbn,
      conj_rep (hrep zn hzn) (hrep gn hgn) (hrep gin hgin) hbn,
      conj_rep (hrep zn hzn) (hrep gn hgn) (hrep gin hgin)
        (conj_lt (hrep zn hzn) (hrep hn hhn) (hrep hin hhin) hbn),
      conj_rep (hrep zn hzn) (hrep hn hhn) (hrep hin hhin)
        (conj_lt (hrep zn hzn) (hrep gn hgn) (hrep gin hgin) hbn)] at hne
    exact hne

end CFSG.KC.LQT.BW

end
