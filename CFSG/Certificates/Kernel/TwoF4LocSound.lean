module

public import Certificates.Data.Kernel.TwoF4LocK
public import Certificates.Data.TwoF4LocCheck
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.Loops
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.TwoF4LocSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.TwoF4LieK CFSG.KC.TwoF4LocK
  CFSG.Monster.B.Co2.Native CFSG.RuF45 CFSG.TwoF4Lie CFSG.TwoF4Loc

theorem strictB_app' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem all_congr' {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem cn_canon {P : Nat} (hP : cn P = true) : canonK 1755 11 (mask 11) (1755 * 11) P = true := hP

theorem get_of_high {n w P i : Nat} (hP0 : Nat.beq (Nat.shiftRight P (n * w)) 0 = true) :
    (unpack n w P)[i]! = pg w (mask w) P i := by
  have hP : P < 2 ^ (n * w) := Nat.lt_of_div_eq_zero (Nat.two_pow_pos _)
    (by rw [← Nat.shiftRight_eq_div_pow]; exact Nat.eq_of_beq_eq_true hP0)
  by_cases h : i < n
  · unfold unpack
    rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact h), Array.getElem_ofFn]
  · rw [getElem!_neg _ i (by unfold unpack; rw [Array.size_ofFn]; exact h)]
    have hw : n * w ≤ w * i := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left w (by omega)
    have e : Nat.shiftRight P (Nat.mul w i) = 0 := by
      have e1 : Nat.shiftRight P (Nat.mul w i) = P >>> (w * i) := rfl
      rw [e1, Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by decide) hw))
    unfold pg
    rw [e]
    exact (Nat.zero_and _).symm

theorem get_U {P : Nat} (hP : cn P = true) (i : Nat) : (unpack 1755 11 P)[i]! = gp P i := by
  have h := cn_canon hP
  unfold canonK at h
  rw [bAnd_iff, bAnd_iff] at h
  exact get_of_high h.2.1

theorem cn_mul {P Q : Nat} (hP : cn P = true) (hQ : cn Q = true) : cn (mul P Q) = true :=
  CFSG.KC.BfsPin.canonK_pcomp (cn_canon hP) (cn_canon hQ)

theorem comp_U {P Q : Nat} (hP : cn P = true) (hQ : cn Q = true) :
    compA 1755 (unpack 1755 11 P) (unpack 1755 11 Q) = unpack 1755 11 (mul P Q) :=
  CFSG.KC.BfsPin.compA_unpack (cn_canon hP) (cn_canon hQ)

theorem eqA_U {P Q : Nat} (hP : cn P = true) (hQ : cn Q = true) :
    eqA 1755 (unpack 1755 11 P) (unpack 1755 11 Q) = Nat.beq P Q :=
  CFSG.KC.BfsPin.eqA_unpack (cn_canon hP) (cn_canon hQ)

theorem inv_U {P Q : Nat} (h : invP P Q = true) :
    invCand 1755 (unpack 1755 11 P) = unpack 1755 11 Q ∧
      isInvA 1755 (unpack 1755 11 P) (unpack 1755 11 Q) = true :=
  invEqK_sound h

theorem conj_U {C X CI : Nat} (hC : cn C = true) (hX : cn X = true) (hCI : cn CI = true)
    (h : invP C CI = true) :
    locConj (unpack 1755 11 C) (unpack 1755 11 X) = unpack 1755 11 (conj C X CI) ∧
      cn (conj C X CI) = true := by
  refine ⟨?_, cn_mul (cn_mul hC hX) hCI⟩
  unfold locConj
  rw [(inv_U h).1, comp_U hC hX, comp_U (cn_mul hC hX) hCI]
  rfl

variable {F FI : Nat → Nat} {G : Array (Array Nat)}

theorem word_U (hG : G.size = 4 ∧ ∀ j < 4, G[j]! = unpack 1755 11 (F j))
    (hFI : allN 4 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (F j) (FI j)) = true)
    {s : String} {X : Nat} (h : wordIs F FI s X = true) :
    wordOK s = true ∧ wArr G (invArrs 1755 G) s = unpack 1755 11 X ∧ cn X = true := by
  unfold wordIs at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hw, hl⟩, hx⟩, hc⟩ := h
  refine ⟨hw, ?_, hc⟩
  have hk : wordEqK 1755 11 (mask 11) (pidn 1755 11) F FI 4 (wdOf s) X = true := by
    unfold wordEqK
    rw [bAnd_iff, bAnd_iff]
    exact ⟨rfl, hl, hx⟩
  unfold wArr
  rw [evalArr_eq_wordA]
  exact (wordEqK_sound hG hFI hk).1

variable {lp : Nat → Nat} {pts : Array Nat}

theorem onLine_eq (hpts : ∀ i < 8775, pts[i]! = lp i) {v : Nat} (hv : v < 2925) (p : Nat) :
    onLineP pts p v = onLineR lp p v := by
  unfold onLineP onLineR
  rw [hpts (3 * v) (by omega), hpts (3 * v + 1) (by omega), hpts (3 * v + 2) (by omega)]

theorem fixesH_U {P : Nat} (hP : cn P = true) : fixesH pts (unpack 1755 11 P) = fixHK P := by
  unfold fixesH actOK fixHK
  rw [if_pos (by norm_num), get_U hP]
  simp

theorem fixesN_U (hpts : ∀ i < 8775, pts[i]! = lp i) {P : Nat} (hP : cn P = true) :
    fixesN pts (unpack 1755 11 P) = fixNK lp P := by
  unfold fixesN actOK fixNK lineMapsP
  rw [if_neg (by norm_num)]
  simp only [Nat.le_refl, decide_true, Nat.sub_self, Bool.true_and]
  have h4680 : decide (1755 < 4680) = true := by decide
  rw [h4680, Bool.true_and]
  apply all_congr'
  intro k hk
  have hk3 := List.mem_range.1 hk
  rw [hpts _ (by omega), get_U hP, onLine_eq hpts (by norm_num)]

theorem fixesS_U (hpts : ∀ i < 8775, pts[i]! = lp i) {P : Nat} (hP : cn P = true) :
    fixesS pts (unpack 1755 11 P) = fixSK lp P := by
  unfold fixesS fixSK
  rw [fixesH_U hP, fixesN_U hpts hP]

theorem locCol_eq (hpts : ∀ i < 8775, pts[i]! = lp i) : locCol pts = colK lp := by
  unfold locCol colK
  rw [List.filter_congr fun w hw => by rw [onLine_eq hpts (List.mem_range.1 hw)]]
  apply flatMap_congr'
  intro w hw
  have hw' := List.mem_range.1 (List.mem_filter.1 hw).1
  rw [hpts (3 * w) (by omega), hpts (3 * w + 1) (by omega), hpts (3 * w + 2) (by omega)]

theorem locCollFixed_U (hpts : ∀ i < 8775, pts[i]! = lp i) {P : Nat} (hP : cn P = true) :
    locCollFixed pts (unpack 1755 11 P) = collK lp P := by
  unfold locCollFixed collK
  rw [locCol_eq hpts]
  exact all_congr' fun q _ => by rw [get_U hP]

theorem all_of_mem {cl : List Nat} (h1 : ((colK lp).all fun x => cl.contains x) = true)
    (h2 : (cl.all fun x => (colK lp).contains x) = true) (f : Nat → Bool) :
    cl.all f = (colK lp).all f := by
  rw [List.all_eq_true] at h1 h2
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  constructor
  · intro h x hx
    exact h x (by simpa using h1 x hx)
  · intro h x hx
    exact h x (by simpa using h2 x hx)

theorem locFix_U {P : Nat} (hP : cn P = true) : locFix (unpack 1755 11 P) = fixL P := by
  unfold locFix fixL
  exact List.filter_congr fun p _ => by rw [get_U hP]

theorem locLineOK_U (hpts : ∀ i < 8775, pts[i]! = lp i) {C : Nat} (hC : cn C = true) :
    locLineOK pts (unpack 1755 11 C) = lineK lp C := by
  unfold locLineOK lineK
  simp only [onLine_eq hpts (show (0 : Nat) < 2925 by norm_num), get_U hC]
  congr 1
  apply all_congr'
  intro k hk
  rw [hpts k (by have := List.mem_range.1 hk; omega)]

theorem locVOK_U {Z Z1 Z2 : Nat} (hZ : cn Z = true) (hZ1 : cn Z1 = true) (hZ2 : cn Z2 = true) :
    locVOK (unpack 1755 11 Z) (unpack 1755 11 Z1) (unpack 1755 11 Z2) = vK Z Z1 Z2 := by
  unfold locVOK vK
  rw [comp_U hZ hZ1, comp_U hZ1 hZ, eqA_U (cn_mul hZ hZ1) hZ2,
    eqA_U (cn_mul hZ hZ1) (cn_mul hZ1 hZ), eqA_U hZ hZ1]

theorem locQOK_U {T Z Z1 Q : Nat} (hT : cn T = true) (hZ : cn Z = true) (hZ1 : cn Z1 = true)
    (hQ : cn Q = true) :
    locQOK (unpack 1755 11 T) (unpack 1755 11 Z) (unpack 1755 11 Z1) (unpack 1755 11 Q) =
      qK T Z Z1 Q := by
  unfold locQOK qK
  rw [comp_U hQ hQ, comp_U hQ hT, comp_U hT hQ, comp_U hQ hZ1, comp_U hZ1 hQ,
    eqA_U (cn_mul hQ hQ) hZ, eqA_U (cn_mul hQ hT) (cn_mul hT hQ),
    eqA_U (cn_mul hQ hZ1) (cn_mul hZ1 hQ)]

theorem chain_U (hG : G.size = 4 ∧ ∀ j < 4, G[j]! = unpack 1755 11 (F j))
    (hFI : allN 4 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (F j) (FI j)) = true)
    (hpts : ∀ i < 8775, pts[i]! = lp i) {cl : List Nat}
    (hcl : ∀ f : Nat → Bool, cl.all f = (colK lp).all f) {Z : Nat} (hZ : cn Z = true)
    {W WI : Nat → Nat} {ws : List String} (hW : wordsK F FI W WI ws = true) :
    ∀ (ch : List (Nat × Nat)) (A B : Nat), (∀ e ∈ ch, e.2 < ws.length) → cn A = true →
      cn B = true → chainK lp cl Z W WI ch A B = true →
      locChainOK pts G (invArrs 1755 G) (unpack 1755 11 Z) (unpack 1755 11 A)
        (unpack 1755 11 B) (ch.map fun e => (e.1, ws.getD e.2 "")) = true := by
  intro ch
  induction ch with
  | nil =>
    intro A B _ hA hB h
    change (Nat.beq A Z && !(cl.all fun q => gp B q == q)) = true at h
    simp only [List.map_nil, locChainOK]
    rw [eqA_U hA hZ, locCollFixed_U hpts hB]
    unfold collK
    rw [← hcl]
    exact h
  | cons e rest ih =>
    intro A B hidx hA hB h
    obtain ⟨kd, j⟩ := e
    have hj : j < ws.length := hidx (kd, j) List.mem_cons_self
    unfold wordsK at hW
    have hWj := List.all_eq_true.1 hW j (List.mem_range.2 hj)
    simp only [Bool.and_eq_true] at hWj
    obtain ⟨⟨hwi, hci⟩, hinv⟩ := hWj
    obtain ⟨hwo, hwa, hcw⟩ := word_U hG hFI hwi
    obtain ⟨eA, cA⟩ := conj_U hcw hA hci hinv
    obtain ⟨eB, cB⟩ := conj_U hcw hB hci hinv
    change (strictB (conj (W j) A (WI j)) fun A' => strictB (conj (W j) B (WI j)) fun B' =>
        (if kd == 0 then fixHK (W j) else fixNK lp (W j)) && fixSK lp A' && fixSK lp B' &&
          chainK lp cl Z W WI rest A' B') = true at h
    rw [strictB_app', strictB_app'] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hk, hA'⟩, hB'⟩, hr⟩ := h
    simp only [List.map_cons, locChainOK]
    rw [hwa, (inv_U hinv).1, (inv_U hinv).2, eA, eB, fixesS_U hpts cA,
      fixesS_U hpts cB, fixesH_U hcw, fixesN_U hpts hcw, hwo, hA', hB',
      ih _ _ (fun e he => hidx e (List.mem_cons_of_mem _ he)) cA cB hr]
    simpa using hk

theorem row_U (hG : G.size = 4 ∧ ∀ j < 4, G[j]! = unpack 1755 11 (F j))
    (hFI : allN 4 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (F j) (FI j)) = true)
    (hpts : ∀ i < 8775, pts[i]! = lp i) {cl : List Nat}
    (hcl : ∀ f : Nat → Bool, cl.all f = (colK lp).all f) {Z T Z1 Z2 : Nat} (hZ : cn Z = true)
    (hT : cn T = true) (hZ1 : cn Z1 = true) (hZ2 : cn Z2 = true)
    {W WI : Nat → Nat} {ws : List String} (hW : wordsK F FI W WI ws = true)
    {M MI p : Nat} {w : String} {ch : List (Nat × Nat)} (hidx : ∀ e ∈ ch, e.2 < ws.length)
    (h : TwoF4LocK.rowK F FI lp W WI cl Z T Z1 Z2 M MI p w ch = true) :
    (wordOK w && (wArr G (invArrs 1755 G) w)[0]! == p &&
      isInvA 1755 (wArr G (invArrs 1755 G) w) (invCand 1755 (wArr G (invArrs 1755 G) w)) &&
      (eqA 1755 (locConj (wArr G (invArrs 1755 G) w) (unpack 1755 11 Z)) (unpack 1755 11 Z) ||
        eqA 1755 (locConj (wArr G (invArrs 1755 G) w) (unpack 1755 11 Z)) (unpack 1755 11 Z1) ||
        eqA 1755 (locConj (wArr G (invArrs 1755 G) w) (unpack 1755 11 Z)) (unpack 1755 11 Z2) ||
        (fixesS pts (locConj (wArr G (invArrs 1755 G) w) (unpack 1755 11 Z)) &&
          fixesS pts (unpack 1755 11 T) &&
          locChainOK pts G (invArrs 1755 G) (unpack 1755 11 Z)
            (locConj (wArr G (invArrs 1755 G) w) (unpack 1755 11 Z)) (unpack 1755 11 T)
            (ch.map fun e => (e.1, ws.getD e.2 ""))))) = true := by
  unfold TwoF4LocK.rowK at h
  rw [strictB_app'] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hwi, hci⟩, hinv⟩, hp⟩, hr⟩ := h
  obtain ⟨hwo, hwa, hcm⟩ := word_U hG hFI hwi
  obtain ⟨eU, cU⟩ := conj_U hcm hZ hci hinv
  rw [hwa, (inv_U hinv).1, (inv_U hinv).2, eU, eqA_U cU hZ, eqA_U cU hZ1,
    eqA_U cU hZ2, fixesS_U hpts cU, fixesS_U hpts hT, get_U hcm, hwo, hp, Bool.true_and,
    Bool.true_and, Bool.true_and]
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hr ⊢
  rcases hr with ((h1 | h1) | h1) | ⟨⟨h1, h2⟩, h3⟩
  · exact Or.inl (Or.inl (Or.inl h1))
  · exact Or.inl (Or.inl (Or.inr h1))
  · exact Or.inl (Or.inr h1)
  · exact Or.inr ⟨⟨h1, h2⟩, chain_U hG hFI hpts hcl hZ hW ch _ _ hidx cU hT h3⟩

end CFSG.KC.TwoF4LocSound

end
