module

public import Certificates.Data.Kernel.LyS0.Check
public import Certificates.Data.E27.LyS0
public import CFSG.HardMathSupport.Foote.E27.TableMat
public import CFSG.Certificates.Kernel.SporSch.LyMatSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.K
public import CFSG.Certificates.Kernel.LyS0.Parse
import CFSG.Certificates.Kernel.SporSch.LyLoop
import Mathlib.Data.List.Nodup
public import CFSG.Sporadic.Schreier.LyCheckSeven

public section

namespace CFSG.KS.LyS0K

open CFSG.KD.LyS0 CFSG.KC.Ord CFSG.KC.Enum CFSG.KS.SporSch.LyM CFSG.KS.LyS0Parse
open CFSG.Sporadic.Ly.S0 CFSG.Sporadic.He.Native CFSG.HardMathSupport.Foote.E27
open CFSG.KS.Ord CFSG.Sporadic.Ly.Native

theorem blt_of {a b : Nat} (h : Nat.blt a b = true) : a < b := Eq.mp Nat.blt_eq h

theorem blt_iff {a b : Nat} (h : a < b) : Nat.blt a b = true := Eq.mpr Nat.blt_eq h

local notation "U" X:max => unpackL 111 12 1332 X

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) : nIf(c, t, e) = if c then t else e := by cases c <;> rfl

theorem bIf_eq (c t e : Bool) : bIf(c, t, e) = if c then t else e := by cases c <;> rfl

theorem ofFnG {α : Type} [Inhabited α] (P : Nat → α) {n i : Nat} (h : i < n) :
    (Array.ofFn (n := n) fun j => P j.val)[i]! = P i := by
  rw [getElem!_pos (Array.ofFn (n := n) fun j => P j.val) i (by simpa using h), Array.getElem_ofFn]

theorem hv {X : Nat} (h : vld X = true) :
    validM 5 (111 * 1332) CFSG.KD.OrdLy.L CFSG.KD.OrdLy.H X = true := h

theorem mulE {X Y : Nat} (hX : vld X = true) (hY : vld Y = true) :
    mulM 5 111 (U X) (U Y) = U (mul X Y) := (mulR_eq CFSG.KD.OrdLy.consts (hv hX) (hv hY)).1

theorem mulV {X Y : Nat} (hX : vld X = true) (hY : vld Y = true) : vld (mul X Y) = true :=
  (mulR_eq CFSG.KD.OrdLy.consts (hv hX) (hv hY)).2

theorem idE : idM 111 = U CFSG.KD.OrdLy.ONE := (idM_eq CFSG.KD.OrdLy.consts).1

theorem vOne : vld CFSG.KD.OrdLy.ONE = true := (idM_eq CFSG.KD.OrdLy.consts).2

theorem matEqB_self (p d : Nat) (X : Array (Array Nat)) : matEqB p d X X = true := by
  unfold matEqB
  simp

theorem eq_of_matEqB {X Y : Nat} (hX : vld X = true) (hY : vld Y = true)
    (h : matEqB 5 111 (U X) (U Y) = true) : X = Y := by
  have cX := validM_canon CFSG.KD.OrdLy.consts (hv hX)
  have cY := validM_canon CFSG.KD.OrdLy.consts (hv hY)
  unfold matEqB at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine CFSG.KS.SporSch.LyM.canon_ext cX cY fun i hi j hj => ?_
  have e := h i hi j hj
  rw [unpackL_get hi hj, unpackL_get hi hj] at e
  have e1 : 1332 * i + 12 * j = 111 * 12 * i + 12 * j := by ring
  rw [e1, Nat.mod_eq_of_lt (canon_ent cX hi hj), Nat.mod_eq_of_lt (canon_ent cY hi hj)] at e
  exact e

theorem ek_succ (G T : Nat → Nat) (d i : Nat) :
    ek G T (d + 1) i = mul (G (PJ T i)) (ek G T d (PP T i)) := by
  change strictN (PP T i) (fun p => strictN (PJ T i) (fun j => mul (G j) (ek G T d p))) = _
  rw [strictN_eq, strictN_eq]

theorem E_succ {G T : Nat → Nat} {i : Nat} (hD : DT T i = DT T (PP T i) + 1) :
    E G T i = mul (G (PJ T i)) (E G T (PP T i)) := by
  unfold E
  rw [strictN_eq, strictN_eq, hD, ek_succ]

theorem E_zero {G T : Nat → Nat} (hD : DT T 0 = 0) : E G T 0 = CFSG.KD.OrdLy.ONE := by
  unfold E
  rw [strictN_eq, hD]
  rfl

structure Shape (T : Nat → Nat) : Prop where
  t0 : T 0 = 0
  d0 : DT T 0 = 0
  tree : ∀ i < 2187, i ≠ 0 → PP T i < i ∧ PJ T i < 5 ∧ DT T i = DT T (PP T i) + 1

theorem shapeK_spec {T : Nat → Nat} (h : shapeK T = true) : Shape T := by
  unfold shapeK at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, fun i hi hi0 => ?_⟩
  have e := allN_spec h3 i hi
  rw [strictB_eq, bIf_eq] at e
  have hb : Nat.beq i 0 = false := by
    cases i with
    | zero => exact absurd rfl hi0
    | succ n => rfl
  rw [hb] at e
  simp only [Bool.false_eq_true, ↓reduceIte] at e
  obtain ⟨e1, e⟩ := (bAnd_iff _ _).1 e
  obtain ⟨e2, e3⟩ := (bAnd_iff _ _).1 e
  exact ⟨blt_of e1, blt_of e2, Nat.eq_of_beq_eq_true e3⟩

theorem PP_zero {T : Nat → Nat} (h : T 0 = 0) : PP T 0 = 0 := by
  unfold PP
  rw [h]
  rfl

theorem vE {G T : Nat → Nat} (hs : Shape T) (hG : ∀ j < 5, vld (G j) = true) :
    ∀ i < 2187, vld (E G T i) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      rw [E_zero hs.d0]
      exact vOne
    · obtain ⟨hp, hj, hD⟩ := hs.tree i hi (by omega)
      rw [E_succ hD]
      exact mulV (hG _ hj) (ih _ hp (by omega))

theorem nth_eq : ∀ (l : List Nat) (k : Nat), nth l k = l.getD k 0
  | [], k => by cases k <;> rfl
  | x :: l, 0 => rfl
  | x :: l, k + 1 => by
    change nth l k = _
    rw [nth_eq l k]
    rfl

theorem regs_succ (A B : Nat) (T : Nat → Nat) (t : Nat) :
    regs A B T (t + 1) = regs A B T t ++
      [mul ((regs A B T t).getD (OP T t) 0) ((regs A B T t).getD (OQ T t) 0)] := by
  change regs A B T t ++ [mul (nth (regs A B T t) (OP T t)) (nth (regs A B T t) (OQ T t))] = _
  rw [nth_eq, nth_eq]

theorem regs_length (A B : Nat) (T : Nat → Nat) : ∀ t, (regs A B T t).length = t + 2
  | 0 => rfl
  | t + 1 => by rw [regs_succ, List.length_append, regs_length A B T t]; rfl

theorem regs_stable (A B : Nat) (T : Nat → Nat) {k t : Nat} (hk : k < t + 2) :
    ∀ m, (regs A B T (t + m)).getD k 0 = (regs A B T t).getD k 0
  | 0 => rfl
  | m + 1 => by
    rw [← Nat.add_assoc, regs_succ, List.getD_append _ _ _ _
      (by rw [regs_length]; omega), regs_stable A B T hk m]

theorem regs_last (A B : Nat) (T : Nat → Nat) (t : Nat) :
    (regs A B T (t + 1)).getD (t + 2) 0 =
      mul ((regs A B T t).getD (OP T t) 0) ((regs A B T t).getD (OQ T t) 0) := by
  rw [regs_succ, List.getD_append_right _ _ _ _ (by rw [regs_length]), regs_length, Nat.sub_self,
    List.getD_cons_zero]

@[expose] noncomputable def R (A B : Nat) (T : Nat → Nat) (k : Nat) : Nat :=
  (regs A B T 745).getD k 0

theorem R_of {A B : Nat} {T : Nat → Nat} {k t : Nat} (hk : k < t + 2) (ht : t ≤ 745) :
    R A B T k = (regs A B T t).getD k 0 := by
  unfold R
  have e : 745 = t + (745 - t) := by omega
  rw [e, regs_stable A B T hk]

theorem R_step {A B : Nat} {T : Nat → Nat} {t : Nat} (ht : t < 745)
    (hop : OP T t < t + 2) (hoq : OQ T t < t + 2) :
    R A B T (t + 2) = mul (R A B T (OP T t)) (R A B T (OQ T t)) := by
  rw [R_of (t := t + 1) (by omega) (by omega), regs_last, R_of hop (by omega),
    R_of hoq (by omega)]

theorem R_zero (A B : Nat) (T : Nat → Nat) : R A B T 0 = A := by
  rw [R_of (t := 0) (by omega) (by omega)]
  rfl

theorem R_one (A B : Nat) (T : Nat → Nat) : R A B T 1 = B := by
  rw [R_of (t := 0) (by omega) (by omega)]
  rfl

theorem opsK_spec {T : Nat → Nat} (h : opsK T = true) :
    ∀ t < 745, OP T t < t + 2 ∧ OQ T t < t + 2 := by
  intro t ht
  have e := allN_spec h t ht
  obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 e
  exact ⟨blt_of e1, blt_of e2⟩

theorem gensK_spec {A B : Nat} {T G : Nat → Nat} (h : gensK A B T G = true) :
    ∀ j < 5, R A B T (nth gensL j) = G j := by
  intro j hj
  unfold gensK at h
  rw [strictB_eq] at h
  have e := allBlk_spec h j hj
  rw [Nat.add_eq, Nat.zero_add, nth_eq (regs A B T 745)] at e
  exact Nat.eq_of_beq_eq_true e

theorem gens_eq (j : Nat) (hj : j < 5) : gens[j]! = nth gensL j := by
  rw [nth_eq]
  interval_cases j <;> rfl

theorem listT_spec {f : Nat → Nat} : ∀ {l : List Nat} {k n : Nat}, listT f l k n = true →
    l.length + k = n ∧ ∀ m < l.length, l[m]! = f (k + m)
  | [], k, n, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun m hm => absurd hm (by simp)⟩
  | x :: l, k, n, h => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨e1, e2⟩ := listT_spec h2
    refine ⟨by simp only [List.length_cons]; omega, fun m hm => ?_⟩
    cases m with
    | zero => simpa using Nat.eq_of_beq_eq_true h1
    | succ m =>
      rw [List.getElem!_cons_succ, e2 m (by simpa using hm)]
      congr 1
      omega

theorem parseNats_of {f : Nat → Nat} {cs : List Char} {n : Nat} (h : parseOK f cs n = true) :
    (parseNats (String.ofList cs)).size = n ∧
      ∀ m < n, (parseNats (String.ofList cs))[m]! = f m := by
  unfold parseOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨e1, e2⟩ := listT_spec h2
  have hp : parseNats (String.ofList cs) = (natsL cs).toArray := parse_ofList h1
  rw [hp]
  refine ⟨by simpa using e1, fun m hm => ?_⟩
  rw [List.getElem!_toArray, e2 m (by omega), Nat.zero_add]

theorem pairsOf_eq {a : Array Nat} {m : Nat} {f : Nat → Nat} (hs : a.size = 2 * m)
    (ha : ∀ k < 2 * m, a[k]! = f k) :
    pairsOf a = Array.ofFn (n := m) fun i => (f (2 * i.val), f (2 * i.val + 1)) := by
  unfold pairsOf
  have hm : a.size / 2 = m := by omega
  apply Array.ext
  · simp [hm]
  · intro i h1 h2
    simp only [Array.getElem_ofFn]
    rw [ha _ (by simp at h2; omega), ha _ (by simp at h2; omega)]

theorem opsRec_eq (T : Nat → Nat) (i : Nat) :
    opsRec T (2 * i) = OP T i ∧ opsRec T (2 * i + 1) = OQ T i := by
  constructor
  · unfold opsRec OP
    simp only [Nat.add_eq, Nat.mul_eq]
  · unfold opsRec OQ
    simp only [Nat.add_eq, Nat.mul_eq]
    congr 1
    omega

theorem parRec_eq (T : Nat → Nat) (i : Nat) :
    parRec T (2 * i) = PP T i ∧ parRec T (2 * i + 1) = PJ T i := by
  have m0 : Nat.mod (2 * i) 2 = 0 := Nat.mul_mod_right 2 i
  have m1 : Nat.mod (2 * i + 1) 2 = 1 := by
    change (2 * i + 1) % 2 = 1
    omega
  have d0 : Nat.div (2 * i) 2 = i := by
    change 2 * i / 2 = i
    omega
  have d1 : Nat.div (2 * i + 1) 2 = i := by
    change (2 * i + 1) / 2 = i
    omega
  unfold parRec
  rw [m0, m1, d0, d1]
  exact ⟨rfl, rfl⟩

theorem ops_of {T : Nat → Nat} {cs : List Char} (hc : opsStr = String.ofList cs)
    (h : parseOK (opsRec T) cs 1490 = true) :
    ops () = Array.ofFn (n := 745) fun t => (OP T t.val, OQ T t.val) := by
  obtain ⟨h1, h2⟩ := parseNats_of h
  have e : ops () = pairsOf (parseNats opsStr) := by unfold ops; exact rfl
  rw [e, hc, pairsOf_eq (m := 745) h1 h2]
  congr 1
  funext t
  rw [(opsRec_eq T t.val).1, (opsRec_eq T t.val).2]

theorem par_of {T : Nat → Nat} {cs : List Char} (hc : parStr = String.ofList cs)
    (h : parseOK (parRec T) cs 4374 = true) :
    par () = Array.ofFn (n := 2187) fun i => (PP T i.val, PJ T i.val) := by
  obtain ⟨h1, h2⟩ := parseNats_of h
  have e : par () = pairsOf (parseNats parStr) := by unfold par; exact rfl
  rw [e, hc, pairsOf_eq (m := 2187) h1 h2]
  congr 1
  funext i
  rw [(parRec_eq T i.val).1, (parRec_eq T i.val).2]

theorem L_of {T : Nat → Nat} {cs : List Char} (hc : LStr = String.ofList cs)
    (h : parseOK (LRec T) cs 10935 = true) :
    L () = Array.ofFn (n := 5) fun j => Array.ofFn (n := 2187) fun i => LT T j.val i.val := by
  obtain ⟨h1, h2⟩ := parseNats_of h
  have e : L () = Array.ofFn (n := 5) fun j => Array.ofFn (n := nS) fun i =>
      (parseNats LStr)[j.val * nS + i.val]! := by unfold L; exact rfl
  rw [e, hc]
  apply Array.ext
  · simp
  · intro j hj1 hj2
    simp only [Array.getElem_ofFn]
    apply Array.ext
    · simp [nS]
    · intro i hi1 hi2
      simp only [Array.getElem_ofFn]
      have hj : j < 5 := by simpa using hj1
      have hi : i < 2187 := by simpa [nS] using hi1
      rw [h2 _ (by unfold nS; omega)]
      unfold LRec CFSG.KD.LyS0.LT nS
      simp only [Nat.add_eq, Nat.mul_eq]
      congr 1
      ring

theorem regsM_eq {A B : Nat} {T : Nat → Nat}
    (hops : ops () = Array.ofFn (n := 745) fun t => (OP T t.val, OQ T t.val))
    (hoK : ∀ t < 745, OP T t < t + 2 ∧ OQ T t < t + 2)
    (hA : matA () = U A) (hB : matB () = U B) (vA : vld A = true) (vB : vld B = true) :
    ∀ k < 747, (regsM ())[k]! = U (R A B T k) ∧ vld (R A B T k) = true := by
  have hsz : (ops ()).size = 745 := by rw [hops, Array.size_ofFn]
  have h := buildN_inv (#[matA (), matB ()] : Array (Array (Array ℕ)))
    (fun acc k => mulM 5 111 (acc[((ops ())[k - 2]!).1]!) (acc[((ops ())[k - 2]!).2]!))
    (fun k x => x = U (R A B T k) ∧ vld (R A B T k) = true) (ops ()).size ?_ ?_
  · intro k hk
    have e : regsM () = buildN (#[matA (), matB ()] : Array (Array (Array ℕ)))
        (fun acc k => mulM 5 111 (acc[((ops ())[k - 2]!).1]!) (acc[((ops ())[k - 2]!).2]!))
        (ops ()).size := by unfold regsM; exact rfl
    rw [e]
    exact h.2 k (by rw [hsz]; simpa using hk)
  · intro k hk
    have hk2 : k < 2 := by simpa using hk
    interval_cases k
    · refine ⟨?_, by rw [R_zero]; exact vA⟩
      rw [R_zero]
      exact hA
    · refine ⟨?_, by rw [R_one]; exact vB⟩
      rw [R_one]
      exact hB
  · intro n hn r hr hP
    rw [hsz] at hn
    have hrs : r.size = n + 2 := by simpa [Nat.add_comm] using hr
    obtain ⟨hp, hq⟩ := hoK n hn
    have hon : (ops ())[r.size - 2]! = (OP T n, OQ T n) := by
      rw [hrs, Nat.add_sub_cancel, hops, ofFnG (fun t => (OP T t, OQ T t)) hn]
    simp only [hon]
    obtain ⟨e1, v1⟩ := hP (OP T n) (by omega)
    obtain ⟨e2, v2⟩ := hP (OQ T n) (by omega)
    rw [e1, e2, mulE v1 v2, hrs, R_step hn hp hq]
    exact ⟨rfl, mulV v1 v2⟩

theorem genM_eq {A B : Nat} {T G : Nat → Nat}
    (hops : ops () = Array.ofFn (n := 745) fun t => (OP T t.val, OQ T t.val))
    (hoK : ∀ t < 745, OP T t < t + 2 ∧ OQ T t < t + 2)
    (hA : matA () = U A) (hB : matB () = U B) (vA : vld A = true) (vB : vld B = true)
    (hg : gensK A B T G = true) : ∀ j < 5, genM j = U (G j) ∧ vld (G j) = true := by
  intro j hj
  have hr := regsM_eq hops hoK hA hB vA vB
  have e : genM j = (regsM ())[gens[j]!]! := by unfold genM; exact rfl
  have hgj : gens[j]! < 747 := by interval_cases j <;> decide
  rw [e]
  obtain ⟨e1, v1⟩ := hr _ hgj
  have e2 : R A B T (gens[j]!) = G j := by
    rw [gens_eq j hj]
    exact gensK_spec hg j hj
  rw [e2] at e1 v1
  exact ⟨e1, v1⟩

theorem eltsM_eq {G T : Nat → Nat}
    (hpar : par () = Array.ofFn (n := 2187) fun i => (PP T i.val, PJ T i.val))
    (hs : Shape T) (hgen : ∀ j < 5, genM j = U (G j)) (hG : ∀ j < 5, vld (G j) = true) :
    ∀ i < 2187, (eltsM ())[i]! = U (E G T i) := by
  have h := buildN_inv (#[idM 111] : Array (Array (Array ℕ)))
    (fun acc i => mulM 5 111 (genM ((par ())[i]!).2) (acc[((par ())[i]!).1]!))
    (fun k x => x = U (E G T k)) (nS - 1) ?_ ?_
  · intro i hi
    have e : eltsM () = buildN (#[idM 111] : Array (Array (Array ℕ)))
        (fun acc i => mulM 5 111 (genM ((par ())[i]!).2) (acc[((par ())[i]!).1]!)) (nS - 1) := by
      unfold eltsM
      exact rfl
    rw [e]
    exact h.2 i (by unfold nS; simpa using hi)
  · intro k hk
    have : k = 0 := by simpa using hk
    subst this
    change idM 111 = _
    rw [E_zero hs.d0, idE]
  · intro n hn r hr hP
    have hrs : r.size = n + 1 := by simpa [Nat.add_comm] using hr
    have hlt : r.size < 2187 := by unfold nS at hn; omega
    obtain ⟨hp, hj, hD⟩ := hs.tree r.size hlt (by omega)
    have hpn : (par ())[r.size]! = (PP T r.size, PJ T r.size) := by
      rw [hpar, ofFnG (fun i => (PP T i, PJ T i)) hlt]
    simp only [hpn]
    rw [hgen _ hj, hP _ hp, mulE (hG _ hj) (vE hs hG _ (by omega)), E_succ hD]

theorem leftK_spec {G T : Nat → Nat} {b len : Nat} (h : leftK G T b len = true) :
    ∀ l < len, ∀ j < 5, LT T j (b + l) < 2187 ∧
      mul (G j) (E G T (b + l)) = E G T (LT T j (b + l)) := by
  intro l hl j hj
  have e := allBlk_spec h l hl
  rw [strictB_eq] at e
  have e2 := allBlk_spec e j hj
  rw [strictB_eq, strictB_eq, Nat.add_eq, Nat.zero_add] at e2
  obtain ⟨e3, e4⟩ := (bAnd_iff _ _).1 e2
  exact ⟨blt_of e3, Nat.eq_of_beq_eq_true e4⟩

theorem slices {P : Nat → Prop} (h : ∀ q < 27, ∀ l < 81, P (81 * q + l)) : ∀ i < 2187, P i := by
  intro i hi
  have e : i = 81 * (i / 81) + i % 81 := (Nat.div_add_mod i 81).symm
  rw [e]
  exact h _ (by omega) _ (Nat.mod_lt _ (by norm_num))

theorem leftOK_of {G T : Nat → Nat}
    (hL : L () = Array.ofFn (n := 5) fun j => Array.ofFn (n := 2187) fun i => LT T j.val i.val)
    (helts : ∀ i < 2187, (eltsM ())[i]! = U (E G T i))
    (hgen : ∀ j < 5, genM j = U (G j)) (hG : ∀ j < 5, vld (G j) = true) (hs : Shape T)
    (hl : ∀ q < 27, leftK G T (81 * q) 81 = true) : leftOK () = true := by
  have hall : ∀ i < 2187, ∀ j < 5, LT T j i < 2187 ∧ mul (G j) (E G T i) = E G T (LT T j i) :=
    slices fun q hq l hl' => leftK_spec (hl q hq) l hl'
  unfold leftOK
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  intro j hj i hi
  unfold nS at hi
  have hLji : ((L ())[j]!)[i]! = LT T j i := by
    rw [hL, ofFnG (fun j => Array.ofFn (n := 2187) fun i => LT T j i.val) hj,
      ofFnG (fun i => LT T j i) hi]
  obtain ⟨h1, h2⟩ := hall i hi j hj
  rw [hLji]
  refine ⟨h1, ?_⟩
  rw [hgen j hj, helts i hi, helts _ h1, mulE (hG j hj) (vE hs hG i hi), h2]
  exact matEqB_self _ _ _

theorem sortK_spec {G T : Nat → Nat} {b len : Nat} (h : sortK G T b len = true) :
    ∀ l < len, sortB (E G T) (SO T) (SOI T) 2187 (b + l) = true := by
  intro l hl
  have e := allBlk_spec h l hl
  rw [strictB_eq] at e
  exact e

theorem distinctOK_of {G T : Nat → Nat}
    (helts : ∀ i < 2187, (eltsM ())[i]! = U (E G T i))
    (hG : ∀ j < 5, vld (G j) = true) (hs : Shape T)
    (hsort : ∀ q < 27, sortK G T (81 * q) 81 = true) : distinctOK () = true := by
  have hall : ∀ i < 2187, sortB (E G T) (SO T) (SOI T) 2187 i = true :=
    slices fun q hq l hl => sortK_spec (hsort q hq) l hl
  have hinj := CFSG.KS.SporSch.LyLoop.sortB_inj hall
  unfold distinctOK
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true']
  intro i hi k hk
  unfold nS at hi
  rw [helts i hi, helts k (by omega)]
  rcases Bool.eq_false_or_eq_true (matEqB 5 111 (U (E G T i)) (U (E G T k))) with e | e
  · exfalso
    have := hinj i hi k (by omega) (eq_of_matEqB (vE hs hG i hi) (vE hs hG k (by omega)) e)
    omega
  · exact e

theorem tmF_succ (T : Nat → Nat) (f a b : Nat) :
    tmF T (f + 1) a b = nIf(Nat.blt (PP T a) a, LT T (PJ T a) (tmF T f (PP T a) b), b) := rfl

theorem tabMul_eq {T : Nat → Nat}
    (hpar : par () = Array.ofFn (n := 2187) fun i => (PP T i.val, PJ T i.val))
    (hL : L () = Array.ofFn (n := 5) fun j => Array.ofFn (n := 2187) fun i => LT T j.val i.val)
    (hs : Shape T) (hLt : ∀ j < 5, ∀ i < 2187, LT T j i < 2187) {b : Nat} (hb : b < 2187) :
    ∀ f a, a < 2187 → a < f → tabMul (par ()) (L ()) a b = tmF T f a b ∧ tmF T f a b < 2187
  | 0, a, _, h => absurd h (Nat.not_lt_zero a)
  | f + 1, a, ha, hf => by
    have hpa : (par ())[a]! = (PP T a, PJ T a) := by
      rw [hpar, ofFnG (fun i => (PP T i, PJ T i)) ha]
    rw [tabMul, tmF_succ, nIf_eq, hpa]
    by_cases hlt : PP T a < a
    · have hb' : Nat.blt (PP T a) a = true := blt_iff hlt
      rw [dif_pos hlt, hb']
      simp only [↓reduceIte]
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact absurd hlt (by omega)
      obtain ⟨-, hj, -⟩ := hs.tree a ha ha0
      obtain ⟨e1, e2⟩ := tabMul_eq hpar hL hs hLt hb f (PP T a) (by omega) (by omega)
      rw [e1, hL, ofFnG (fun j => Array.ofFn (n := 2187) fun i => LT T j i.val) hj,
        ofFnG (fun i => LT T (PJ T a) i) e2]
      exact ⟨rfl, hLt _ hj _ e2⟩
    · have hb' : Nat.blt (PP T a) a = false := by
        rw [Bool.eq_false_iff]
        intro e
        exact hlt (blt_of e)
      rw [dif_neg hlt, hb']
      exact ⟨rfl, hb⟩

theorem tm_eq {T : Nat → Nat}
    (hpar : par () = Array.ofFn (n := 2187) fun i => (PP T i.val, PJ T i.val))
    (hL : L () = Array.ofFn (n := 5) fun j => Array.ofFn (n := 2187) fun i => LT T j.val i.val)
    (hs : Shape T) (hLt : ∀ j < 5, ∀ i < 2187, LT T j i < 2187) {a b : Nat} (ha : a < 2187)
    (hb : b < 2187) : tabMul (par ()) (L ()) a b = tm T a b ∧ tm T a b < 2187 :=
  tabMul_eq hpar hL hs hLt hb (a + 1) a ha (by omega)

theorem le_countP {W : Nat → Nat} {p : Nat → Bool} {n m : Nat} (hlt : ∀ k < m, W k < n)
    (hinc : ∀ k, k + 1 < m → W k < W (k + 1)) (hp : ∀ k < m, p (W k) = true) :
    m ≤ (List.range n).countP p := by
  have mono : ∀ k k', k < k' → k' < m → W k < W k' := by
    intro k k' hkk hk'
    induction k' with
    | zero => omega
    | succ k' ih =>
      rcases Nat.lt_or_ge k k' with h | h
      · exact Nat.lt_trans (ih h (by omega)) (hinc k' hk')
      · have : k = k' := by omega
        subst this
        exact hinc k hk'
  have hnd : ((List.range m).map W).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy e => ?_) List.nodup_range
    rw [List.mem_range] at hx hy
    rcases Nat.lt_trichotomy x y with h | h | h
    · exact absurd e (Nat.ne_of_lt (mono x y h hy))
    · exact h
    · exact absurd e.symm (Nat.ne_of_lt (mono y x h hx))
  have hsub : (List.range m).map W ⊆ (List.range n).filter p := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hk
    exact List.mem_filter.2 ⟨List.mem_range.2 (hlt k hk), hp k hk⟩
  have := (hnd.subperm hsub).length_le
  rw [List.length_map, List.length_range] at this
  rw [List.countP_eq_length_filter]
  exact this

theorem witK_spec {T : Nat → Nat} {a : Nat} (h : witK T a = true) :
    ∀ k < 81, WT T a k < 2187 ∧ (k ≠ 0 → WT T a (k - 1) < WT T a k) ∧
      tm T a (WT T a k) = tm T (WT T a k) a := by
  intro k hk
  have e := allBlk_spec h k hk
  rw [Nat.add_eq, Nat.zero_add, strictB_eq, strictB_eq] at e
  obtain ⟨e1, e⟩ := (bAnd_iff _ _).1 e
  obtain ⟨e2, e3⟩ := (bAnd_iff _ _).1 e
  refine ⟨blt_of e1, fun hk0 => ?_, Nat.eq_of_beq_eq_true e3⟩
  rw [bIf_eq] at e2
  have hb : Nat.beq k 0 = false := by
    cases k with
    | zero => exact absurd rfl hk0
    | succ n => rfl
  rw [hb] at e2
  simp only [Bool.false_eq_true, ↓reduceIte] at e2
  have e4 : Nat.sub k 1 = k - 1 := rfl
  rw [e4] at e2
  exact blt_of e2

theorem killOK_of {T : Nat → Nat}
    (hpar : par () = Array.ofFn (n := 2187) fun i => (PP T i.val, PJ T i.val))
    (hL : L () = Array.ofFn (n := 5) fun j => Array.ofFn (n := 2187) fun i => LT T j.val i.val)
    (hs : Shape T) (hLt : ∀ j < 5, ∀ i < 2187, LT T j i < 2187) (hk : killK T = true) :
    killOK () = true := by
  unfold killOK
  simp only [List.all_eq_true, List.mem_range]
  intro a ha
  unfold nS at ha
  have e := allN_spec hk a ha
  rw [strictB_eq, bIf_eq] at e
  by_cases ha0 : a = 0
  · subst ha0
    rfl
  have hb : Nat.beq a 0 = false := by
    cases a with
    | zero => exact absurd rfl ha0
    | succ n => rfl
  rw [hb] at e
  simp only [Bool.false_eq_true, ↓reduceIte] at e
  rw [strictB_eq, bIf_eq] at e
  obtain ⟨m1, l1⟩ := tm_eq hpar hL hs hLt ha ha
  obtain ⟨m2, -⟩ := tm_eq hpar hL hs hLt ha l1
  have hcube : tabMul (par ()) (L ()) a (tabMul (par ()) (L ()) a a) = tm T a (tm T a a) := by
    rw [m1, m2]
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq]
  by_cases hc : tm T a (tm T a a) = 0
  · right
    have hb0 : Nat.beq (tm T a (tm T a a)) 0 = true := by rw [hc]; rfl
    rw [hb0] at e
    simp only [↓reduceIte] at e
    have hw := witK_spec e
    unfold tabComm
    have hcongr : (List.range 2187).countP (fun b => tabMul (par ()) (L ()) a b ==
        tabMul (par ()) (L ()) b a) =
        (List.range 2187).countP (fun b => tm T a b == tm T b a) := by
      refine List.countP_congr fun b hb' => ?_
      rw [List.mem_range] at hb'
      rw [(tm_eq hpar hL hs hLt ha hb').1, (tm_eq hpar hL hs hLt hb' ha).1]
    unfold nS
    rw [hcongr]
    refine le_countP (W := WT T a) (fun k hk' => (hw k hk').1)
      (fun k hk' => by
        have := (hw (k + 1) hk').2.1 (by omega)
        simpa using this)
      (fun k hk' => by simpa using (hw k hk').2.2)
  · left
    right
    rw [hcube]
    exact hc

theorem shapeOK_of {T : Nat → Nat}
    (hops : ops () = Array.ofFn (n := 745) fun t => (OP T t.val, OQ T t.val))
    (hoK : ∀ t < 745, OP T t < t + 2 ∧ OQ T t < t + 2)
    (hpar : par () = Array.ofFn (n := 2187) fun i => (PP T i.val, PJ T i.val))
    (hL : L () = Array.ofFn (n := 5) fun j => Array.ofFn (n := 2187) fun i => LT T j.val i.val)
    (hs : Shape T) : shapeOK () = true := by
  unfold shapeOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true]
  have hsz : (ops ()).size = 745 := by rw [hops, Array.size_ofFn]
  refine ⟨⟨⟨⟨⟨⟨hsz, rfl⟩, by rw [hpar, Array.size_ofFn]; rfl⟩, by rw [hL, Array.size_ofFn]⟩,
    fun t ht => ?_⟩, fun j hj => ?_⟩, fun i hi => ?_⟩
  · rw [hsz] at ht
    rw [hops, ofFnG (fun t => (OP T t, OQ T t)) ht]
    exact hoK t ht
  · have hj5 : j < 5 := hj
    rw [hsz]
    interval_cases j <;> decide
  · unfold nS at hi
    by_cases hi0 : i = 0
    · left
      rw [hi0]
    · right
      rw [hpar, ofFnG (fun i => (PP T i, PJ T i)) hi]
      obtain ⟨h1, h2, -⟩ := hs.tree i hi hi0
      exact ⟨h1, h2⟩

theorem lyS0Check_of {A B : Nat} {T G : Nat → Nat} {co cp cl : List Char}
    (hco : opsStr = String.ofList co) (hcp : parStr = String.ofList cp)
    (hcl : LStr = String.ofList cl) (po : parseOK (opsRec T) co 1490 = true)
    (pp : parseOK (parRec T) cp 4374 = true) (pl : parseOK (LRec T) cl 10935 = true)
    (hs : shapeK T = true) (ho : opsK T = true) (hA : matA () = U A) (hB : matB () = U B)
    (vA : vld A = true) (vB : vld B = true) (hg : gensK A B T G = true)
    (hl : ∀ q < 27, leftK G T (81 * q) 81 = true) (hso : ∀ q < 27, sortK G T (81 * q) 81 = true)
    (hk : killK T = true) : lyS0Check () = true := by
  have hops := ops_of hco po
  have hpar := par_of hcp pp
  have hL := L_of hcl pl
  have hsh := shapeK_spec hs
  have hoK := opsK_spec ho
  have hgen := genM_eq hops hoK hA hB vA vB hg
  have hG : ∀ j < 5, vld (G j) = true := fun j hj => (hgen j hj).2
  have hgen' : ∀ j < 5, genM j = U (G j) := fun j hj => (hgen j hj).1
  have helts := eltsM_eq hpar hsh hgen' hG
  have hLt : ∀ j < 5, ∀ i < 2187, CFSG.KD.LyS0.LT T j i < 2187 := fun j hj i hi =>
    slices (P := fun i => ∀ j < 5, CFSG.KD.LyS0.LT T j i < 2187)
      (fun q hq l hl' j hj => (leftK_spec (hl q hq) l hl' j hj).1) i hi j hj
  unfold lyS0Check
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨shapeOK_of hops hoK hpar hL hsh, killOK_of hpar hL hsh hLt hk⟩,
    leftOK_of hL helts hgen' hG hsh hl⟩, distinctOK_of helts hG hsh hso⟩

end CFSG.KS.LyS0K

end
