module

public import Certificates.Data.Kernel.U6.Core
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.EvenSmallLie.UnitarySix CFSG.Sporadic.Th.Native CFSG.F4.Native

@[expose] noncomputable def decA (P w n : Nat) : Array Nat := Array.ofFn (n := n) fun i => fget P i.val w

@[expose] def tvTableG (pts pos : Array Nat) (v : Nat) : Table :=
  Array.ofFn (n := 693) fun k => UInt32.ofNat (pos[normC (tvC v pts[k.val]!)]!)

@[expose] def LetsBind (L : List (Equiv.Perm (Fin 693))) (LT : Nat) : Prop :=
  L.length = 46 ∧ ∀ k < 46, ∀ p : Fin 693, ((L.getD k 1) p : ℕ) = ap10 (letK LT k) p.val

@[expose] def uPtsG (iso norm : Nat → Nat) : Array Nat :=
  ((List.range 4096).filter fun c => c != 0 && iso c == 0 && norm c == c).toArray

@[expose] def uPosG (pts : Array Nat) : Array Nat :=
  Array.ofFn (n := 4096) fun c => pts.toList.idxOf c.val

@[expose] def tvGensG (wt : Nat → Bool) (pts : Array Nat) : Array Nat :=
  (pts.filter wt).push (1 + 4 + 16 + 64)

namespace Snd

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.F4M

theorem andB_iff {a b : Bool} : CFSG.KLie.CT.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [CFSG.KLie.CT.andB]

theorem notB_iff {a : Bool} : CFSG.KLie.CT.notB a = true ↔ a = false := by
  cases a <;> simp [CFSG.KLie.CT.notB]

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem recAnd_iff (g : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun l ih => CFSG.KLie.CT.andB (g l) ih) n = true ↔
      ∀ l < n, g l = true
  | 0 => ⟨fun _ l hl => absurd hl (Nat.not_lt_zero l), fun _ => rfl⟩
  | n + 1 => by
    change CFSG.KLie.CT.andB (g n) (Nat.rec (motive := fun _ => Bool) true (fun l ih => CFSG.KLie.CT.andB (g l) ih) n) =
      true ↔ _
    rw [andB_iff, recAnd_iff g n]
    constructor
    · rintro ⟨h1, h2⟩ l hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
      · exact h2 l h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun l hl => h l (Nat.lt_succ_of_lt hl)⟩

theorem allN_iff {n : ℕ} {f : ℕ → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  recAnd_iff f n

theorem allBelow_spec {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true)
    (hm : m ≤ 64 * hi) : ∀ i < m, f i = true := by
  intro i him
  have h1 := (recAnd_iff (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      CFSG.KLie.CT.andB ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
        (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64) hi).1 h (i / 64) (by omega)
  have h2 := (recAnd_iff (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
      (Nat.blt i m)) (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64).1 h1 (i % 64)
    (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
    omega
  dsimp only at h2
  rw [e, blt_iff.2 him] at h2
  exact h2

theorem fget_eq (X i w : ℕ) : fget X i w = X >>> (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& (1 <<< w - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

theorem fget_lt (X i w : ℕ) : fget X i w < 2 ^ w := by
  rw [fget_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem getElem_of_ofFn {n : ℕ} {f : Fin n → ℕ} {L : List ℕ} (hL : L = List.ofFn f) (i : ℕ)
    (h : i < L.length) (hn : i < n) : L[i] = f ⟨i, hn⟩ := by
  subst hL
  simp

theorem decA_get (P w n i : ℕ) (hi : i < n) : (decA P w n)[i]! = fget P i w := by
  rw [decA, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem allIn_iff {n : ℕ} {p : ℕ → Bool} : allIn 0 n p = true ↔ ∀ i < n, p i = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    have := h ⟨i, by omega⟩ (List.mem_finRange _)
    simpa using this
  · intro h k _
    simpa using h k.val (by have := k.isLt; omega)

theorem coord_lt (c i : ℕ) : coord c i < 4 := Nat.mod_lt _ (by norm_num)

theorem f4mul_lt (x y : ℕ) : f4mul x y < 4 := by
  show (x % 2 * (y % 2) + x / 2 * (y / 2)) % 2 +
    2 * ((x % 2 * (y / 2) + x / 2 * (y % 2) + x / 2 * (y / 2)) % 2) < 4
  have h1 : (x % 2 * (y % 2) + x / 2 * (y / 2)) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h2 : (x % 2 * (y / 2) + x / 2 * (y % 2) + x / 2 * (y / 2)) % 2 < 2 :=
    Nat.mod_lt _ (by norm_num)
  generalize (x % 2 * (y % 2) + x / 2 * (y / 2)) % 2 = a at h1 ⊢
  generalize (x % 2 * (y / 2) + x / 2 * (y % 2) + x / 2 * (y / 2)) % 2 = b at h2 ⊢
  omega

theorem crd_eq (c i : ℕ) : crd c i = coord c i := by
  show fget c i 2 = c / 4 ^ i % 4
  rw [fget_eq, Nat.shiftRight_eq_div_pow, Nat.mul_comm, Nat.pow_mul]
  rfl

theorem fm_lt (a b : ℕ) : fm a b < 4 := fget_lt _ _ 2

theorem fm_eq' : ∀ a < 4, ∀ b < 4, fm a b = f4mul a b := by decide

theorem fm_eq {a b : ℕ} (ha : a < 4) (hb : b < 4) : fm a b = f4mul a b := fm_eq' a ha b hb

theorem foldl_xor_succ (F : ℕ → ℕ) (n : ℕ) :
    (List.range (n + 1)).foldl (fun acc i => acc ^^^ F i) 0 =
      (List.range n).foldl (fun acc i => acc ^^^ F i) 0 ^^^ F n := by
  rw [List.range_succ, List.foldl_append]
  rfl

theorem foldl_add_succ (F : ℕ → ℕ) (n : ℕ) :
    (List.range (n + 1)).foldl (fun acc i => acc + F i) 0 =
      (List.range n).foldl (fun acc i => acc + F i) 0 + F n := by
  rw [List.range_succ, List.foldl_append]
  rfl

theorem xorN_eq (f : ℕ → ℕ) : ∀ n, xorN n f = (List.range n).foldl (fun acc i => acc ^^^ f i) 0
  | 0 => rfl
  | n + 1 => by
    rw [foldl_xor_succ, ← xorN_eq f n, Nat.xor_comm]
    rfl

theorem xorN_lt (f : ℕ → ℕ) (hf : ∀ i, f i < 4) : ∀ n, xorN n f < 4
  | 0 => by
    show 0 < 4
    norm_num
  | n + 1 => by
    show f n ^^^ xorN n f < 2 ^ 2
    exact Nat.xor_lt_two_pow (hf n) (xorN_lt f hf n)

theorem orN_sum (f : ℕ → ℕ) (hf : ∀ i, f i < 4) : ∀ n,
    orN n (fun i => Nat.shiftLeft (f i) (Nat.mul 2 i)) =
        (List.range n).foldl (fun acc i => acc + f i * 4 ^ i) 0 ∧
      (List.range n).foldl (fun acc i => acc + f i * 4 ^ i) 0 < 4 ^ n
  | 0 => ⟨rfl, by simp⟩
  | n + 1 => by
    obtain ⟨e, b⟩ := orN_sum f hf n
    rw [foldl_add_succ]
    have e4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
      rw [Nat.pow_mul]
    refine ⟨?_, ?_⟩
    · show Nat.lor (Nat.shiftLeft (f n) (Nat.mul 2 n))
        (orN n (fun i => Nat.shiftLeft (f i) (Nat.mul 2 i))) = _
      rw [e]
      change f n <<< (2 * n) ||| _ = _
      rw [← Nat.shiftLeft_add_eq_or_of_lt (by rw [← e4]; exact b), Nat.shiftLeft_eq, ← e4]
      exact Nat.add_comm _ _
    · have h3 : f n * 4 ^ n ≤ 3 * 4 ^ n := Nat.mul_le_mul_right _ (by have := hf n; omega)
      rw [Nat.pow_succ]
      omega

theorem hermK_lt (c d : ℕ) : hermK c d < 4 := xorN_lt _ (fun _ => fm_lt _ _) 6

theorem hermK_eq (c d : ℕ) : hermK c d = hermC c d := by
  have e : ∀ i, fm (crd c i) (sqC (crd d i)) =
      f4mul (coord c i) (f4mul (coord d i) (coord d i)) := by
    intro i
    rw [sqC, crd_eq, crd_eq, fm_eq (coord_lt d i) (coord_lt d i),
      fm_eq (coord_lt c i) (f4mul_lt _ _)]
  rw [show hermK c d = xorN 6 (fun i => fm (crd c i) (sqC (crd d i))) from rfl, xorN_eq]
  simp only [e]
  rfl

theorem scaleK_eq (a c : ℕ) (ha : a < 4) : scaleK a c = scaleC a c ∧ scaleC a c < 4096 := by
  have h := orN_sum (fun i => fm a (crd c i)) (fun _ => fm_lt _ _) 6
  have e : ∀ i, fm a (crd c i) * 4 ^ i = f4mul a (coord c i) * 4 ^ i := fun i => by
    rw [crd_eq, fm_eq ha (coord_lt c i)]
  simp only [e] at h
  exact ⟨h.1, h.2⟩

theorem leadK_lt (c : ℕ) : leadK c < 4 := by
  have : ∀ n, Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => (fun i =>
      Bool.rec (motive := fun _ => ℕ) (crd c i) acc (Nat.beq (crd c i) 0)) (Nat.sub 5 j)) n < 4 := by
    intro n
    induction n with
    | zero =>
      show 0 < 4
      norm_num
    | succ n ih =>
      show Bool.rec (motive := fun _ => ℕ) (crd c (Nat.sub 5 n)) _
        (Nat.beq (crd c (Nat.sub 5 n)) 0) < 4
      cases Nat.beq (crd c (Nat.sub 5 n)) 0
      · exact fget_lt _ _ 2
      · exact ih
  exact this 6

theorem leadK_eq (c : ℕ) : leadK c = leadC c := by
  have sel : ∀ x acc : ℕ, Bool.rec (motive := fun _ => ℕ) x acc (Nat.beq x 0) =
      if x = 0 then acc else x := by
    intro x acc
    rcases x with _ | n
    · simp
    · have hb : Nat.beq (n + 1) 0 = false := rfl
      simp [hb]
  have sel2 : ∀ x acc : ℕ, (if (x != 0) = true then x else acc) = if x = 0 then acc else x := by
    intro x acc
    by_cases h : x = 0 <;> simp [h]
  show Bool.rec (motive := fun _ => ℕ) (crd c 0) (Bool.rec (motive := fun _ => ℕ) (crd c 1)
      (Bool.rec (motive := fun _ => ℕ) (crd c 2) (Bool.rec (motive := fun _ => ℕ) (crd c 3)
        (Bool.rec (motive := fun _ => ℕ) (crd c 4) (Bool.rec (motive := fun _ => ℕ) (crd c 5) 0
          (Nat.beq (crd c 5) 0)) (Nat.beq (crd c 4) 0)) (Nat.beq (crd c 3) 0))
        (Nat.beq (crd c 2) 0)) (Nat.beq (crd c 1) 0)) (Nat.beq (crd c 0) 0) =
    (if (coord c 0 != 0) = true then coord c 0 else if (coord c 1 != 0) = true then coord c 1
      else if (coord c 2 != 0) = true then coord c 2 else if (coord c 3 != 0) = true then coord c 3
      else if (coord c 4 != 0) = true then coord c 4 else if (coord c 5 != 0) = true then coord c 5
      else 0)
  simp only [sel, sel2, crd_eq]

theorem normK_eq (y : ℕ) : normK y = normC y ∧ normC y < 4096 := by
  have hl := leadK_lt y
  obtain ⟨e, b⟩ := scaleK_eq (sqC (leadK y)) y (fm_lt _ _)
  have e2 : sqC (leadK y) = f4mul (leadC y) (leadC y) := by
    rw [sqC, fm_eq hl hl, leadK_eq]
  have e3 : normK y = scaleK (sqC (leadK y)) y := strictN_eq _ _
  have e4 : normC y = scaleC (sqC (leadK y)) y := by
    rw [e2]
    rfl
  rw [e3, e, e4]
  exact ⟨rfl, b⟩

theorem tvK_eq (v x : ℕ) : tvK v x = tvC v x := by
  show Nat.xor x (scaleK (hermK x v) v) = x ^^^ scaleC (hermC x v) v
  rw [(scaleK_eq _ v (hermK_lt x v)).1, hermK_eq]
  rfl

theorem isPt_iff {iso norm : ℕ → ℕ} {c : ℕ} :
    isPt iso norm c = true ↔ c ≠ 0 ∧ iso c = 0 ∧ norm c = c := by
  unfold isPt
  rw [andB_iff, andB_iff, notB_iff, Bool.eq_false_iff, Ne, beq_iff, beq_iff, beq_iff]

end Snd

open Snd in
theorem pts_sound {iso norm : Nat → Nat} {UP POS : Nat} (h : ptsOK iso norm UP POS = true) :
    decA UP 12 693 = uPtsG iso norm ∧ decA POS 10 4096 = uPosG (decA UP 12 693) := by
  unfold ptsOK at h
  rw [andB_iff, andB_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  have H1 := allBelow_spec h1 (by norm_num)
  have H2 := allBelow_spec h2 (by norm_num)
  have H3 := allBelow_spec h3 (by norm_num)
  have hpt : ∀ i < 693, isPt iso norm (up UP i) = true ∧ pos POS (up UP i) = i := fun i hi => by
    have := H2 i hi
    rw [andB_iff, beq_iff] at this
    exact this
  have hup_lt : ∀ i, up UP i < 4096 := fun i => fget_lt UP i 12
  obtain ⟨L, hLd⟩ : ∃ L, L = List.ofFn (fun i : Fin 693 => up UP i.val) := ⟨_, rfl⟩
  have hLlen : L.length = 693 := by rw [hLd, List.length_ofFn]
  have hsorted : StrictMono (fun i : Fin 693 => up UP i.val) :=
    Fin.strictMono_iff_lt_succ.2 fun i => blt_iff.1 (H1 i.val i.isLt)
  have hpw : L.Pairwise (· < ·) := by
    rw [hLd]
    exact List.sortedLT_iff_pairwise.1 (List.sortedLT_ofFn_iff.2 hsorted)
  have hnd : L.Nodup := hpw.nodup
  have hmemL : ∀ a, a ∈ L ↔ ∃ i < 693, up UP i = a := by
    intro a
    rw [hLd, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hgood : ∀ a < 4096, isPt iso norm a = true → pos POS a < 693 ∧ up UP (pos POS a) = a := by
    intro a ha hP
    have := H3 a ha
    dsimp only at this
    rw [hP, andB_iff, beq_iff] at this
    exact ⟨blt_iff.1 this.1, this.2⟩
  have hbad : ∀ a < 4096, isPt iso norm a = false → pos POS a = 693 := by
    intro a ha hP
    have := H3 a ha
    dsimp only at this
    rw [hP, beq_iff] at this
    exact this
  have hL : (decA UP 12 693).toList = L := by
    rw [hLd, decA, Array.toList_ofFn]
    rfl
  have e1 : decA UP 12 693 = uPtsG iso norm := by
    apply Array.toList_inj.1
    rw [hL, uPtsG, List.toList_toArray]
    apply List.Pairwise.eq_of_mem_iff hpw (List.pairwise_lt_range.filter _)
    intro a
    rw [hmemL, List.mem_filter, List.mem_range]
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, ne_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨hp, -⟩ := hpt i hi
      rw [isPt_iff] at hp
      exact ⟨hup_lt i, ⟨hp.1, hp.2.1⟩, hp.2.2⟩
    · rintro ⟨ha, ⟨h0, hi⟩, hn⟩
      obtain ⟨hj, hu⟩ := hgood a ha (isPt_iff.2 ⟨h0, hi, hn⟩)
      exact ⟨pos POS a, hj, hu⟩
  refine ⟨e1, ?_⟩
  have key : ∀ c < 4096, pos POS c = L.idxOf c := by
    intro c hc
    by_cases hP : isPt iso norm c = true
    · obtain ⟨hj, hu⟩ := hgood c hc hP
      have hjL : pos POS c < L.length := by
        rw [hLlen]
        exact hj
      have hget : L[pos POS c]'hjL = c := (getElem_of_ofFn hLd _ hjL hj).trans hu
      conv_lhs => rw [← hnd.idxOf_getElem _ hjL]
      rw [hget]
    · have hnot : c ∉ L := by
        rw [hmemL]
        rintro ⟨i, hi, hiu⟩
        exact hP (hiu ▸ (hpt i hi).1)
      rw [hbad c hc (Bool.eq_false_iff.2 hP), List.idxOf_eq_length hnot, hLlen]
  rw [uPosG, hL]
  show Array.ofFn (n := 4096) (fun i => fget POS i.val 10) = _
  exact congrArg (Array.ofFn (n := 4096)) (funext fun c => key c.val c.isLt)

open Snd in
theorem tv_sound {wt : Nat → Bool} {UP TV : Nat} (h : tvOK wt UP TV = true) :
    decA TV 12 46 = tvGensG wt (decA UP 12 693) := by
  unfold tvOK at h
  rw [andB_iff, beq_iff, beq_iff] at h
  obtain ⟨h45, hR⟩ := h
  let F : ℕ → ℕ → ℕ := fun i j => Bool.rec (motive := fun _ => ℕ) j
    (Bool.rec (motive := fun _ => ℕ) 100000 (Nat.succ j) (Nat.beq (fget TV j 12) (up UP i)))
    (wt (up UP i))
  let R : ℕ → ℕ := fun n => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i j => CFSG.KC.Loop.strictN j fun j => (fun c => Bool.rec (motive := fun _ => Nat) j
      (Bool.rec (motive := fun _ => Nat) (nat_lit 100000) (Nat.succ j)
        (Nat.beq (fget TV j (nat_lit 12)) c)) (wt c)) (up UP i)) n
  have hRs : ∀ n, R (n + 1) = F n (R n) := fun n => strictN_eq _ _
  have hR693 : R 693 = 45 := hR
  let filt : ℕ → List ℕ := fun n => ((List.range n).map (up UP)).filter wt
  have hbig : ∀ n, 100000 ≤ R n → 100000 ≤ R (n + 1) := by
    intro n hn
    rw [hRs]
    simp only [F]
    cases wt (up UP n)
    · exact hn
    · cases Nat.beq (fget TV (R n) 12) (up UP n)
      · exact le_refl _
      · exact Nat.le_succ_of_le hn
  have hbig' : ∀ n m, 100000 ≤ R n → 100000 ≤ R (n + m) := by
    intro n m hn
    induction m with
    | zero => exact hn
    | succ m ih => exact hbig _ ih
  have inv : ∀ n, R n < 100000 →
      R n = (filt n).length ∧ ∀ j < R n, fget TV j 12 = (filt n)[j]! := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    | succ n ih =>
      intro hn
      have hn' : R n < 100000 := by
        by_contra hc
        exact absurd (hbig n (Nat.le_of_not_lt hc)) (Nat.not_le_of_lt hn)
      obtain ⟨hl, ht⟩ := ih hn'
      have hf : filt (n + 1) = filt n ++ (if wt (up UP n) then [up UP n] else []) := by
        simp only [filt, List.range_succ, List.map_append, List.filter_append, List.map_cons,
          List.map_nil, List.filter_cons, List.filter_nil]
      rw [hRs] at hn ⊢
      simp only [F] at hn ⊢
      cases hw : wt (up UP n)
      · simp only [hf, hw, Bool.false_eq_true, ite_false, List.append_nil]
        exact ⟨hl, ht⟩
      · simp only [hw] at hn
        cases hb : Nat.beq (fget TV (R n) 12) (up UP n)
        · rw [hb] at hn
          exact absurd hn (lt_irrefl _)
        · rw [beq_iff] at hb
          simp only [hf, hw, ite_true]
          refine ⟨by rw [List.length_append, ← hl]; rfl, fun j hj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
          · rw [ht j hj, getElem!_pos _ j (by omega), getElem!_pos _ j (by simp; omega),
              List.getElem_append_left]
          · subst hj
            rw [hb, getElem!_pos _ _ (by simp; omega), List.getElem_append_right (by omega)]
            simp [hl]
  have hlt : ∀ n ≤ 693, R n < 100000 := by
    intro n hn
    by_contra hc
    have := hbig' n (693 - n) (Nat.le_of_not_lt hc)
    rw [Nat.add_sub_cancel' hn, hR693] at this
    omega
  obtain ⟨hl, ht⟩ := inv 693 (hlt 693 le_rfl)
  rw [hR693] at hl ht
  have hdec : (decA UP 12 693).toList = (List.range 693).map (up UP) := by
    apply List.ext_getElem (by simp only [decA, Array.toList_ofFn, List.length_ofFn,
      List.length_map, List.length_range])
    intro j h1 h2
    simp only [decA, Array.toList_ofFn, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    rfl
  apply Array.toList_inj.1
  rw [tvGensG, Array.toList_push, Array.toList_filter, hdec]
  change (decA TV 12 46).toList = filt 693 ++ [85]
  rw [decA, Array.toList_ofFn]
  apply List.ext_getElem (by rw [List.length_ofFn, List.length_append, ← hl]; rfl)
  intro j h1 h2
  have hj : j < 46 := by rwa [List.length_ofFn] at h1
  rw [List.getElem_ofFn]
  show fget TV j 12 = _
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
  · rw [List.getElem_append_left (by omega)]
    rw [ht j hj, getElem!_pos _ j (by omega)]
  · subst hj
    rw [List.getElem_append_right (by omega)]
    simp only [← hl, Nat.sub_self, List.getElem_cons_zero]
    exact h45

open Snd in
theorem letters_sound {UP POS TV LT : Nat} {pts pos tvg : Array Nat} (hu : decA UP 12 693 = pts)
    (hp : decA POS 10 4096 = pos) (ht : decA TV 12 46 = tvg)
    (hl : ∀ k < 46, letOK UP POS TV LT k = true) :
    ∀ k < 46, (tvTableG pts pos tvg[k]!).size = 693 ∧ Nat.shiftRight (letK LT k) 6930 = 0 ∧
      ∀ p < 693, ap (tvTableG pts pos tvg[k]!) p = ap10 (letK LT k) p ∧
        ap10 (letK LT k) p < 693 := by
  subst hu hp ht
  intro k hk
  have h := hl k hk
  unfold letOK at h
  rw [strictB_eq, strictB_eq, andB_iff, beq_iff] at h
  obtain ⟨h1, h2⟩ := h
  have H := allBelow_spec h2 (by norm_num)
  refine ⟨by simp [tvTableG], h1, fun p hp => ?_⟩
  have hq := H p hp
  dsimp only at hq
  rw [strictB_eq, andB_iff, andB_iff, beq_iff, beq_iff] at hq
  obtain ⟨e1, e2, -⟩ := hq
  have e2' : ap10 (letK LT k) p < 693 := blt_iff.1 e2
  refine ⟨?_, e2'⟩
  obtain ⟨en, bn⟩ := normK_eq (tvC (fget TV k 12) (fget UP p 12))
  have hT : (tvTableG (decA UP 12 693) (decA POS 10 4096) (decA TV 12 46)[k]!)[p]! =
      UInt32.ofNat (tabK UP POS (fget TV k 12) p) := by
    rw [tvTableG, getElem!_pos _ p (by simpa using hp), Array.getElem_ofFn]
    simp only
    rw [decA_get _ _ _ _ hk, decA_get _ _ _ _ hp, decA_get _ _ _ _ bn]
    apply congrArg UInt32.ofNat
    show fget POS (normC (tvC (fget TV k 12) (fget UP p 12))) 10 =
      fget POS (normK (tvK (fget TV k 12) (fget UP p 12))) 10
    rw [tvK_eq, en]
  unfold ap
  rw [hT, e1, UInt32.toNat_ofNat_of_lt' (Nat.lt_trans e2' (by norm_num))]

open Snd in
theorem sound3180 {UP POS TV LT : Nat} {pts pos tvg : Array Nat} (hu : decA UP 12 693 = pts)
    (hp : decA POS 10 4096 = pos) (ht : decA TV 12 46 = tvg)
    (hl : ∀ k < 46, letOK UP POS TV LT k = true)
    (_hne : ∀ k < 46, ∃ p < 693, ap10 (letK LT k) p ≠ p) :
    ∀ k : ℕ, k < 46 → involOK (tvTableG pts pos tvg[((k : ℤ) + 1).natAbs - 1]!) = true := by
  intro k hk
  have e : ((k : ℤ) + 1).natAbs - 1 = k := by omega
  rw [e]
  obtain ⟨-, -, H⟩ := letters_sound hu hp ht hl k hk
  have hinv : ∀ p < 693, ap10 (letK LT k) (ap10 (letK LT k) p) = p := by
    intro p hp
    have h := hl k hk
    unfold letOK at h
    rw [strictB_eq, strictB_eq, andB_iff] at h
    have hq := allBelow_spec h.2 (by norm_num) p hp
    dsimp only at hq
    rw [strictB_eq, andB_iff, andB_iff, beq_iff, beq_iff] at hq
    exact hq.2.2
  unfold involOK invoOK
  rw [Bool.and_eq_true, allIn_iff, allIn_iff]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [(H i hi).1]
    exact decide_eq_true (H i hi).2
  · rw [(H i hi).1, (H _ (H i hi).2).1, hinv i hi]
    exact beq_self_eq_true i

end CFSG.KC.U6

end
