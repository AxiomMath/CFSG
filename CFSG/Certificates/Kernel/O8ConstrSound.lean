module

public import Certificates.Data.Kernel.O8.Nat8
import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Data
public import CFSG.Open.LocalVocabulary
public import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KS CFSG.KS.Raw CFSG.KC.Enum CFSG.EvenSmallLie
  CFSG.EvenSmallLie.OmegaEight.Stage1

@[expose] def eichG (q : ℕ → Bool) (b : ℕ → ℕ → Bool) (u w x : ℕ) : ℕ :=
  x ^^^ (if b x u then w else 0) ^^^ (if b x w then u else 0) ^^^ (if q w && b x u then u else 0)

@[expose] def transG (b : ℕ → ℕ → Bool) (v x : ℕ) : ℕ := if b x v then x ^^^ v else x

@[expose] def nsListG (q : ℕ → Bool) : List ℕ := (List.range 256).filter q

@[expose] def nsArrG (q : ℕ → Bool) : Array ℕ := (nsListG q).toArray

@[expose] def nsIdxG (q : ℕ → Bool) : Array ℕ :=
  Array.ofFn (n := 256) fun v => (nsListG q).idxOf v.val

@[expose] def rootArrG (q : ℕ → Bool) (b : ℕ → ℕ → Bool) (p : List (ℕ × ℕ)) : Array ℕ :=
  Array.ofFn (n := 360) fun i =>
    120 * (i.val / 120) +
      (nsIdxG q)[eichG q b (p.getD (i.val / 120) (0, 0)).1 (p.getD (i.val / 120) (0, 0)).2
        (nsArrG q)[i.val % 120]!]!

@[expose] def tauArrG (q : ℕ → Bool) (b : ℕ → ℕ → Bool) : Array ℕ :=
  Array.ofFn (n := 360) fun i =>
    120 * ((3 - i.val / 120) % 3) + (nsIdxG q)[transG b 136 (nsArrG q)[i.val % 120]!]!

@[expose] def genArrsPG (q : ℕ → Bool) (b : ℕ → ℕ → Bool) (RPs : List (List (ℕ × ℕ))) :
    Array (Array ℕ) :=
  (RPs.map (rootArrG q b)).toArray ++ #[OmegaEight.rhoArr, tauArrG q b]

@[expose] def eichArrG (q : ℕ → Bool) (b : ℕ → ℕ → Bool) (p : ℕ × ℕ) : Array ℕ :=
  Array.ofFn (n := 136) fun i => (nsIdxG q)[eichG q b p.1 p.2 (nsArrG q)[i.val]!]!

@[expose] def reflArrG (q : ℕ → Bool) (b : ℕ → ℕ → Bool) : Array ℕ :=
  Array.ofFn (n := 136) fun i => (nsIdxG q)[transG b 64 (nsArrG q)[i.val]!]!

@[expose] def genArrsMG (q : ℕ → Bool) (b : ℕ → ℕ → Bool) (GPs : List (ℕ × ℕ)) :
    Array (Array ℕ) :=
  (GPs.map (eichArrG q b)).toArray ++ #[reflArrG q b]

@[expose] def fromWG (bp : ℕ → ℕ) (y : ℕ) : ℕ :=
  (List.range 6).foldl (fun acc j => if y.testBit j then acc ^^^ 2 ^ bp j else acc) 0

@[expose] def psiArrG (n : ℕ) (q : ℕ → Bool) (b : ℕ → ℕ → Bool) (bp : ℕ → ℕ) (y : ℕ) :
    Array ℕ :=
  Array.ofFn (n := n) fun i => (nsIdxG q)[eichG q b 1 (fromWG bp y) (nsArrG q)[i.val]!]!

@[expose] def FormBind (e : Bool) (q : ℕ → Bool) (b : ℕ → ℕ → Bool) : Prop :=
  (∀ v < 256, q v = (q8K e v == 1)) ∧ ∀ v < 256, ∀ w < 256, b v w = (b8K e v w == 1)

private theorem nxor (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
private theorem nland (a b : ℕ) : Nat.land a b = a &&& b := rfl
private theorem nmul (a b : ℕ) : Nat.mul a b = a * b := rfl
private theorem nadd (a b : ℕ) : Nat.add a b = a + b := rfl
private theorem nsub (a b : ℕ) : Nat.sub a b = a - b := rfl
private theorem ndiv (a b : ℕ) : Nat.div a b = a / b := rfl
private theorem nmod (a b : ℕ) : Nat.mod a b = a % b := rfl
private theorem nshl (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl
private theorem nsucc (a : ℕ) : Nat.succ a = a + 1 := rfl

private theorem ctAndB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by cases a <;> rfl

private theorem ctOrB_eq (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by cases a <;> rfl

private theorem nIf_eq (c : Bool) (t e : ℕ) : nIf(c, t, e) = if c = true then t else e := by
  cases c <;> rfl

private theorem nIf_lt {c : Bool} {t e m : ℕ} (ht : t < m) (he : e < m) : nIf(c, t, e) < m := by
  cases c
  · exact he
  · exact ht

private theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem ctAllN_iff {n : ℕ} {f : ℕ → Bool} :
    CFSG.KLie.CT.allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [CFSG.KLie.CT.allN]
  | succ n ih =>
    change CFSG.KLie.CT.andB (f n) (CFSG.KLie.CT.allN n f) = true ↔ _
    rw [ctAndB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_ge i n with h | h
      · exact h2 i h
      · have e : i = n := by omega
        rw [e]
        exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (by omega)⟩

private theorem orN_succ' (n : ℕ) (f : ℕ → ℕ) :
    CFSG.KLie.CT.orN (n + 1) f = f n ||| CFSG.KLie.CT.orN n f := rfl

private theorem orN_zero' (f : ℕ → ℕ) : CFSG.KLie.CT.orN 0 f = 0 := rfl

private theorem maskN_eq' (w : ℕ) : maskN w = 2 ^ w - 1 := by
  rw [maskN, pw2]
  change (1 <<< w) - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

private theorem mask_eq' (w : ℕ) : mask w = 2 ^ w - 1 := by
  change (1 <<< w) - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

private theorem fget_eq' (X i w : ℕ) : fget X i w = X >>> (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& maskN w = _
  rw [maskN_eq', Nat.and_two_pow_sub_one_eq_mod]

private theorem fget_lt' (X i w : ℕ) : fget X i w < 2 ^ w := by
  rw [fget_eq']
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

private theorem pg_eq' (w p i : ℕ) : pg w (mask w) p i = p >>> (w * i) % 2 ^ w := by
  change (p >>> (w * i)) &&& mask w = _
  rw [mask_eq', Nat.and_two_pow_sub_one_eq_mod]

private theorem testBit_orN' {d n : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ d) (p : ℕ) :
    (CFSG.KLie.CT.orN n fun i => f i <<< (d * i)).testBit p =
      (decide (p < d * n) && (f (p / d)).testBit (p % d)) := by
  induction n with
  | zero => simp [CFSG.KLie.CT.orN]
  | succ n ih =>
    rw [orN_succ', Nat.testBit_or, Nat.testBit_shiftLeft, ih fun i hi => hf i (by omega),
      Nat.mul_succ]
    have hn := hf n (by omega)
    by_cases h1 : p < d * n
    · have : ¬ (p ≥ d * n) := by omega
      simp [h1, this, show p < d * n + d by omega]
    · by_cases h2 : p < d * n + d
      · have hd : 0 < d := by omega
        have hq : p / d = n := by
          rw [Nat.div_eq_iff hd]
          constructor <;> [rw [Nat.mul_comm]; rw [Nat.mul_comm]] <;> omega
        have hr : p % d = p - d * n := by
          rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]
        simp [h1, h2, hq, hr, show p ≥ d * n by omega]
      · have hb : (f n).testBit (p - d * n) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) (by omega)))
        simp [h1, h2, hb]

private theorem field_orN {w n : ℕ} {g : ℕ → ℕ} (hg : ∀ i < n, g i < 2 ^ w) {j : ℕ} (hj : j < n) :
    (CFSG.KLie.CT.orN n fun i => g i <<< (w * i)) >>> (w * j) % 2 ^ w = g j := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, testBit_orN' hg]
  by_cases ht : t < w
  · have hw : 0 < w := by omega
    have e1 : (w * j + t) / w = j := by
      rw [Nat.mul_add_div hw, Nat.div_eq_of_lt ht, Nat.add_zero]
    have e2 : (w * j + t) % w = t := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
    have e3 : w * j + t < w * n := by
      have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hj)
      rw [Nat.mul_succ] at this
      omega
    simp [ht, e1, e2, e3]
  · simp only [ht, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hg j hj)
      (Nat.pow_le_pow_right (by decide) (by omega)))).symm

private theorem pg_orN {w n : ℕ} {g : ℕ → ℕ} (hg : ∀ i < n, g i < 2 ^ w) {j : ℕ} (hj : j < n) :
    pg w (mask w) (CFSG.KLie.CT.orN n fun i => Nat.shiftLeft (g i) (Nat.mul w i)) j = g j := by
  rw [pg_eq']
  exact field_orN hg hj

private theorem fget_orN {w n : ℕ} {g : ℕ → ℕ} (hg : ∀ i < n, g i < 2 ^ w) {j : ℕ} (hj : j < n) :
    fget (CFSG.KLie.CT.orN n fun i => Nat.shiftLeft (g i) (Nat.mul w i)) j w = g j := by
  rw [fget_eq', Nat.mul_comm j w]
  exact field_orN hg hj

private theorem bitN_eq (x i : ℕ) : bitN x i = if x.testBit i then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change (x >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

private theorem bitN_lt (x i : ℕ) : bitN x i < 2 := by
  rw [bitN_eq]
  split <;> omega

private theorem bb_lt (x y i j : ℕ) : bb x y i j < 2 := by
  change bitN x i &&& bitN y j < 2
  exact Nat.lt_of_le_of_lt Nat.and_le_right (bitN_lt y j)

private theorem xor2 {a c : ℕ} (ha : a < 2) (hc : c < 2) : a ^^^ c < 2 :=
  Nat.xor_lt_two_pow (n := 1) ha hc

private theorem b8K_lt (e : Bool) (v w : ℕ) : b8K e v w < 2 := by
  cases e <;> simp only [b8K, nxor] <;> (repeat' apply xor2) <;> exact bb_lt _ _ _ _

private theorem q8K_lt (e : Bool) (v : ℕ) : q8K e v < 2 := by
  cases e <;> simp only [q8K, nxor] <;> (repeat' apply xor2) <;>
    first | exact bb_lt _ _ _ _ | exact bitN_lt _ _

private theorem fb_q {e : Bool} {q : ℕ → Bool} {b : ℕ → ℕ → Bool} (hf : FormBind e q b)
    {v : ℕ} (hv : v < 256) : q v = (q8K e v == 1) := by
  unfold FormBind at hf
  exact hf.1 v hv

private theorem fb_b {e : Bool} {q : ℕ → Bool} {b : ℕ → ℕ → Bool} (hf : FormBind e q b)
    {v w : ℕ} (hv : v < 256) (hw : w < 256) : b v w = (b8K e v w == 1) := by
  unfold FormBind at hf
  exact hf.2 v hv w hw

private theorem b8K_ite {e : Bool} {q : ℕ → Bool} {b : ℕ → ℕ → Bool} (hf : FormBind e q b)
    {v w : ℕ} (hv : v < 256) (hw : w < 256) : b8K e v w = if b v w then 1 else 0 := by
  rw [fb_b hf hv hw]
  have := b8K_lt e v w
  rcases (by omega : b8K e v w = 0 ∨ b8K e v w = 1) with h | h <;> simp [h]

private theorem q8K_ite {e : Bool} {q : ℕ → Bool} {b : ℕ → ℕ → Bool} (hf : FormBind e q b)
    {v : ℕ} (hv : v < 256) : q8K e v = if q v then 1 else 0 := by
  rw [fb_q hf hv]
  have := q8K_lt e v
  rcases (by omega : q8K e v = 0 ∨ q8K e v = 1) with h | h <;> simp [h]

private theorem eichK_eq {e : Bool} {q : ℕ → Bool} {b : ℕ → ℕ → Bool} (hf : FormBind e q b)
    {u w x : ℕ} (hu : u < 256) (hw : w < 256) (hx : x < 256) :
    eichK e u w x = eichG q b u w x := by
  unfold eichK eichG
  simp only [nxor, nmul, nland]
  rw [b8K_ite hf hx hu, b8K_ite hf hx hw, q8K_ite hf hw]
  cases b x u <;> cases b x w <;> cases q w <;> simp [Nat.xor_assoc]

private theorem transK_eq {e : Bool} {q : ℕ → Bool} {b : ℕ → ℕ → Bool} (hf : FormBind e q b)
    {v x : ℕ} (hv : v < 256) (hx : x < 256) : transK e v x = transG b v x := by
  unfold transK transG
  simp only [nxor, nmul]
  rw [b8K_ite hf hx hv]
  cases b x v <;> simp

private theorem ite_lt {c : Prop} [Decidable c] {a m : ℕ} (ha : a < m) (hm : 0 < m) :
    (if c then a else 0) < m := by
  split
  · exact ha
  · exact hm

private theorem eichG_lt {q : ℕ → Bool} {b : ℕ → ℕ → Bool} {u w x : ℕ} (hu : u < 256)
    (hw : w < 256) (hx : x < 256) : eichG q b u w x < 256 := by
  have h8 : (256 : ℕ) = 2 ^ 8 := rfl
  rw [h8] at hu hw hx ⊢
  unfold eichG
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hx (ite_lt hw (by decide)))
    (ite_lt hu (by decide))) (ite_lt hu (by decide))

private theorem transG_lt {b : ℕ → ℕ → Bool} {v x : ℕ} (hv : v < 256) (hx : x < 256) :
    transG b v x < 256 := by
  have h8 : (256 : ℕ) = 2 ^ 8 := rfl
  unfold transG
  split
  · rw [h8] at hv hx ⊢
    exact Nat.xor_lt_two_pow hx hv
  · exact hx

private theorem mono_of_succ {g : ℕ → ℕ} {N : ℕ} (h : ∀ j, 0 < j → j < N → g (j - 1) < g j) :
    ∀ i j, i < j → j < N → g i < g j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hs := h (j + 1) (by omega) hj
    rw [Nat.add_sub_cancel] at hs
    rcases Nat.lt_or_ge i j with h' | h'
    · exact Nat.lt_trans (ih h' (by omega)) hs
    · have e : i = j := by omega
      rw [e]
      exact hs

private theorem ns_facts {e : Bool} {q : ℕ → Bool} {b : ℕ → ℕ → Bool} {N NS NI : ℕ}
    (hf : FormBind e q b) (hns : nsOK e N NS NI = true) :
    (nsListG q).length = N ∧ (∀ j < N, (nsArrG q)[j]! = fget NS j 8) ∧
      ∀ v < 256, (nsIdxG q)[v]! = fget NI v 8 := by
  unfold nsOK at hns
  rw [ctAndB_eq, Bool.and_eq_true, ctAllN_iff, ctAllN_iff] at hns
  obtain ⟨h1, h2⟩ := hns
  have hA : ∀ j < N, fget NS j 8 < 256 ∧ q8K e (fget NS j 8) = 1 ∧ fget NI (fget NS j 8) 8 = j ∧
      (j = 0 ∨ fget NS (j - 1) 8 < fget NS j 8) := by
    intro j hj
    have := h1 j hj
    simp only [ctAndB_eq, ctOrB_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq,
      nsub] at this
    exact this
  have hB : ∀ v < 256, (q8K e v = 1 → fget NI v 8 < N ∧ fget NS (fget NI v 8) 8 = v) ∧
      (q8K e v ≠ 1 → fget NI v 8 = N) := by
    intro v hv
    have h := h2 v hv
    cases hq : Nat.beq (q8K e v) 1
    · have hq' : q8K e v ≠ 1 := Nat.ne_of_beq_eq_false hq
      simp only [hq] at h
      exact ⟨fun h' => absurd h' hq', fun _ => Nat.eq_of_beq_eq_true h⟩
    · have hq' : q8K e v = 1 := Nat.eq_of_beq_eq_true hq
      simp only [hq, ctAndB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
      exact ⟨fun _ => h, fun h' => absurd hq' h'⟩
  obtain ⟨M, hMdef⟩ : ∃ M : List ℕ, M = (List.range N).map fun j => fget NS j 8 := ⟨_, rfl⟩
  have hMs : M.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [hMdef, List.length_map, List.length_range] at hi hj
    simp only [hMdef, List.getElem_map, List.getElem_range]
    exact mono_of_succ (g := fun j => fget NS j 8) (fun j hj0 hjN => by
      rcases (hA j hjN).2.2.2 with h | h
      · omega
      · exact h) i j hij hj
  have hLs : (nsListG q).Pairwise (· < ·) := List.pairwise_lt_range.filter _
  have hmem : ∀ a, a ∈ M ↔ a ∈ nsListG q := by
    intro a
    simp only [hMdef, nsListG, List.mem_map, List.mem_range, List.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨(hA j hj).1, ?_⟩
      rw [fb_q hf (hA j hj).1, (hA j hj).2.1]
      rfl
    · rintro ⟨ha, hq⟩
      have hq' : q8K e a = 1 := by
        rw [fb_q hf ha] at hq
        exact Nat.eq_of_beq_eq_true hq
      exact ⟨fget NI a 8, ((hB a ha).1 hq').1, ((hB a ha).1 hq').2⟩
  have hML : M = nsListG q := hMs.eq_of_mem_iff hLs hmem
  have hMlen : M.length = N := by simp [hMdef]
  have hMget : ∀ j < N, M[j]! = fget NS j 8 := by
    intro j hj
    rw [getElem!_pos M j (by omega)]
    simp [hMdef]
  refine ⟨hML ▸ hMlen, fun j hj => ?_, fun v hv => ?_⟩
  · rw [nsArrG, List.getElem!_toArray, ← hML, hMget j hj]
  · rw [nsIdxG, CFSG.Monster.B.Co2.getElem!_ofFn_nat _ hv]
    simp only [← hML]
    by_cases hq : q8K e v = 1
    · obtain ⟨hi, hv'⟩ := (hB v hv).1 hq
      have hnd : M.Nodup := hMs.imp Nat.ne_of_lt
      have e1 : M[fget NI v 8]'(by omega) = v := by
        rw [← getElem!_pos M _ (by omega), hMget _ hi, hv']
      calc M.idxOf v = M.idxOf (M[fget NI v 8]'(by omega)) := by rw [e1]
        _ = fget NI v 8 := hnd.idxOf_getElem _ _
    · rw [(hB v hv).2 hq, List.idxOf_eq_length, hMlen]
      rw [hmem, nsListG, List.mem_filter]
      rintro ⟨-, hq2⟩
      rw [fb_q hf hv] at hq2
      exact hq (Nat.eq_of_beq_eq_true hq2)

private theorem nsMap_eq {e : Bool} {q : ℕ → Bool} {b : ℕ → ℕ → Bool} {N NS NI : ℕ}
    (hf : FormBind e q b) (hns : nsOK e N NS NI = true) {f : ℕ → ℕ}
    (hfl : ∀ x < 256, f x < 256) {j : ℕ} (hj : j < N) :
    nsMap NS NI f j = (nsIdxG q)[f (nsArrG q)[j]!]! := by
  obtain ⟨-, hNS, hNI⟩ := ns_facts hf hns
  have hx : fget NS j 8 < 256 := fget_lt' NS j 8
  rw [nsMap, hNS j hj, hNI _ (hfl _ hx)]

private theorem getElem!_append_lt {A B : Array (Array ℕ)} {j : ℕ} (h : j < A.size) :
    (A ++ B)[j]! = A[j]! := by
  rw [getElem!_pos (A ++ B) j (by simp; omega), getElem!_pos A j h, Array.getElem_append_left h]

private theorem getElem!_append_ge {A B : Array (Array ℕ)} {j : ℕ} (h1 : A.size ≤ j)
    (h2 : j < A.size + B.size) : (A ++ B)[j]! = B[j - A.size]! := by
  rw [getElem!_pos (A ++ B) j (by simp; omega), getElem!_pos B (j - A.size) (by omega),
    Array.getElem_append_right h1]

private theorem lit2_get0 (a c : Array ℕ) : (#[a, c] : Array (Array ℕ))[0]! = a := rfl

private theorem lit2_get1 (a c : Array ℕ) : (#[a, c] : Array (Array ℕ))[1]! = c := rfl

private theorem lit1_get0 (a : Array ℕ) : (#[a] : Array (Array ℕ))[0]! = a := rfl

private theorem arr_ext {A B : Array ℕ} {n : ℕ} (hA : A.size = n) (hB : B.size = n)
    (h : ∀ i < n, A[i]! = B[i]!) : A = B := by
  apply Array.ext (by omega)
  intro i h1 h2
  have := h i (by omega)
  rwa [getElem!_pos A i h1, getElem!_pos B i h2] at this

private theorem unpack_size (n w P : ℕ) : (unpack n w P).size = n := by
  simp [unpack]

private theorem ofFn_get {n : ℕ} (f : Fin n → ℕ) {i : ℕ} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ :=
  CFSG.Monster.B.Co2.getElem!_ofFn_nat f hi

private theorem push_get! {S : Array (Array ℕ)} {X : Array ℕ} {h : ℕ} (hh : h < S.size + 1) :
    (S.push X)[h]! = if h < S.size then S[h]! else X := by
  rw [getElem!_pos (S.push X) h (by simp; omega)]
  by_cases h1 : h < S.size
  · rw [Array.getElem_push_lt h1, getElem!_pos S h h1, ite_eq_left_iff.2 (fun h2 => absurd h1 h2)]
  · have e : h = S.size := by omega
    subst e
    rw [Array.getElem_push_eq, ite_eq_right_iff.2 (fun h2 => absurd h2 (Nat.lt_irrefl _))]

private theorem nsMap_lt (NS NI : ℕ) (f : ℕ → ℕ) (j : ℕ) : nsMap NS NI f j < 256 :=
  fget_lt' _ _ 8

private theorem bound3 {k x : ℕ} (hk : k < 3) (hx : x < 256) : 120 * k + x < 2 ^ 9 := by
  have h : (2 : ℕ) ^ 9 = 512 := rfl
  rw [h]
  omega

private theorem fromW_P {bp : ℕ → ℕ} (hbp : ∀ j < 6, bp j = fget 5665569 j 4) (y : ℕ) :
    fromWG bp y = fromWK 5665569 y ∧ fromWK 5665569 y < 256 := by
  have hr : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
  unfold fromWG fromWK
  rw [hr, orN_succ', orN_succ', orN_succ', orN_succ', orN_succ', orN_succ', orN_zero']
  simp only [List.foldl_cons, List.foldl_nil, hbp 0 (by decide), hbp 1 (by decide),
    hbp 2 (by decide), hbp 3 (by decide), hbp 4 (by decide), hbp 5 (by decide), bitN_eq, nshl]
  generalize y.testBit 0 = b0
  generalize y.testBit 1 = b1
  generalize y.testBit 2 = b2
  generalize y.testBit 3 = b3
  generalize y.testBit 4 = b4
  generalize y.testBit 5 = b5
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

private theorem fromW_M {bp : ℕ → ℕ} (hbp : ∀ j < 6, bp j = fget 4552225 j 4) (y : ℕ) :
    fromWG bp y = fromWK 4552225 y ∧ fromWK 4552225 y < 256 := by
  have hr : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
  unfold fromWG fromWK
  rw [hr, orN_succ', orN_succ', orN_succ', orN_succ', orN_succ', orN_succ', orN_zero']
  simp only [List.foldl_cons, List.foldl_nil, hbp 0 (by decide), hbp 1 (by decide),
    hbp 2 (by decide), hbp 3 (by decide), hbp 4 (by decide), hbp 5 (by decide), bitN_eq, nshl]
  generalize y.testBit 0 = b0
  generalize y.testBit 1 = b1
  generalize y.testBit 2 = b2
  generalize y.testBit 3 = b3
  generalize y.testBit 4 = b4
  generalize y.testBit 5 = b5
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

private theorem psi_sound {e : Bool} {q : ℕ → Bool} {b : ℕ → ℕ → Bool} {bp : ℕ → ℕ}
    {N w P NS NI : ℕ} (hf : FormBind e q b) (hns : nsOK e N NS NI = true) (hw : 256 ≤ 2 ^ w)
    (y : ℕ) (hW : fromWG bp y = fromWK P y ∧ fromWK P y < 256) :
    (psiArrG N q b bp y).toList = (List.range N).map fun i => fget (psiK e NS NI N w P y) i w := by
  apply List.ext_getElem
  · simp [psiArrG]
  intro i h1 h2
  simp only [Array.length_toList, Array.size_ofFn, psiArrG] at h1
  simp only [Array.getElem_toList, psiArrG, Array.getElem_ofFn, List.getElem_map,
    List.getElem_range]
  rw [psiK, strictN_eq']
  obtain ⟨-, hNS, -⟩ := ns_facts hf hns
  have hx : (nsArrG q)[i]! < 256 := by
    rw [hNS i h1]
    exact fget_lt' NS i 8
  have hfl : ∀ x < 256, eichK e 1 (fromWK P y) x < 256 := fun x hx => by
    rw [eichK_eq hf (by decide) hW.2 hx]
    exact eichG_lt (by decide) hW.2 hx
  have hg : ∀ i < N, nsMap NS NI (eichK e 1 (fromWK P y)) i < 2 ^ w := fun i _ =>
    Nat.lt_of_lt_of_le (nsMap_lt _ _ _ _) hw
  rw [fget_orN hg h1, nsMap_eq hf hns hfl h1, eichK_eq hf (by decide) hW.2 hx, hW.1]

theorem genP_sound {q : ℕ → Bool} {b : ℕ → ℕ → Bool} {RPs : List (List (ℕ × ℕ))} {NS NI : Nat}
    (hf : FormBind false q b) (hns : nsOK false 120 NS NI = true)
    (hR : RPs.length = 8 ∧ ∀ j < 8, ∀ t < 3,
      (RPs.getD j []).getD t (0, 0) = (fget RP (6 * j + 2 * t) 8, fget RP (6 * j + 2 * t + 1) 8)) :
    (genArrsPG q b RPs).size = 10 ∧
      ∀ j < 10, (genArrsPG q b RPs)[j]! = unpack 360 9 (genP NS NI j) := by
  obtain ⟨hR1, hR2⟩ := hR
  have hA8 : ((RPs.map (rootArrG q b)).toArray).size = 8 := by simp [hR1]
  refine ⟨by simp [genArrsPG, hR1], fun j hj => ?_⟩
  obtain ⟨-, hNS, -⟩ := ns_facts hf hns
  have hfl : ∀ i < 120, (nsArrG q)[i]! < 256 := fun i hi => by
    rw [hNS i hi]
    exact fget_lt' NS i 8
  unfold genArrsPG
  by_cases h8 : j < 8
  · have hjl : j < RPs.length := by omega
    rw [getElem!_append_lt (A := (RPs.map (rootArrG q b)).toArray) (by omega),
      List.getElem!_toArray, getElem!_pos (RPs.map (rootArrG q b)) j (by simpa using hjl),
      List.getElem_map]
    have hb : Nat.blt j 8 = true := by
      rw [Nat.blt_eq]
      exact h8
    have eG : genP NS NI j = rootPK NS NI (fget RP (6 * j + 0) 8) (fget RP (6 * j + 1) 8)
        (fget RP (6 * j + 2) 8) (fget RP (6 * j + 3) 8) (fget RP (6 * j + 4) 8)
        (fget RP (6 * j + 5) 8) :=
      congrArg (fun c => nIf(c, rootPK NS NI (fget RP (6 * j + 0) 8) (fget RP (6 * j + 1) 8)
        (fget RP (6 * j + 2) 8) (fget RP (6 * j + 3) 8) (fget RP (6 * j + 4) 8)
        (fget RP (6 * j + 5) 8), nIf(Nat.beq j 8, rhoPK, tauPK NS NI))) hb
    rw [eG]
    apply arr_ext (n := 360) (by simp [rootArrG]) (unpack_size _ _ _)
    intro i hi
    rw [rootArrG, ofFn_get _ hi, Orb.unpack_get hi, rootPK]
    refine Eq.symm ((pg_orN ?_ hi).trans ?_)
    · intro i' hi'
      simp only [nadd, nmul, ndiv, nmod]
      have h3 : i' / 120 < 3 := by omega
      exact bound3 h3 (nsMap_lt _ _ _ _)
    simp only [nadd, nmul, ndiv, nmod]
    have hk : i / 120 < 3 := by omega
    have hr : i % 120 < 120 := Nat.mod_lt _ (by decide)
    have hU : ∀ k, nIf(Nat.beq k 0, fget RP (6 * j + 0) 8,
        nIf(Nat.beq k 1, fget RP (6 * j + 2) 8, fget RP (6 * j + 4) 8)) < 256 := fun k =>
      nIf_lt (fget_lt' _ _ 8) (nIf_lt (fget_lt' _ _ 8) (fget_lt' _ _ 8))
    have hW : ∀ k, nIf(Nat.beq k 0, fget RP (6 * j + 1) 8,
        nIf(Nat.beq k 1, fget RP (6 * j + 3) 8, fget RP (6 * j + 5) 8)) < 256 := fun k =>
      nIf_lt (fget_lt' _ _ 8) (nIf_lt (fget_lt' _ _ 8) (fget_lt' _ _ 8))
    have hfl' : ∀ x < 256, eichK false (nIf(Nat.beq (i / 120) 0, fget RP (6 * j + 0) 8,
        nIf(Nat.beq (i / 120) 1, fget RP (6 * j + 2) 8, fget RP (6 * j + 4) 8)))
        (nIf(Nat.beq (i / 120) 0, fget RP (6 * j + 1) 8,
        nIf(Nat.beq (i / 120) 1, fget RP (6 * j + 3) 8, fget RP (6 * j + 5) 8))) x < 256 :=
      fun x hx => by
        rw [eichK_eq hf (hU _) (hW _) hx]
        exact eichG_lt (hU _) (hW _) hx
    rw [nsMap_eq hf hns hfl' hr, eichK_eq hf (hU _) (hW _) (hfl _ hr)]
    have hRj : RPs.getD j [] = RPs[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
    have hP := hR2 j h8 (i / 120) hk
    rw [hRj] at hP
    rw [hP]
    generalize i / 120 = k at hk ⊢
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> rfl
  · have hsz : ((RPs.map (rootArrG q b)).toArray).size ≤ j := by omega
    have hsz2 : j < ((RPs.map (rootArrG q b)).toArray).size +
        (#[OmegaEight.rhoArr, tauArrG q b] : Array (Array ℕ)).size := by simp [hR1]; omega
    rw [getElem!_append_ge hsz hsz2, hA8]
    rcases (by omega : j = 8 ∨ j = 9) with rfl | rfl
    · have eG : genP NS NI 8 = rhoPK := rfl
      rw [eG, Nat.sub_self, lit2_get0]
      apply arr_ext (n := 360) (by simp [OmegaEight.rhoArr]) (unpack_size _ _ _)
      intro i hi
      rw [Orb.unpack_get hi, rhoPK]
      refine Eq.symm ((pg_orN ?_ hi).trans ?_)
      · intro i' _
        simp only [nadd, nmod]
        exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
      simp only [nadd, nmod]
      rw [OmegaEight.rhoArr, ofFn_get _ hi]
    · have eG : genP NS NI 9 = tauPK NS NI := rfl
      have e9 : (9 : ℕ) - 8 = 1 := rfl
      rw [eG, e9, lit2_get1]
      apply arr_ext (n := 360) (by simp [tauArrG]) (unpack_size _ _ _)
      intro i hi
      rw [tauArrG, ofFn_get _ hi, Orb.unpack_get hi, tauPK]
      have hfl' : ∀ x < 256, transK false 136 x < 256 := fun x hx => by
        rw [transK_eq hf (by decide) hx]
        exact transG_lt (by decide) hx
      refine Eq.symm ((pg_orN ?_ hi).trans ?_)
      · intro i' _
        simp only [nadd, nmul, ndiv, nmod, nsub]
        exact bound3 (Nat.mod_lt _ (by decide)) (nsMap_lt _ _ _ _)
      simp only [nadd, nmul, ndiv, nmod, nsub]
      have hr : i % 120 < 120 := Nat.mod_lt _ (by decide)
      rw [nsMap_eq hf hns hfl' hr, transK_eq hf (by decide) (hfl _ hr)]

theorem genM_sound {q : ℕ → Bool} {b : ℕ → ℕ → Bool} {GPs : List (ℕ × ℕ)} {NS NI : Nat}
    (hf : FormBind true q b) (hns : nsOK true 136 NS NI = true)
    (hG : GPs.length = 10 ∧
      ∀ j < 10, GPs.getD j (0, 0) = (fget GP (2 * j) 8, fget GP (2 * j + 1) 8)) :
    (genArrsMG q b GPs).size = 11 ∧
      ∀ j < 11, (genArrsMG q b GPs)[j]! = unpack 136 8 (genM NS NI j) := by
  obtain ⟨hG1, hG2⟩ := hG
  have hA10 : ((GPs.map (eichArrG q b)).toArray).size = 10 := by simp [hG1]
  refine ⟨by simp [genArrsMG, hG1], fun j hj => ?_⟩
  obtain ⟨-, hNS, -⟩ := ns_facts hf hns
  have hfl : ∀ i < 136, (nsArrG q)[i]! < 256 := fun i hi => by
    rw [hNS i hi]
    exact fget_lt' NS i 8
  have hg : ∀ (f : ℕ → ℕ), ∀ i < 136, nsMap NS NI f i < 2 ^ 8 := fun f i _ => fget_lt' _ _ 8
  unfold genArrsMG
  by_cases h10 : j < 10
  · have hjl : j < GPs.length := by omega
    rw [getElem!_append_lt (A := (GPs.map (eichArrG q b)).toArray) (by omega),
      List.getElem!_toArray, getElem!_pos (GPs.map (eichArrG q b)) j (by simpa using hjl),
      List.getElem_map]
    have hb : Nat.blt j 10 = true := by
      rw [Nat.blt_eq]
      exact h10
    have eG : genM NS NI j = eichMK NS NI (fget GP (2 * j) 8) (fget GP (2 * j + 1) 8) :=
      congrArg (fun c => nIf(c, eichMK NS NI (fget GP (2 * j) 8) (fget GP (2 * j + 1) 8),
        transMK NS NI)) hb
    have hP := hG2 j h10
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some] at hP
    rw [eG, hP]
    apply arr_ext (n := 136) (by simp [eichArrG]) (unpack_size _ _ _)
    intro i hi
    rw [eichArrG, ofFn_get _ hi, Orb.unpack_get hi, eichMK, pg_orN (hg _) hi]
    have hu := fget_lt' GP (2 * j) 8
    have hw := fget_lt' GP (2 * j + 1) 8
    have h28 : (2 : ℕ) ^ 8 = 256 := rfl
    rw [h28] at hu hw
    have hfl' : ∀ x < 256, eichK true (fget GP (2 * j) 8) (fget GP (2 * j + 1) 8) x < 256 :=
      fun x hx => by
        rw [eichK_eq hf hu hw hx]
        exact eichG_lt hu hw hx
    rw [nsMap_eq hf hns hfl' hi, eichK_eq hf hu hw (hfl _ hi)]
  · have hj10 : j = 10 := by omega
    subst hj10
    have hsz : ((GPs.map (eichArrG q b)).toArray).size ≤ 10 := by omega
    have hsz2 : 10 < ((GPs.map (eichArrG q b)).toArray).size +
        (#[reflArrG q b] : Array (Array ℕ)).size := by simp [hG1]
    rw [getElem!_append_ge hsz hsz2, hA10]
    have eG : genM NS NI 10 = transMK NS NI := rfl
    rw [eG, Nat.sub_self, lit1_get0]
    apply arr_ext (n := 136) (by simp [reflArrG]) (unpack_size _ _ _)
    intro i hi
    rw [reflArrG, ofFn_get _ hi, Orb.unpack_get hi, transMK, pg_orN (hg _) hi]
    have hfl' : ∀ x < 256, transK true 64 x < 256 := fun x hx => by
      rw [transK_eq hf (by decide) hx]
      exact transG_lt (by decide) hx
    rw [nsMap_eq hf hns hfl' hi, transK_eq hf (by decide) (hfl _ hi)]

theorem psiP_sound {q : ℕ → Bool} {b : ℕ → ℕ → Bool} {bp : ℕ → ℕ} {NS NI : Nat}
    (hf : FormBind false q b) (hns : nsOK false 120 NS NI = true)
    (hbp : ∀ j < 6, bp j = fget 5665569 j 4) (y : Nat) :
    (psiArrG 120 q b bp y).toList =
      (List.range 120).map fun i => fget (psiK false NS NI 120 9 5665569 y) i 9 :=
  psi_sound hf hns (by decide) y (fromW_P hbp y)

theorem psiM_sound {q : ℕ → Bool} {b : ℕ → ℕ → Bool} {bp : ℕ → ℕ} {NS NI : Nat}
    (hf : FormBind true q b) (hns : nsOK true 136 NS NI = true)
    (hbp : ∀ j < 6, bp j = fget 4552225 j 4) (y : Nat) :
    (psiArrG 136 q b bp y).toList =
      (List.range 136).map fun i => fget (psiK true NS NI 136 8 4552225 y) i 8 :=
  psi_sound hf hns (by decide) y (fromW_M hbp y)

private theorem lenW_eq' : ∀ D : List (List Int), CFSG.KS.Mathieu.lenW D = D.length
  | [] => rfl
  | _ :: D => congrArg Nat.succ (lenW_eq' D)

private theorem wordA_size (n : ℕ) (S Sinv : Array (Array ℕ)) (wd : List ℤ) :
    (CFSG.Monster.B.Co2.Native.wordA n S Sinv wd).size = n := by
  cases wd <;> simp [CFSG.Monster.B.Co2.Native.wordA, CFSG.Monster.B.Co2.Native.idA,
    CFSG.Monster.B.Co2.Native.compA]

private theorem arr_eq_of_rep {n : ℕ} {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : t.size = n)
    (hu : u.size = n) (hgt : CFSG.Monster.B.Co2.Rep n t g) (hgu : CFSG.Monster.B.Co2.Rep n u g) :
    t = u :=
  arr_ext ht hu fun i hi => by rw [hgt.apply hi, hgu.apply hi]

theorem pushWords_eq {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat} {G : Array (Array Nat)}
    {D : List (List Int)} (hG : G.size = kO ∧ ∀ j < kO, G[j]! = unpack n w (PS j))
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    (OmegaEight.pushWords n G D).size = kS ∧
      ∀ j < kS, (OmegaEight.pushWords n G D)[j]! = unpack n w (PS j) := by
  unfold headK at hh
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨hsz, -, -, hlen, hperm, hder, -, -⟩ := hh
  unfold szOK at hsz
  simp only [Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hsz
  have hn24 : n < 16777216 := hsz.1
  have hw : n + 1 < 2 ^ w := by
    have := hsz.2
    rwa [nshl, Nat.shiftLeft_eq, Nat.one_mul] at this
  have hlen' : D.length + kO = kS := by
    have := Nat.eq_of_beq_eq_true hlen
    rwa [nadd, lenW_eq'] at this
  have hrep : ∀ h < kS, CFSG.Monster.B.Co2.Rep n (unpack n w (PS h))
      (CFSG.Monster.B.Co2.permOfArr n (unpack n w (PS h))) ∧
      CFSG.Monster.B.Co2.Rep n (unpack n w (PSI h))
        (CFSG.Monster.B.Co2.permOfArr n (unpack n w (PS h)))⁻¹ := fun h hh =>
    CFSG.Monster.B.Co2.rep_permOfArr (Orb.isInvA_unpack (Orb.allN_iff.1 hperm h hh))
  have key : ∀ (ws : List (List ℤ)) (S : Array (Array ℕ)), kO ≤ S.size →
      S.size + ws.length = kS → (∀ h < S.size, S[h]! = unpack n w (PS h)) →
      (∀ i (hi : i < ws.length), ws[i] = D.getD (S.size - kO + i) []) →
      (OmegaEight.pushWords n S ws).size = kS ∧
        ∀ j < kS, (OmegaEight.pushWords n S ws)[j]! = unpack n w (PS j) := by
    intro ws
    induction ws with
    | nil =>
      intro S _ hk hSe _
      simp only [List.length_nil, Nat.add_zero] at hk
      rw [OmegaEight.pushWords]
      exact ⟨hk, fun j hj => hSe j (by omega)⟩
    | cons wd ws ih =>
      intro S hkO hk hSe hws
      simp only [List.length_cons] at hk
      have hkS : S.size < kS := by omega
      have hwd : wd = D.getD (S.size - kO) [] := by
        have h0 := hws 0 (by simp)
        rw [List.getElem_cons_zero, Nat.add_zero] at h0
        exact h0
      have hX : CFSG.Monster.B.Co2.Native.wordA n S (CFSG.Certificates.Native.rawInvs n S) wd =
          unpack n w (PS S.size) := by
        have hd := Orb.allN_iff.1 hder S.size hkS
        rw [Orb.bIf_eq, ite_eq_right (by rw [Orb.blt_dec]; simpa using hkO), Orb.strictB_eq,
          Bool.and_eq_true, Orb.beq_dec, decide_eq_true_iff, Orb.dword_eq hkO, ← hwd] at hd
        obtain ⟨hl, he⟩ := hd
        obtain ⟨hP, hlo⟩ := Orb.prep_wordK
          (gs := fun h => CFSG.Monster.B.Co2.permOfArr n (unpack n w (PS h))) (j := S.size)
          hn24 hw (fun h hh => Orb.prep_of_rep (hrep h (by omega)).1)
          (fun h hh => Orb.prep_of_rep (hrep h (by omega)).2) wd hl
        have hS' : ∀ h < S.size, CFSG.Monster.B.Co2.Rep n S[h]!
            (CFSG.Monster.B.Co2.permOfArr n (unpack n w (PS h))) := fun h hh => by
          rw [hSe h hh]
          exact (hrep h (by omega)).1
        have hSi : ∀ h < S.size,
            CFSG.Monster.B.Co2.Rep n (CFSG.Certificates.Native.rawInvs n S)[h]!
              (CFSG.Monster.B.Co2.permOfArr n (unpack n w (PS h)))⁻¹ := fun h hh => by
          rw [Orb.rawInvs_get hh]
          exact rep_invCand (hS' h hh)
        have hrW := CFSG.Monster.B.Co2.rep_wordA hS' hSi wd hlo
        have hrP : CFSG.Monster.B.Co2.Rep n (unpack n w (PS S.size))
            (Quiver.SchreierGraph.evalWord
              (fun h : Fin S.size => CFSG.Monster.B.Co2.permOfArr n (unpack n w (PS h)))
              (CFSG.Monster.B.Co2.toLetters S.size wd)) := by
          rw [he]
          exact Orb.rep_unpack hP
        exact arr_eq_of_rep (wordA_size _ _ _ _) (unpack_size _ _ _) hrW hrP
      rw [OmegaEight.pushWords]
      refine ih _ (by simp; omega) (by simp; omega) (fun h hh => ?_) (fun i hi => ?_)
      · simp only [Array.size_push] at hh
        rw [push_get! hh]
        split
        · exact hSe h (by assumption)
        · have e : h = S.size := by omega
          rw [hX, e]
      · have := hws (i + 1) (by simp; omega)
        rw [List.getElem_cons_succ] at this
        rw [this, Array.size_push]
        congr 1
        omega
  obtain ⟨hG1, hG2⟩ := hG
  exact key D G (by omega) (by omega) (fun h hh => hG2 h (by omega))
    (fun i hi => by simp [List.getD_eq_getElem?_getD, hG1, hi])

theorem wordsOf_eq (k : Nat) (D : List (List Int)) :
    OmegaEight.wordsOf k D =
      CFSG.Sporadic.Schreier.Co3.Native.wordsArr k (k + D.length) D := by
  apply Array.ext
  · simp [OmegaEight.wordsOf, CFSG.Sporadic.Schreier.Co3.Native.wordsArr]
  · intro i h1 h2
    simp only [OmegaEight.wordsOf, CFSG.Sporadic.Schreier.Co3.Native.wordsArr, List.getElem_toArray,
      Array.getElem_ofFn]
    by_cases hi : i < k
    · rw [List.getElem_append_left (by simp; omega)]
      simp [hi]
    · rw [List.getElem_append_right (by simp; omega)]
      have hd : i - k < D.length := by
        simp [OmegaEight.wordsOf] at h1
        omega
      simp only [hi, if_false, List.length_replicate, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hd, Option.getD_some]

end CFSG.KC.O8

end
