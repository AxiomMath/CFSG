module

public import CFSG.Certificates.Kernel.Census.Sound
public import CFSG.Certificates.Kernel.Census.SiftSound
public import CFSG.Certificates.Kernel.Census.ExcSound
public import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.Census.SP

open CFSG.KC.Enum CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.Monster.B.Fischer

variable {n w : Nat}

theorem lt_of_canon {p : Nat} (hp : canon1 n w p = true) : p < 2 ^ (n * w) := by
  have h0 : p >>> (n * w) = 0 := Nat.eq_of_beq_eq_true hp
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
  · exact h0

theorem canon_of_lt {p : Nat} (hp : p < 2 ^ (n * w)) : canon1 n w p = true := by
  unfold canon1
  rw [Nat.beq_eq]
  change p >>> (n * w) = 0
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff]
  exact Or.inr hp

theorem at'_big {p k : Nat} (hp : canon1 n w p = true) (hk : n ≤ k) : at' w p k = 0 := by
  have hlt := lt_of_canon hp
  apply Nat.eq_of_testBit_eq
  intro j
  rw [at', CFSG.KS.PackFld.testBit_pgM, Nat.zero_testBit]
  have hle : n * w ≤ w * k + j := by
    have := Nat.mul_le_mul_right w hk
    rw [Nat.mul_comm k w] at this
    omega
  rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hle)),
    Bool.and_false]

theorem unpackP_size (p : Nat) : (unpackP n w p).size = n := by simp [unpackP]

theorem unpackP_get (p x : Nat) :
    (unpackP n w p)[x]! = if x < n then at' w p x else 0 := by
  split
  · next h =>
    rw [getElem!_pos _ _ (by rw [unpackP_size]; exact h)]
    unfold unpackP
    rw [Array.getElem_ofFn]
    rfl
  · next h =>
    rw [getElem!_neg _ _ (by rw [unpackP_size]; exact h)]
    rfl

theorem unpackP_get_canon {p : Nat} (hp : canon1 n w p = true) (x : Nat) :
    (unpackP n w p)[x]! = at' w p x := by
  rw [unpackP_get]
  split
  · rfl
  · next h => exact (at'_big hp (by omega)).symm

theorem eq_of_at' {p q : Nat} (hp : canon1 n w p = true) (hq : canon1 n w q = true)
    (h : ∀ i < n, at' w p i = at' w q i) : p = q := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < n * w
  · have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · rw [h0, Nat.mul_zero] at hb
        omega
      · exact h0
    have hi : b / w < n := by
      rw [Nat.div_lt_iff_lt_mul hw]
      exact hb
    have hd := Nat.div_add_mod b w
    have hm : b % w < w := Nat.mod_lt _ hw
    have e := congrArg (fun x => x.testBit (b % w)) (h _ hi)
    simp only [at'] at e
    rw [CFSG.KS.PackFld.testBit_pgM, CFSG.KS.PackFld.testBit_pgM, hd] at e
    simpa [hm] using e
  · have hle : n * w ≤ b := by omega
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt_of_canon hp) (Nat.pow_le_pow_right
      (by omega) hle)), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt_of_canon hq)
      (Nat.pow_le_pow_right (by omega) hle))]

theorem unpackP_inj {p q : Nat} (hp : canon1 n w p = true) (hq : canon1 n w q = true)
    (h : unpackP n w p = unpackP n w q) : p = q :=
  eq_of_at' hp hq fun i _ => by
    rw [← unpackP_get_canon hp, ← unpackP_get_canon hq, h]

theorem beq_unpack {p q : Nat} (hp : canon1 n w p = true) (hq : canon1 n w q = true) :
    (unpackP n w p == unpackP n w q) = Nat.beq p q := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, Nat.beq_eq]
  exact ⟨unpackP_inj hp hq, fun h => h ▸ rfl⟩

theorem eqA_unpack {p q : Nat} (hp : canon1 n w p = true) (hq : canon1 n w q = true) :
    eqA n (unpackP n w p) (unpackP n w q) = Nat.beq p q := by
  apply Bool.eq_iff_iff.mpr
  rw [eqA, allLt_iff, Nat.beq_eq]
  constructor
  · intro h
    refine eq_of_at' hp hq fun i hi => ?_
    have := h i hi
    rwa [beq_iff_eq, unpackP_get_canon hp, unpackP_get_canon hq] at this
  · rintro rfl i _
    exact beq_self_eq_true _

theorem unpackP_pc' {p q : Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hp : canon1 n w p = true) :
    unpackP n w (pc n w p q) = compA n (unpackP n w p) (unpackP n w q) :=
  unpackP_pc hn hw hp

theorem canon_pc {p q : Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) : canon1 n w (pc n w p q) = true :=
  canon1_pc hn hw

theorem keyA_unpack {p : Nat} (hp : canon1 n w p = true) (ps : List Nat) :
    keyA n ps (unpackP n w p) = pkey n w ps p := by
  unfold keyA pkey
  congr 1
  exact List.map_congr_left fun q _ => unpackP_get_canon hp q

open CFSG.KS.PackFld in
theorem fld_pmkT (n w : Nat) (f : Nat → Nat) (hf : ∀ x < n, f x < 2 ^ w) : ∀ d lo,
    Fld w (pmkT n w f d lo)
      (fun i => if i < 2 ^ d then (if lo + i < n then f (lo + i) else 0) else 0)
  | 0, lo => by
    have hG : ∀ z, (fun x => if x < n then f x else 0) z < 2 ^ w := by
      intro z
      by_cases hz : z < n
      · simp only [hz, ↓reduceIte]
        exact hf z hz
      · simp only [hz, ↓reduceIte]
        exact Nat.two_pow_pos w
    have e : pmkT n w f 0 lo = (fun x => if x < n then f x else 0) lo := by
      change Bool.rec (motive := fun _ => Nat) (nat_lit 0) (f lo) (Nat.blt lo n) = _
      cases h : Nat.blt lo n
      · have hl : ¬ lo < n := fun hh => by
          have := Nat.blt_eq.mpr hh
          rw [h] at this
          exact Bool.false_ne_true this
        exact (iteF hl).symm
      · exact (iteT (Nat.blt_eq.mp h)).symm
    rw [e]
    exact fld_single (F := fun x => if x < n then f x else 0) (hG lo)
  | d + 1, lo => by
    have e : pmkT n w f (d + 1) lo = Nat.lor (pmkT n w f d lo)
        (Nat.shiftLeft (pmkT n w f d (Nat.add lo (Nat.shiftLeft (nat_lit 1) d)))
          (Nat.mul w (Nat.shiftLeft (nat_lit 1) d))) := rfl
    rw [e, shl_eq 1 d, Nat.one_mul]
    refine fld_congr (fld_double (F := fun x => if x < n then f x else 0)
      (x := lo) (y := Nat.add lo (2 ^ d)) (c := 2 ^ d)
      (fld_pmkT n w f hf d lo) (fld_pmkT n w f hf d _) rfl) ?_
    intro i
    rw [Nat.pow_succ, Nat.mul_two]

noncomputable def clogR (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun _ ih => nIf(Nat.blt (Nat.shiftLeft (nat_lit 1) ih) n, Nat.succ ih, ih))

theorem clogR_spec (n : Nat) : ∀ k, clogR n k = k ∨ n ≤ 2 ^ clogR n k
  | 0 => Or.inl rfl
  | k + 1 => by
    have e : clogR n (k + 1) =
        nIf(Nat.blt (Nat.shiftLeft (nat_lit 1) (clogR n k)) n, Nat.succ (clogR n k), clogR n k) :=
      rfl
    have ih := clogR_spec n k
    rw [e]
    generalize clogR n k = c at ih ⊢
    cases h : Nat.blt (Nat.shiftLeft 1 c) n
    · right
      have hl : ¬ Nat.shiftLeft 1 c < n := fun hh => by
        have := Nat.blt_eq.mpr hh
        rw [h] at this
        exact Bool.false_ne_true this
      rw [CFSG.KS.PackFld.shl_eq, Nat.one_mul] at hl
      exact Nat.le_of_not_lt hl
    · have hl := Nat.blt_eq.mp h
      rw [CFSG.KS.PackFld.shl_eq, Nat.one_mul] at hl
      rcases ih with ih | ih
      · left
        exact congrArg Nat.succ ih
      · omega

theorem clog_spec' (n : Nat) : clog n = 24 ∨ n ≤ 2 ^ clog n := by
  have e : clog n = clogR n 24 := rfl
  rw [e]
  exact clogR_spec n 24

theorem fld_pid (hw : n ≤ 2 ^ w) :
    CFSG.KS.PackFld.Fld w (pid n w)
      (fun i => if i < 2 ^ clog n then (if i < n then i else 0) else 0) := by
  have h := fld_pmkT n w (fun i => i) (fun x hx => by omega) (clog n) 0
  have e : pid n w = pmkT n w (fun i => i) (clog n) 0 := by
    unfold pid pidn pmk
    rw [CFSG.KS.PackFld.strictN_eqP]
  rw [e]
  refine CFSG.KS.PackFld.fld_congr h fun i => ?_
  simp only [Nat.zero_add]

theorem pid_good (hw : n ≤ 2 ^ w) (hv : pvalid n w (pid n w) = true) :
    unpackP n w (pid n w) = idA n ∧ canon1 n w (pid n w) = true := by
  have hf := fld_pid (n := n) hw
  have hval : ∀ i, (if i < 2 ^ clog n then (if i < n then i else 0) else 0) < 2 ^ w := by
    intro i
    split
    · split
      · omega
      · exact Nat.two_pow_pos w
    · exact Nat.two_pow_pos w
  have hat : ∀ i, at' w (pid n w) i =
      if i < 2 ^ clog n then (if i < n then i else 0) else 0 :=
    fun i => CFSG.KS.PackFld.pg_of_fld hf (hval i)
  have hc : n ≤ 2 ^ clog n := by
    rcases clogR_spec n 24 with h | h
    · by_contra hlt
      have hlt' : 2 ^ 24 < n := by
        have e : clog n = clogR n 24 := rfl
        rw [e, h] at hlt
        omega
      obtain ⟨-, hinj⟩ := inj_of_pvalid hv
      have h0 := hat 0
      have h1 := hat (2 ^ 24)
      have e : clog n = clogR n 24 := rfl
      rw [e, h] at h0 h1
      simp only [Nat.two_pow_pos, ↓reduceIte, lt_irrefl] at h0 h1
      have := hinj 0 (by omega) (2 ^ 24) hlt' (by rw [h1, h0]; split <;> rfl)
      omega
    · exact h
  have hid : ∀ i < n, at' w (pid n w) i = i := fun i hi => by
    rw [hat i]
    simp only [show i < 2 ^ clog n by omega, hi, ↓reduceIte]
  refine ⟨?_, ?_⟩
  · apply Array.ext
    · simp [unpackP_size, idA]
    · intro i h1 _
      have hi : i < n := by simpa [unpackP_size] using h1
      have := unpackP_get (n := n) (w := w) (pid n w) i
      rw [getElem!_pos _ _ (by rw [unpackP_size]; exact hi)] at this
      simp only [hi, ↓reduceIte, hid i hi] at this
      rw [this]
      simp [idA]
  · rcases Nat.eq_zero_or_pos w with rfl | hw0
    · have hn1 : n ≤ 1 := by simpa using hw
      rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
      · decide +kernel
      · decide +kernel
    · unfold canon1
      rw [Nat.beq_eq]
      exact CFSG.KS.PackFld.shr_zero_of_fld hw0 hf fun i hi => by
        have : ¬ i < n := by omega
        simp [this]

theorem canon_pset {r j v : Nat} (hr : canon1 n w r = true) (hj : j < n) (hv : v < 2 ^ w) :
    canon1 n w (pset w r j v) = true := by
  rcases Nat.eq_zero_or_pos w with rfl | hw0
  · have hr0 : r = 0 := by
      have := lt_of_canon hr
      simp at this
      exact this
    have hv0 : v = 0 := by simpa using hv
    subst hr0 hv0
    have e : pset 0 0 j 0 = 0 := by simp [pset]
    rw [e]
    rfl
  · apply canon_of_lt
    have hlt := lt_of_canon hr
    apply Nat.lt_pow_two_of_testBit
    intro b hb
    have hd := Nat.div_add_mod b w
    have hm : b % w < w := Nat.mod_lt _ hw0
    have hi : n ≤ b / w := by
      rw [Nat.le_div_iff_mul_le hw0]
      omega
    rw [← hd, testBit_pset hv hm]
    have hne : ¬ b / w = j := by omega
    simp only [hne, ↓reduceIte]
    rw [hd]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hb))

theorem unpackP_pset {r j v : Nat} (hr : canon1 n w r = true) (hj : j < n) (hv : v < 2 ^ w) :
    unpackP n w (pset w r j v) = (unpackP n w r).set! j v := by
  apply Array.ext
  · simp [unpackP_size]
  · intro i h1 h2
    have hi : i < n := by simpa [unpackP_size] using h1
    have e1 := unpackP_get_canon (canon_pset hr hj hv) i
    rw [getElem!_pos (unpackP n w (pset w r j v)) i h1] at e1
    rw [e1, at'_pset hv]
    simp only [Array.set!_eq_setIfInBounds]
    by_cases hij : i = j
    · subst hij
      simp
    · have hji : j ≠ i := fun h => hij h.symm
      rw [Array.getElem_setIfInBounds_ne (by rw [unpackP_size]; exact hi) hji]
      simp only [hij, ↓reduceIte]
      have := unpackP_get_canon hr i
      rw [getElem!_pos _ _ (by rw [unpackP_size]; exact hi)] at this
      exact this.symm

theorem pinv_fold (hw : n ≤ 2 ^ w) {P : Nat} (hP : canon1 n w P = true) : ∀ k ≤ n,
    unpackP n w ((List.range k).foldl (fun r i =>
      strictN r fun r => nIf(Nat.blt (at' w P i) n, pset w r (at' w P i) i, r)) 0) =
      (List.range k).foldl (fun r i => r.set! (unpackP n w P)[i]! i) (Array.replicate n 0) ∧
    canon1 n w ((List.range k).foldl (fun r i =>
      strictN r fun r => nIf(Nat.blt (at' w P i) n, pset w r (at' w P i) i, r)) 0) = true := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, by simp [canon1]⟩
    apply Array.ext
    · simp [unpackP_size]
    · intro i h1 _
      have hi : i < n := by simpa [unpackP_size] using h1
      simp only [List.range_zero, List.foldl_nil, Array.getElem_replicate]
      have := unpackP_get (n := n) (w := w) 0 i
      rw [getElem!_pos (unpackP n w 0) i (by rw [unpackP_size]; exact hi)] at this
      rw [this]
      simp only [hi, ↓reduceIte]
      exact at'_big (n := 0) (by simp [canon1]) (Nat.zero_le _)
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil, CFSG.KS.PackFld.strictN_eqP]
    generalize ((List.range k).foldl (fun r i =>
      strictN r fun r => nIf(Nat.blt (at' w P i) n, pset w r (at' w P i) i, r)) 0) = R at ih1 ih2
    rw [← ih1, unpackP_get_canon hP]
    cases hb : Nat.blt (at' w P k) n
    · have hge : n ≤ at' w P k := Nat.not_lt.1 fun h => by
        rw [Nat.blt_eq.mpr h] at hb
        cases hb
      refine ⟨?_, ih2⟩
      change unpackP n w R = (unpackP n w R).set! (at' w P k) k
      have hns : ¬ at' w P k < (unpackP n w R).size := by
        rw [unpackP_size]
        omega
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hns]
    · have hlt := Nat.blt_eq.mp hb
      exact ⟨unpackP_pset ih2 hlt (by omega), canon_pset ih2 hlt (by omega)⟩

theorem unpackP_pinv (hw : n ≤ 2 ^ w) {P : Nat} (hP : canon1 n w P = true) :
    unpackP n w (pinv n w P) = invCand n (unpackP n w P) ∧ canon1 n w (pinv n w P) = true := by
  have h := pinv_fold hw hP n (Nat.le_refl n)
  rw [← invK_eq]
  exact h

theorem validA_unpack (hw : n ≤ 2 ^ w) {P : Nat} (hP : canon1 n w P = true) :
    validA n (unpackP n w P) = pvalid n w P := by
  obtain ⟨hi1, hi2⟩ := unpackP_pinv hw hP
  apply Bool.eq_iff_iff.mpr
  rw [validA, isInvA, allLt_iff, pvalid, CFSG.KS.PackFld.strictB_eqP, List.all_eq_true, ← hi1]
  refine forall_congr' fun i => ?_
  rw [List.mem_range]
  refine imp_congr_right fun hi => ?_
  rw [unpackP_get_canon hP, unpackP_get_canon hi2]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.blt_eq, Nat.beq_eq]

theorem map_get {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {k : Nat}
    (hk : k < a.size) : (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by simpa using hk), getElem!_pos a k hk, Array.getElem_map]

theorem map_get' {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (hf : f default = default)
    (a : Array α) (k : Nat) : (a.map f)[k]! = f a[k]! := by
  by_cases hk : k < a.size
  · exact map_get f a hk
  · rw [getElem!_neg (a.map f) k (by simpa using hk), getElem!_neg a k hk, hf]

structure Good (n w : Nat) : Prop where
  hn : n < 2 ^ 32
  hw : n ≤ 2 ^ w
  pid_eq : unpackP n w (pid n w) = idA n
  pid_canon : canon1 n w (pid n w) = true

variable (G : Good n w)
include G

theorem pc_eq {p q : Nat} (hp : canon1 n w p = true) :
    unpackP n w (pc n w p q) = compA n (unpackP n w p) (unpackP n w q) :=
  unpackP_pc G.hn G.hw hp

theorem pc_canon (p q : Nat) : canon1 n w (pc n w p q) = true := canon1_pc G.hn G.hw

theorem pprod_eq : ∀ {l : List Nat}, (∀ x ∈ l, canon1 n w x = true) →
    unpackP n w (pprod n w l) = prodA n (l.map (unpackP n w)) ∧
      canon1 n w (pprod n w l) = true
  | [], _ => ⟨G.pid_eq, G.pid_canon⟩
  | a :: l, h => by
    have ih := pprod_eq (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨?_, pc_canon G _ _⟩
    change unpackP n w (pc n w a (pprod n w l)) = compA n (unpackP n w a) (prodA n _)
    rw [pc_eq G (h a List.mem_cons_self), ih.1]

theorem ppow_eq {p : Nat} (hp : canon1 n w p = true) (m : Nat) :
    unpackP n w (ppow n w p m) = powA n (unpackP n w p) m ∧ canon1 n w (ppow n w p m) = true := by
  have h := pprod_eq G (l := List.replicate m p) fun x hx => (List.eq_of_mem_replicate hx) ▸ hp
  unfold ppow powA
  rw [List.map_replicate] at h
  exact h

theorem pmask_eq {basis : Array Nat} (hb : ∀ x ∈ basis.toList, canon1 n w x = true) (m : Nat) :
    unpackP n w (pmask n w basis m) = maskA n (basis.map (unpackP n w)) m ∧
      canon1 n w (pmask n w basis m) = true := by
  have hb' : ∀ k < basis.size, canon1 n w basis[k]! = true := fun k hk => by
    rw [getElem!_pos basis k hk]
    exact hb _ (Array.getElem_mem_toList hk)
  have h := pprod_eq G (l := ((List.range basis.size).filter fun k => m.testBit k).map
    fun k => basis[k]!) fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact hb' k (List.mem_range.1 (List.mem_filter.1 hk).1)
  unfold pmask maskA
  refine ⟨?_, h.2⟩
  rw [h.1, List.map_map, Array.size_map]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < basis.size := List.mem_range.1 (List.mem_filter.1 hk).1
  exact (map_get (unpackP n w) basis hk').symm

theorem commA_eq {p q : Nat} (hp : canon1 n w p = true) (hq : canon1 n w q = true) :
    commA n (unpackP n w p) (unpackP n w q) = pcommA n w p q := by
  rw [commA, pcommA, ← pc_eq G hp, ← pc_eq G hq, eqA_unpack (pc_canon G _ _) (pc_canon G _ _)]

theorem pinv_eq {p : Nat} (hp : canon1 n w p = true) :
    unpackP n w (pinv n w p) = invCand n (unpackP n w p) ∧ canon1 n w (pinv n w p) = true :=
  unpackP_pinv G.hw hp

theorem pcomm_eq {p q : Nat} (hp : canon1 n w p = true) (hq : canon1 n w q = true) :
    unpackP n w (pcomm n w p q) = commutatorA n (unpackP n w p) (unpackP n w q) := by
  obtain ⟨e1, c1⟩ := pinv_eq G hp
  obtain ⟨e2, -⟩ := pinv_eq G hq
  rw [pcomm, commutatorA, pc_eq G (pc_canon G _ _), pc_eq G hp, pc_eq G c1, e1, e2]

theorem pconj_eq {p q : Nat} (hp : canon1 n w p = true) (hq : canon1 n w q = true) :
    unpackP n w (pconj n w p q) = conjA n (unpackP n w p) (unpackP n w q) := by
  obtain ⟨e1, -⟩ := pinv_eq G hp
  rw [pconj, conjA, pc_eq G hp, pc_eq G hq, e1]

theorem eqA_pid {p : Nat} (hp : canon1 n w p = true) :
    eqA n (unpackP n w p) (idA n) = Nat.beq p (pid n w) := by
  rw [← G.pid_eq, eqA_unpack hp G.pid_canon]

omit G in
theorem getD_toList {α : Type} [Inhabited α] (a : Array α) (j : Nat) :
    a.toList.getD j default = a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos a j hj, List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  · rw [getElem!_neg a j hj, List.getD_eq_default _ _ (by simpa using hj)]

omit G in
theorem getD_toList_arr (a : Array (Array Nat)) (j : Nat) : a.toList.getD j #[] = a[j]! :=
  getD_toList a j

omit G in
theorem getD_toList_nat (a : Array Nat) (j : Nat) : a.toList.getD j 0 = a[j]! :=
  getD_toList a j

omit G in
theorem ppointsOK_spec {gs : Array Nat} {c : ArrCertP} :
    ∀ (i : Nat) (us : List Nat) (es : List (Array Nat)) (ps ls : List Nat),
      ppointsOK n w gs c i us es ps ls = true → ∀ j (hj : j < us.length),
        ppointAt n w gs c (i + j) us[j] (es.getD j #[]) (ps.getD j 0) (ls.getD j 0) = true
  | _, [], _, _, _, _ => fun j hj => absurd hj (by simp)
  | i, u :: us, es, ps, ls, h => by
    simp only [ppointsOK, Bool.and_eq_true] at h
    intro j hj
    cases j with
    | zero =>
      have h1 := h.1
      cases es <;> cases ps <;> cases ls <;> simpa using h1
    | succ j =>
      have := ppointsOK_spec (i + 1) us es.tail ps.tail ls.tail h.2 j (by simpa using hj)
      have e1 : es.tail.getD j #[] = es.getD (j + 1) #[] := by cases es <;> simp
      have e2 : ∀ l : List Nat, l.tail.getD j 0 = l.getD (j + 1) 0 := fun l => by cases l <;> simp
      rw [e1, e2, e2, show i + 1 + j = i + (j + 1) by omega] at this
      simpa using this

omit G in
theorem asc_eq : ∀ l : List Nat, asc l = keysAsc l
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    have e : Nat.blt a b = decide (a < b) := by
      apply Bool.eq_iff_iff.mpr
      rw [Nat.blt_eq, decide_eq_true_eq]
    rw [asc, keysAsc, asc_eq (b :: l), e]

omit G in
theorem getPts {c : ArrCertP} {x : Nat} (hx : x < c.pts.size) :
    (c.toMain n w).pts[x]! = unpackP n w c.pts[x]! :=
  map_get _ _ hx

theorem enumOKK_of_penumOK {gs : Array Nat} {ps : List Nat} {c : ArrCertP}
    (hg : ∀ x ∈ gs.toList, canon1 n w x = true) (hc : ∀ x ∈ c.pts.toList, canon1 n w x = true)
    (h : penumOK n w gs ps c = true) : enumOKK n (gs.map (unpackP n w)) ps (c.toMain n w) = true := by
  have hg' : ∀ k < gs.size, canon1 n w gs[k]! = true := fun k hk => by
    rw [getElem!_pos gs k hk]
    exact hg _ (Array.getElem_mem_toList hk)
  have hc' : ∀ k < c.pts.size, canon1 n w c.pts[k]! = true := fun k hk => by
    rw [getElem!_pos c.pts k hk]
    exact hc _ (Array.getElem_mem_toList hk)
  unfold penumOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hv, ⟨⟨h0, hid⟩, hpts⟩, hasc⟩ := h
  unfold enumOKK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, allLt_iff,
    Array.size_map, and_assoc]
  refine ⟨fun k hk => ?_, ?_, ?_, fun i hi => ?_, ?_⟩
  · rw [validK_eq, map_get _ _ hk, validA_unpack G.hw (hg' k hk)]
    exact hv k hk
  · simpa [ArrCertP.toMain] using h0
  · rw [getPts h0, hid, G.pid_eq]
    exact beq_self_eq_true _
  · have hi' : i < c.pts.size := by simpa [ArrCertP.toMain] using hi
    have hp := ppointsOK_spec 0 c.pts.toList c.edges.toList c.par.toList c.lab.toList hpts i
      (by simpa using hi')
    rw [getD_toList_arr, getD_toList_nat, getD_toList_nat, Nat.zero_add] at hp
    have hu : c.pts.toList[i] = c.pts[i]! := by
      rw [getElem!_pos c.pts i hi']
      simp
    rw [hu] at hp
    unfold ppointAt at hp
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_range, Nat.blt_eq,
      Nat.beq_eq] at hp
    obtain ⟨⟨⟨hpv, hes⟩, hed⟩, hpar⟩ := hp
    unfold arrPointOK
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq, beq_iff_eq]
    have he : (c.toMain n w).edges = c.edges := rfl
    have hpa : (c.toMain n w).par = c.par := rfl
    have hla : (c.toMain n w).lab = c.lab := rfl
    have hsz : (c.toMain n w).pts.size = c.pts.size := by simp [ArrCertP.toMain]
    rw [he, hpa, hla, hsz]
    refine ⟨⟨⟨?_, hes⟩, fun k hk => ⟨(hed k hk).1, ?_⟩⟩, ?_⟩
    · rw [validK_eq, getPts hi', validA_unpack G.hw (hc' i hi')]
      exact hpv
    · have hk1 := (hed k hk).1
      rw [getPts hk1, getPts hi', leftA, map_get _ _ hk, ← pc_eq G (hg' k hk)]
      exact congrArg (unpackP n w) (hed k hk).2
    · rcases hpar with h0 | ⟨⟨hpi, hli⟩, hpe⟩
      · exact Or.inl h0
      · refine Or.inr ⟨⟨hpi, hli⟩, ?_⟩
        rw [getPts hi', getPts (by omega), leftA, map_get _ _ hli, ← pc_eq G (hg' _ hli)]
        exact congrArg (unpackP n w) hpe
  · have hpm : (c.toMain n w).pts = c.pts.map (unpackP n w) := rfl
    rw [← asc_eq, hpm, Array.toList_map, List.map_map]
    have e : List.map (keyA n ps ∘ unpackP n w) c.pts.toList = c.pts.toList.map (pkey n w ps) :=
      List.map_congr_left fun x hx => keyA_unpack (hc x hx) ps
    rw [e]
    exact hasc

omit G in
theorem inX_eq {inX : Array Nat → Bool} {inXP : Nat → Bool}
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    {P : Nat} (hP : canon1 n w P = true) (hv : pvalid n w P = true) (h : inXP P = true) :
    inX (unpackP n w P) = true := by
  rw [← hin P hP hv]
  exact h

theorem gval_eq {f : GFacP} (hf : canon1 n w f.c₁ = true ∧ canon1 n w f.c₂ = true) :
    unpackP n w (GFacP.val n w f) = GFac.val n (GFacP.toMain n w f) :=
  pcomm_eq G hf.1 hf.2

theorem gamma_eq {l : List GFacP} (hl : canonG n w l = true) :
    unpackP n w (pgamma n w l) = gammaA n (l.map (GFacP.toMain n w)) ∧
      canon1 n w (pgamma n w l) = true := by
  have hl' : ∀ f ∈ l, canon1 n w f.c₁ = true ∧ canon1 n w f.c₂ = true := fun f hf => by
    have := List.all_eq_true.1 hl f hf
    simpa only [Bool.and_eq_true] using this
  have h := pprod_eq G (l := l.map (GFacP.val n w)) fun x hx => by
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hx
    exact pc_canon G _ _
  refine ⟨?_, h.2⟩
  rw [pgamma, h.1, gammaA, List.map_map, List.map_map]
  exact congrArg _ (List.map_congr_left fun f hf => gval_eq G (hl' f hf))

theorem gok_of {inX : Array Nat → Bool} {inXP : Nat → Bool}
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    {basis : Array Nat} (hb : ∀ x ∈ basis.toList, canon1 n w x = true) {f : GFacP}
    (hf : canon1 n w f.c₁ = true ∧ canon1 n w f.c₂ = true)
    (h : GFacP.ok n w inXP basis f = true) :
    GFac.okK n inX (basis.map (unpackP n w)) (GFacP.toMain n w f) = true := by
  obtain ⟨hm, hmc⟩ := pmask_eq G hb f.t
  unfold GFacP.ok at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  unfold GFac.okK
  simp only [GFacP.toMain, Bool.and_eq_true, Bool.not_eq_true']
  rw [← hm, eqA_pid G hmc, validK_eq, validA_unpack G.hw hf.1, validA_unpack G.hw hf.2,
    commA_eq G hf.1 hmc, commA_eq G hf.2 hmc]
  exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, inX_eq hin hf.1 h2 h4⟩, inX_eq hin hf.2 h3 h5⟩, h6⟩, h7⟩

theorem nval_eq {basis : Array Nat} (hb : ∀ x ∈ basis.toList, canon1 n w x = true) {f : NFacP}
    (hf : canonG n w f.γ = true) :
    unpackP n w (NFacP.val n w basis f) =
      NFac.val n (basis.map (unpackP n w)) (NFacP.toMain n w f) := by
  obtain ⟨hm, hmc⟩ := pmask_eq G hb f.e
  obtain ⟨hg, hgc⟩ := gamma_eq G hf
  rw [NFacP.val, pcomm_eq G hmc hgc, hm, hg]
  rfl

theorem nok_of {inX : Array Nat → Bool} {inXP : Nat → Bool}
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    {basis : Array Nat} (hb : ∀ x ∈ basis.toList, canon1 n w x = true) {f : NFacP}
    (hf : canonG n w f.γ = true) (h : NFacP.ok n w inXP basis f = true) :
    NFac.okK n inX (basis.map (unpackP n w)) (NFacP.toMain n w f) = true := by
  obtain ⟨hm, hmc⟩ := pmask_eq G hb f.e
  obtain ⟨hg, hgc⟩ := gamma_eq G hf
  have hl' : ∀ g ∈ f.γ, canon1 n w g.c₁ = true ∧ canon1 n w g.c₂ = true := fun g hg => by
    have := List.all_eq_true.1 hf g hg
    simpa only [Bool.and_eq_true] using this
  unfold NFacP.ok at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold NFac.okK
  simp only [NFacP.toMain, Bool.and_eq_true, List.all_map]
  rw [← hm, ← hg, validK_eq, validA_unpack G.hw hmc, validA_unpack G.hw hgc]
  refine ⟨⟨List.all_eq_true.2 fun g hg => ?_, h2⟩, h3⟩
  exact gok_of G hin hb (hl' g hg) (List.all_eq_true.1 h1 g hg)

theorem nA_eq {basis : Array Nat} (hb : ∀ x ∈ basis.toList, canon1 n w x = true)
    {l : List NFacP} (hl : ∀ f ∈ l, canonG n w f.γ = true) :
    unpackP n w (pnA n w basis l) = nA n (basis.map (unpackP n w)) (l.map (NFacP.toMain n w)) ∧
      canon1 n w (pnA n w basis l) = true := by
  have h := pprod_eq G (l := l.map (NFacP.val n w basis)) fun x hx => by
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hx
    exact pc_canon G _ _
  refine ⟨?_, h.2⟩
  rw [pnA, h.1, nA, List.map_map, List.map_map]
  exact congrArg _ (List.map_congr_left fun f hf => nval_eq G hb (hl f hf))

theorem cval_eq {f : CFacP} (hf : canon1 n w f.x₁ = true ∧ canon1 n w f.x₂ = true) :
    unpackP n w (CFacP.val n w f) = CFac.val n (CFacP.toMain n w f) :=
  pcomm_eq G hf.1 hf.2

theorem cok_of {inX : Array Nat → Bool} {inXP : Nat → Bool}
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    {basis : Array Nat} (hb : ∀ x ∈ basis.toList, canon1 n w x = true) {f : CFacP}
    (hf : canon1 n w f.x₁ = true ∧ canon1 n w f.x₂ = true)
    (h : CFacP.ok n w inXP basis f = true) :
    CFac.okK n inX (basis.map (unpackP n w)) (CFacP.toMain n w f) = true := by
  have hb' : ∀ k < basis.size, canon1 n w basis[k]! = true := fun k hk => by
    rw [getElem!_pos basis k hk]
    exact hb _ (Array.getElem_mem_toList hk)
  unfold CFacP.ok at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  unfold CFac.okK
  simp only [CFacP.toMain, Bool.and_eq_true, allLt_iff, Array.size_map]
  rw [validK_eq, validA_unpack G.hw hf.1, validA_unpack G.hw hf.2]
  refine ⟨⟨⟨⟨h1, h2⟩, inX_eq hin hf.1 h1 h3⟩, inX_eq hin hf.2 h2 h4⟩, fun k hk => ?_⟩
  rw [map_get _ _ hk, commA_eq G hf.1 (hb' k hk), commA_eq G hf.2 (hb' k hk)]
  exact h5 k hk

theorem cprod_eq {l : List CFacP}
    (hl : ∀ f ∈ l, canon1 n w f.x₁ = true ∧ canon1 n w f.x₂ = true) :
    unpackP n w (pprod n w (l.map (CFacP.val n w))) =
        prodA n ((l.map (CFacP.toMain n w)).map (CFac.val n)) ∧
      canon1 n w (pprod n w (l.map (CFacP.val n w))) = true := by
  have h := pprod_eq G (l := l.map (CFacP.val n w)) fun x hx => by
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hx
    exact pc_canon G _ _
  refine ⟨?_, h.2⟩
  rw [h.1, List.map_map, List.map_map]
  exact congrArg _ (List.map_congr_left fun f hf => cval_eq G (hl f hf))

omit G in
theorem memA_eq {c : ArrCertP} (hc : ∀ x ∈ c.pts.toList, canon1 n w x = true) {a : Nat}
    (ha : canon1 n w a = true) : memA n (c.toMain n w) (unpackP n w a) = pmem c a := by
  have hpm : (c.toMain n w).pts = c.pts.map (unpackP n w) := rfl
  rw [memA, pmem, hpm, Array.toList_map, List.any_map]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Function.comp_apply]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by rwa [eqA_unpack ha (hc x hx)] at h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by rwa [eqA_unpack ha (hc x hx)]⟩

omit G in
theorem countA_eq (f : Array Nat → Bool) (c : ArrCert) :
    countA f c = (c.pts.toList.filter f).length := by
  unfold countA
  have e1 : c.pts.toList = (List.range c.pts.size).map fun i => c.pts[i]! := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      rw [getElem!_pos c.pts i (by simpa using h1)]
  rw [e1, List.filter_map, List.length_map, ← List.toFinset_card_of_nodup
    (List.nodup_range.filter _), List.toFinset_filter, List.toFinset_range]
  rfl

omit G in
theorem countA_of {outX : Array Nat → Bool} {outXP : Nat → Bool}
    (hout : ∀ P, canon1 n w P = true → pvalid n w P = true → outXP P = outX (unpackP n w P))
    {c : ArrCertP} (hc : ∀ x ∈ c.pts.toList, canon1 n w x = true ∧ pvalid n w x = true) :
    countA outX (c.toMain n w) = pcount outXP c := by
  have hpm : (c.toMain n w).pts = c.pts.map (unpackP n w) := rfl
  rw [countA_eq, hpm, Array.toList_map, List.filter_map, List.length_map, pcount]
  congr 1
  exact List.filter_congr fun x hx => (hout x (hc x hx).1 (hc x hx).2).symm

omit G in
theorem toMain_default : (default : ArrCertP).toMain n w = default := by
  have e : (default : ArrCertP) = ⟨#[], #[], #[], #[]⟩ := rfl
  rw [e]
  simp only [ArrCertP.toMain, Array.map_empty]
  rfl

omit G in
theorem arr_map_eq {l : List Nat} {L : List (Array Nat)}
    (h : L = l.map (unpackP n w)) : L.toArray = l.toArray.map (unpackP n w) := by
  rw [h, List.map_toArray]

omit G in
theorem canon_arr {l : List Nat} (h : ∀ x ∈ l, canon1 n w x = true) :
    ∀ x ∈ l.toArray.toList, canon1 n w x = true := by
  simpa using h

omit G in
theorem canon_get {a : Array Nat} (h : ∀ x ∈ a.toList, canon1 n w x = true) :
    ∀ k < a.size, canon1 n w a[k]! = true := fun k hk => by
  rw [getElem!_pos a k hk]
  exact h _ (Array.getElem_mem_toList hk)

theorem witOKW_of {ps : List Nat} {inX outX : Array Nat → Bool} {inXP outXP : Nat → Bool}
    {allowPW allowInX allowU : Bool}
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    (hout : ∀ P, canon1 n w P = true → pvalid n w P = true → outXP P = outX (unpackP n w P))
    {basis : Array Nat} (hb : ∀ x ∈ basis.toList, canon1 n w x = true)
    (hbv : ∀ k < basis.size, pvalid n w basis[k]! = true)
    {cE : ArrCertP} (hE : ∀ x ∈ cE.pts.toList, canon1 n w x = true ∧ pvalid n w x = true)
    {cs : Array ArrCertP} (hcs : ∀ j : Nat, ∀ x ∈ (cs[j]!).pts.toList, canon1 n w x = true)
    {wt : WitP} (hW : canonW n w wt = true)
    (h : pwitOK n w ps inXP outXP allowPW allowInX allowU basis cE cs wt = true) :
    witOKW n ps inX outX allowPW allowInX allowU (basis.map (unpackP n w)) (cE.toMain n w)
      (cs.map (ArrCertP.toMain n w)) (wt.toMain n w) = true := by
  have hb' := canon_get hb
  have hcs0 : ∀ j : Nat, (cs.map (ArrCertP.toMain n w))[j]! = (cs[j]!).toMain n w :=
    fun j => map_get' _ toMain_default cs j
  have hcs' : ∀ j : Nat, ∀ x < (cs[j]!).pts.size, canon1 n w (cs[j]!).pts[x]! = true :=
    fun j => canon_get (hcs j)
  have hsz : ∀ c : ArrCertP, (c.toMain n w).pts.size = c.pts.size := fun c => by
    simp [ArrCertP.toMain]
  cases wt with
  | order4 l m =>
    simp only [canonW] at hW
    have hl : ∀ f ∈ l, canonG n w f.γ = true := fun f hf => List.all_eq_true.1 hW f hf
    obtain ⟨hy, hyc⟩ := nA_eq G hb hl
    obtain ⟨hp, hpc⟩ := ppow_eq G hyc m
    obtain ⟨hp4, hp4c⟩ := ppow_eq G hpc 4
    simp only [pwitOK, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [WitP.toMain, witOKW, Bool.and_eq_true, Bool.not_eq_true', List.all_map]
    rw [← hy, ← hp, ← pc_eq G hpc, eqA_pid G (pc_canon G _ _), ← hp4, eqA_pid G hp4c]
    exact ⟨⟨List.all_eq_true.2 fun f hf => nok_of G hin hb (hl f hf) (List.all_eq_true.1 h1 f hf),
      h2⟩, h3⟩
  | twoGroup gens k =>
    simp only [canonW] at hW
    have hl : ∀ l ∈ gens, ∀ f ∈ l.1, canonG n w f.γ = true := fun l hl f hf =>
      List.all_eq_true.1 (List.all_eq_true.1 hW l hl) f hf
    simp only [pwitOK, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    simp only [WitP.toMain, witOKW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_map]
    have hgs : ((gens.map fun l => (l.1.map (NFacP.toMain n w), l.2)).map fun l =>
        powA n (nA n (basis.map (unpackP n w)) l.1) l.2).toArray =
        ((gens.map fun l => ppow n w (pnA n w basis l.1) l.2).toArray).map (unpackP n w) := by
      refine arr_map_eq ?_
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun l hlm => ?_
      obtain ⟨e1, c1⟩ := nA_eq G hb (hl l hlm)
      simp only [Function.comp_apply]
      rw [(ppow_eq G c1 l.2).1, e1]
    have hgc : ∀ x ∈ (gens.map fun l => ppow n w (pnA n w basis l.1) l.2).toArray.toList,
        canon1 n w x = true := canon_arr fun x hx => by
      obtain ⟨l, hlm, rfl⟩ := List.mem_map.1 hx
      exact (ppow_eq G (nA_eq G hb (hl l hlm)).2 l.2).2
    rw [hgs, hcs0, hsz, countA_of hout hE]
    refine ⟨⟨⟨List.all_eq_true.2 fun l hlm => ?_, enumOKK_of_penumOK G hgc (hcs 0) h2⟩, h3⟩, h4⟩
    simp only [Function.comp_apply, List.all_map]
    exact List.all_eq_true.2 fun f hf => nok_of G hin hb (hl l hlm f hf)
      (List.all_eq_true.1 (List.all_eq_true.1 h1 l hlm) f hf)
  | perfect gens comms x k conjs e g =>
    simp only [canonW] at hW
    have hl : ∀ l ∈ gens, canonG n w l.1 = true := fun l hl => List.all_eq_true.1 hW l hl
    simp only [pwitOK, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Bool.not_eq_true',
      List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hPW, h1⟩, hP⟩, hcm⟩, hQ⟩, hQs⟩, hx⟩, hxp⟩, hcj⟩, hR⟩, hRs⟩, hg⟩,
      hnc⟩ := h
    simp only [WitP.toMain, witOKW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      List.all_map, Bool.not_eq_true', List.all_eq_true]
    have hP0 := hcs' 0
    set cP := cs[0]!
    have hpt : ∀ j < cP.pts.size, (cP.toMain n w).pts[j]! = unpackP n w cP.pts[j]! :=
      fun j hj => getPts hj
    have hgs : ((gens.map fun l => (l.1.map (GFacP.toMain n w), l.2)).map fun l =>
        powA n (gammaA n l.1) l.2).toArray =
        ((gens.map fun l => ppow n w (pgamma n w l.1) l.2).toArray).map (unpackP n w) := by
      refine arr_map_eq ?_
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun l hlm => ?_
      obtain ⟨e1, c1⟩ := gamma_eq G (hl l hlm)
      simp only [Function.comp_apply]
      rw [(ppow_eq G c1 l.2).1, e1]
    have hgc : ∀ y ∈ (gens.map fun l => ppow n w (pgamma n w l.1) l.2).toArray.toList,
        canon1 n w y = true := canon_arr fun y hy => by
      obtain ⟨l, hlm, rfl⟩ := List.mem_map.1 hy
      exact (ppow_eq G (gamma_eq G (hl l hlm)).2 l.2).2
    have hqs : (comms.map fun ij => commutatorA n (cP.toMain n w).pts[ij.1]!
        (cP.toMain n w).pts[ij.2]!).toArray =
        (comms.map fun ij => pcomm n w cP.pts[ij.1]! cP.pts[ij.2]!).toArray.map (unpackP n w) := by
      refine arr_map_eq ?_
      rw [List.map_map]
      refine List.map_congr_left fun ij hij => ?_
      have hb1 := hcm ij hij
      simp only [Function.comp_apply]
      rw [hpt _ hb1.1, hpt _ hb1.2, pcomm_eq G (hP0 _ hb1.1) (hP0 _ hb1.2)]
    have hqc : ∀ y ∈ (comms.map fun ij => pcomm n w cP.pts[ij.1]! cP.pts[ij.2]!).toArray.toList,
        canon1 n w y = true := canon_arr fun y hy => by
      obtain ⟨ij, -, rfl⟩ := List.mem_map.1 hy
      exact pc_canon G _ _
    have hxa : (cP.toMain n w).pts[x]! = unpackP n w cP.pts[x]! := hpt x hx
    have hxc := hP0 x hx
    have hrs : (conjs.map fun p => conjA n (cP.toMain n w).pts[p]!
        (compA n (cP.toMain n w).pts[x]! (cP.toMain n w).pts[x]!)).toArray =
        (conjs.map fun p => pconj n w cP.pts[p]! (pc n w cP.pts[x]! cP.pts[x]!)).toArray.map
          (unpackP n w) := by
      refine arr_map_eq ?_
      rw [List.map_map]
      refine List.map_congr_left fun p hp => ?_
      have hp' := hcj p hp
      simp only [Function.comp_apply]
      rw [hpt _ hp', hxa, ← pc_eq G hxc, pconj_eq G (hP0 _ hp') (pc_canon G _ _)]
    have hrc : ∀ y ∈ (conjs.map fun p => pconj n w cP.pts[p]!
        (pc n w cP.pts[x]! cP.pts[x]!)).toArray.toList, canon1 n w y = true :=
      canon_arr fun y hy => by
        obtain ⟨p, -, rfl⟩ := List.mem_map.1 hy
        exact pc_canon G _ _
    obtain ⟨hm, hmc⟩ := pmask_eq G hb e
    rw [hgs, hcs0, hqs, hcs0, hrs, hcs0, hsz, hsz, hsz, hxa, hpt g hg, ← hm,
      commA_eq G hmc (hP0 g hg), ← (ppow_eq G hxc (2 ^ k)).1,
      eqA_pid G (ppow_eq G hxc (2 ^ k)).2]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hPW, fun l hlm => ?_⟩, enumOKK_of_penumOK G hgc (hcs 0) hP⟩,
      fun ij hij => hcm ij hij⟩, enumOKK_of_penumOK G hqc (hcs 1) hQ⟩, hQs⟩, hx⟩,
      Nat.beq_eq.mpr hxp⟩, hcj⟩, enumOKK_of_penumOK G hrc (hcs 2) hR⟩, hRs⟩, hg⟩, hnc⟩
    simp only [Function.comp_apply, List.all_map, List.all_eq_true]
    exact fun f hf => gok_of G hin hb (by
      have := List.all_eq_true.1 (hl l hlm) f hf
      simpa only [Bool.and_eq_true] using this) (h1 l hlm f hf)
  | inX =>
    simp only [pwitOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
    simp only [WitP.toMain, witOKW, Bool.and_eq_true, allLt_iff, Array.size_map]
    refine ⟨h.1, fun k hk => ?_⟩
    rw [map_get _ _ hk]
    exact inX_eq hin (hb' k hk) (hbv k hk) (h.2 k hk)
  | small =>
    simp only [pwitOK, Nat.blt_eq] at h
    simp only [WitP.toMain, witOKW, decide_eq_true_eq, hsz]
    exact h
  | closing s t c kc v gens comms =>
    simp only [canonW, Bool.and_eq_true] at hW
    obtain ⟨hc, hW⟩ := hW
    have hl : ∀ l ∈ gens, ∀ f ∈ l.1, canon1 n w f.x₁ = true ∧ canon1 n w f.x₂ = true :=
      fun l hl f hf => by
        have := List.all_eq_true.1 (List.all_eq_true.1 hW l hl) f hf
        simpa only [Bool.and_eq_true] using this
    simp only [pwitOK, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Bool.not_eq_true',
      List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hU, hs1⟩, ht1⟩, hcv⟩, hcX⟩, hct⟩, hcpow⟩, hvv⟩, hvc⟩, h1⟩, hP⟩,
      hcm⟩, hQ⟩, hQs⟩, hsP⟩ := h
    simp only [WitP.toMain, witOKW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      List.all_map, Bool.not_eq_true', List.all_eq_true]
    have hP0 := hcs' 0
    set cP := cs[0]!
    have hpt : ∀ j < cP.pts.size, (cP.toMain n w).pts[j]! = unpackP n w cP.pts[j]! :=
      fun j hj => getPts hj
    have hgs : ((gens.map fun l => (l.1.map (CFacP.toMain n w), l.2)).map fun l =>
        powA n (prodA n (l.1.map (CFac.val n))) l.2).toArray =
        ((gens.map fun l => ppow n w (pprod n w (l.1.map (CFacP.val n w))) l.2).toArray).map
          (unpackP n w) := by
      refine arr_map_eq ?_
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun l hlm => ?_
      obtain ⟨e1, c1⟩ := cprod_eq G (hl l hlm)
      simp only [Function.comp_apply]
      rw [(ppow_eq G c1 l.2).1, e1]
    have hgc : ∀ y ∈ (gens.map fun l => ppow n w (pprod n w (l.1.map (CFacP.val n w)))
        l.2).toArray.toList, canon1 n w y = true := canon_arr fun y hy => by
      obtain ⟨l, hlm, rfl⟩ := List.mem_map.1 hy
      exact (ppow_eq G (cprod_eq G (hl l hlm)).2 l.2).2
    have hqs : (comms.map fun ij => commutatorA n (cP.toMain n w).pts[ij.1]!
        (cP.toMain n w).pts[ij.2]!).toArray =
        (comms.map fun ij => pcomm n w cP.pts[ij.1]! cP.pts[ij.2]!).toArray.map (unpackP n w) := by
      refine arr_map_eq ?_
      rw [List.map_map]
      refine List.map_congr_left fun ij hij => ?_
      have hb1 := hcm ij hij
      simp only [Function.comp_apply]
      rw [hpt _ hb1.1, hpt _ hb1.2, pcomm_eq G (hP0 _ hb1.1) (hP0 _ hb1.2)]
    have hqc : ∀ y ∈ (comms.map fun ij => pcomm n w cP.pts[ij.1]! cP.pts[ij.2]!).toArray.toList,
        canon1 n w y = true := canon_arr fun y hy => by
      obtain ⟨ij, -, rfl⟩ := List.mem_map.1 hy
      exact pc_canon G _ _
    obtain ⟨hms, hmsc⟩ := pmask_eq G hb s
    obtain ⟨hmt, hmtc⟩ := pmask_eq G hb t
    obtain ⟨hmv, hmvc⟩ := pmask_eq G hb v
    rw [hgs, hcs0, hqs, hcs0, hsz, hsz, ← hms, ← hmt, ← hmv, eqA_pid G hmsc, eqA_pid G hmtc,
      validK_eq, validA_unpack G.hw hc, commA_eq G hc hmtc, ← (ppow_eq G hc (2 ^ kc)).1,
      eqA_pid G (ppow_eq G hc (2 ^ kc)).2, validA_unpack G.hw hmvc, ← pcomm_eq G hmvc hc,
      eqA_unpack (p := pcomm n w (pmask n w basis v) c) (pc_canon G _ _) hmsc,
      memA_eq (hcs 0) hmsc]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hU, hs1⟩, ht1⟩, hcv⟩, inX_eq hin hc hcv hcX⟩, hct⟩,
      Nat.beq_eq.mpr hcpow⟩, hvv⟩, Nat.beq_eq.mpr hvc⟩, fun l hlm => ?_⟩,
      enumOKK_of_penumOK G hgc (hcs 0) hP⟩, fun ij hij => hcm ij hij⟩,
      enumOKK_of_penumOK G hqc (hcs 1) hQ⟩, hQs⟩, hsP⟩
    simp only [Function.comp_apply, List.all_map, List.all_eq_true]
    exact fun f hf => cok_of G hin hb (hl l hlm f hf) (h1 l hlm f hf)

theorem pmaskCert_toMain {basis : Array Nat} (hb : ∀ x ∈ basis.toList, canon1 n w x = true) :
    (pmaskCert n w basis).toMain n w = maskCert n (basis.map (unpackP n w)) := by
  unfold pmaskCert maskCert ArrCertP.toMain
  simp only [Array.size_map, List.map_toArray, List.map_map]
  congr 2
  exact List.map_congr_left fun m _ => (pmask_eq G hb m).1

theorem pmaskCert_canon {basis : Array Nat} (hb : ∀ x ∈ basis.toList, canon1 n w x = true) :
    ∀ x ∈ (pmaskCert n w basis).pts.toList, canon1 n w x = true := by
  intro x hx
  simp only [pmaskCert, List.toList_toArray, List.mem_map] at hx
  obtain ⟨m, -, rfl⟩ := hx
  exact (pmask_eq G hb m).2

omit G in
theorem walkAll_spec {f : Nat → Nat → Bool} : ∀ (us cs : List Nat), walkAll f us cs = true →
    ∀ p (hp : p < us.length), f us[p] (cs.getD p 0) = true
  | [], _, _ => fun p hp => absurd hp (by simp)
  | u :: us, c :: cs, h => by
    simp only [walkAll, Bool.and_eq_true] at h
    intro p hp
    cases p with
    | zero => simpa using h.1
    | succ p => simpa using walkAll_spec us cs h.2 p (by simpa using hp)
  | u :: us, [], h => by
    simp only [walkAll, Bool.and_eq_true] at h
    intro p hp
    cases p with
    | zero => simpa using h.1
    | succ p => simpa using walkAll_spec us [] h.2 p (by simpa using hp)

structure Canon (n w : Nat) (sG : Array Nat) (nodes : Array NodeP) (cS : ArrCertP)
    (wcs : Array (Array ArrCertP)) : Prop where
  sG : ∀ x ∈ sG.toList, canon1 n w x = true
  basis : ∀ i : Nat, ∀ x ∈ (nodes[i]!).basis.toList, canon1 n w x = true
  wit : ∀ i : Nat, canonW n w (nodes[i]!).wit = true
  cS : ∀ x ∈ cS.pts.toList, canon1 n w x = true
  wcs : ∀ i j : Nat, ∀ x ∈ ((wcs[i]!)[j]!).pts.toList, canon1 n w x = true

omit G in
theorem default_basis : (default : NodeP).basis = #[] := rfl

omit G in
theorem default_pts : (default : ArrCertP).pts = #[] := rfl

omit G in
theorem default_arr_get (j : Nat) : (default : Array ArrCertP)[j]! = default := by
  have e : (default : Array ArrCertP) = #[] := rfl
  rw [e, getElem!_neg _ _ (by simp)]

omit G in
theorem canon_of {sG : Array Nat} {nodes : Array NodeP} {cS : ArrCertP}
    {wcs : Array (Array ArrCertP)} (hc : canonP n w sG nodes cS wcs = true) :
    Canon n w sG nodes cS wcs := by
  unfold canonP at hc
  simp only [Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  refine ⟨h1, fun i => ?_, fun i => ?_, h3, fun i j => ?_⟩
  · by_cases hi : i < nodes.size
    · rw [getElem!_pos nodes i hi]
      exact (h2 _ (Array.getElem_mem_toList hi)).1
    · rw [getElem!_neg nodes i hi, default_basis]
      simp
  · by_cases hi : i < nodes.size
    · rw [getElem!_pos nodes i hi]
      exact (h2 _ (Array.getElem_mem_toList hi)).2
    · rw [getElem!_neg nodes i hi]
      rfl
  · by_cases hi : i < wcs.size
    · rw [getElem!_pos wcs i hi]
      have hcs := h4 _ (Array.getElem_mem_toList hi)
      by_cases hj : j < wcs[i].size
      · rw [getElem!_pos wcs[i] j hj]
        exact hcs _ (Array.getElem_mem_toList hj)
      · rw [getElem!_neg wcs[i] j hj, default_pts]
        simp
    · rw [getElem!_neg wcs i hi, default_arr_get, default_pts]
      simp

theorem cN_get {nodes : Array NodeP} (hb : ∀ i : Nat, ∀ x ∈ (nodes[i]!).basis.toList,
    canon1 n w x = true) (i : Nat) :
    ((nodes.map (NodeP.toMain n w)).map fun nd => maskCert n nd.basis)[i]! =
      ((pcN n w nodes)[i]!).toMain n w := by
  by_cases hi : i < nodes.size
  · rw [map_get _ _ (by simpa using hi), map_get _ _ hi, pcN, map_get _ _ hi,
      pmaskCert_toMain G (hb i)]
    rfl
  · rw [getElem!_neg _ _ (by simpa using hi), pcN, getElem!_neg _ _ (by simpa using hi),
      toMain_default]

theorem cN_canon {nodes : Array NodeP} (hb : ∀ i : Nat, ∀ x ∈ (nodes[i]!).basis.toList,
    canon1 n w x = true) (i : Nat) : ∀ x ∈ ((pcN n w nodes)[i]!).pts.toList, canon1 n w x = true := by
  by_cases hi : i < nodes.size
  · rw [pcN, map_get _ _ hi]
    exact pmaskCert_canon G (hb i)
  · rw [getElem!_neg _ _ (by simpa [pcN] using hi), default_pts]
    simp

omit G in
theorem isMono_toMain (wt : WitP) : (wt.toMain n w).isMono = wt.isMono := by
  cases wt <;> rfl

theorem childOK_of {nodes : Array NodeP} (C : ∀ i : Nat, ∀ x ∈ (nodes[i]!).basis.toList,
    canon1 n w x = true) {i : Nat} (hi : i < nodes.size) {u j : Nat} (hu : canon1 n w u = true)
    (h : pchildOK n w nodes (pcN n w nodes) i u j = true) :
    childOK n (nodes.map (NodeP.toMain n w))
      ((nodes.map (NodeP.toMain n w)).map fun nd => maskCert n nd.basis) i (unpackP n w u) j =
      true := by
  unfold pchildOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_range, Nat.blt_eq] at h
  obtain ⟨⟨⟨hj, h1⟩, h2⟩, h3⟩ := h
  unfold childOK
  simp only [Bool.and_eq_true, Bool.or_eq_true, allLt_iff, decide_eq_true_eq, Array.size_map]
  have hnj : (nodes.map (NodeP.toMain n w))[j]! = (nodes[j]!).toMain n w := map_get _ _ hj
  have hni : (nodes.map (NodeP.toMain n w))[i]! = (nodes[i]!).toMain n w := map_get _ _ hi
  have hbj : ((nodes[j]!).toMain n w).basis = (nodes[j]!).basis.map (unpackP n w) := rfl
  have hbi : ((nodes[i]!).toMain n w).basis = (nodes[i]!).basis.map (unpackP n w) := rfl
  rw [hnj, hni, hbj, hbi, cN_get G C, cN_get G C, memA_eq (cN_canon G C j) hu]
  simp only [Array.size_map]
  refine ⟨⟨⟨hj, fun k hk => ?_⟩, fun k hk => ?_⟩, h3⟩
  · have hk' := canon_get (C j) k hk
    rw [map_get _ _ hk, memA_eq (cN_canon G C i) hk', ← pc_eq G hu,
      memA_eq (cN_canon G C i) (pc_canon G _ _)]
    exact h1 k hk
  · rw [map_get _ _ hk, memA_eq (cN_canon G C j) (canon_get (C i) k hk)]
    exact h2 k hk

omit G in
theorem default_map (f : ArrCertP → ArrCert) : (default : Array ArrCertP).map f = default := by
  have e : (default : Array ArrCertP) = #[] := rfl
  rw [e, Array.map_empty]
  rfl

theorem nodeOKW_of {ps : List Nat} {inX outX : Array Nat → Bool} {inXP outXP : Nat → Bool}
    {allowPW allowInX allowU : Bool}
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    (hout : ∀ P, canon1 n w P = true → pvalid n w P = true → outXP P = outX (unpackP n w P))
    {sG : Array Nat} {nodes : Array NodeP} {cS : ArrCertP} {wcs : Array (Array ArrCertP)}
    (C : Canon n w sG nodes cS wcs) {i : Nat} (hi : i < nodes.size)
    (h : pnodeOK n w ps inXP outXP allowPW allowInX allowU cS nodes (pcN n w nodes) wcs i =
      true) :
    nodeOKW n ps inX outX allowPW allowInX allowU (cS.toMain n w) (nodes.map (NodeP.toMain n w))
      ((nodes.map (NodeP.toMain n w)).map fun nd => maskCert n nd.basis)
      (wcs.map fun cs => cs.map (ArrCertP.toMain n w)) i = true := by
  unfold pnodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hE, hW⟩, hch⟩ := h
  have hni : (nodes.map (NodeP.toMain n w))[i]! = (nodes[i]!).toMain n w := map_get _ _ hi
  have hbi : ((nodes[i]!).toMain n w).basis = (nodes[i]!).basis.map (unpackP n w) := rfl
  have hwi : ((nodes[i]!).toMain n w).wit = (nodes[i]!).wit.toMain n w := rfl
  have hci : ((nodes[i]!).toMain n w).children = (nodes[i]!).children := rfl
  have hwcs : (wcs.map fun cs => cs.map (ArrCertP.toMain n w))[i]! =
      (wcs[i]!).map (ArrCertP.toMain n w) := map_get' _ (default_map _) wcs i
  unfold nodeOKW
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  rw [hni, hbi, hwi, hci, cN_get G C.basis, hwcs, isMono_toMain]
  have hcN := cN_canon G C.basis i
  refine ⟨⟨enumOKK_of_penumOK G (C.basis i) hcN hE, witOKW_of G hin hout (C.basis i)
    (fun k hk => pvalid_of_penumOK hE hk)
    (fun x hx => ⟨hcN x hx, pvalid_pts_of_penumOK hE x hx⟩) (C.wcs i) (C.wit i) hW⟩, ?_⟩
  rcases hch with hm | hwk
  · exact Or.inl hm
  · right
    rw [allLt_iff]
    intro p hp
    have hp' : p < cS.pts.size := by simpa [ArrCertP.toMain] using hp
    have hf := walkAll_spec _ _ hwk p (by simpa using hp')
    rw [getD_toList_nat] at hf
    have hu : cS.pts.toList[p] = cS.pts[p]! := by
      rw [getElem!_pos cS.pts p hp']
      simp
    rw [hu] at hf
    have huc := canon_get C.cS p hp'
    have hcomm : (allLt ((nodes[i]!).basis.map (unpackP n w)).size fun k =>
        commA n (unpackP n w cS.pts[p]!) ((nodes[i]!).basis.map (unpackP n w))[k]!) =
        (List.range (nodes[i]!).basis.size).all fun k =>
          pcommA n w cS.pts[p]! (nodes[i]!).basis[k]! := by
      apply Bool.eq_iff_iff.mpr
      rw [allLt_iff, List.all_eq_true, Array.size_map]
      refine forall_congr' fun k => ?_
      rw [List.mem_range]
      refine imp_congr_right fun hk => ?_
      rw [map_get _ _ hk, commA_eq G huc (canon_get (C.basis i) k hk)]
    rw [getPts hp', ← pc_eq G huc, eqA_pid G (pc_canon G _ _), memA_eq hcN huc, hcomm]
    simp only [Bool.or_eq_true] at hf ⊢
    rcases hf with ((h1 | h1) | h1) | h1
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr h1))
    · exact Or.inl (Or.inr h1)
    · exact Or.inr (childOK_of G C.basis hi huc h1)

theorem rootOK_of {nodes : Array NodeP} (Cb : ∀ i : Nat, ∀ x ∈ (nodes[i]!).basis.toList,
    canon1 n w x = true) {u j : Nat} (hu : canon1 n w u = true)
    (h : prootOK n w nodes (pcN n w nodes) u j = true) :
    rootOK n (nodes.map (NodeP.toMain n w))
      ((nodes.map (NodeP.toMain n w)).map fun nd => maskCert n nd.basis) (unpackP n w u) j =
      true := by
  unfold prootOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Nat.blt_eq] at h
  unfold rootOK
  simp only [Bool.or_eq_true, Bool.and_eq_true, allLt_iff, decide_eq_true_eq]
  rw [← pc_eq G hu, eqA_pid G (pc_canon G _ _), eqA_pid G hu]
  rcases h with (h1 | h1) | ⟨⟨hj, h2⟩, h3⟩
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr h1)
  · right
    have hnj : (nodes.map (NodeP.toMain n w))[j]! = (nodes[j]!).toMain n w := map_get _ _ hj
    have hbj : ((nodes[j]!).toMain n w).basis = (nodes[j]!).basis.map (unpackP n w) := rfl
    rw [hnj, hbj, cN_get G Cb, memA_eq (cN_canon G Cb j) hu, Array.size_map, Array.size_map]
    refine ⟨⟨hj, fun k hk => ?_⟩, h3⟩
    have hk' := canon_get (Cb j) k hk
    rw [map_get _ _ hk, eqA_unpack hk' hu, eqA_pid G hk']
    simpa only [Bool.or_eq_true] using h2 k hk

end CFSG.KC.Census.SP

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native

theorem pcensus_sound_proved {n w : Nat} {ps : List Nat} {inX outX : Array Nat → Bool}
    {inXP outXP : Nat → Bool} {allowPW allowInX allowU : Bool} {sG roots : Array Nat}
    {nodes : Array NodeP} {cS : ArrCertP} {wcs : Array (Array ArrCertP)}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonP n w sG nodes cS wcs = true)
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    (hout : ∀ P, canon1 n w P = true → pvalid n w P = true → outXP P = outX (unpackP n w P))
    (hS : penumOK n w sG ps cS = true)
    (hR : ((List.range cS.pts.size).all fun p =>
      prootOK n w nodes (pcN n w nodes) cS.pts[p]! roots[p]!) = true)
    (hN : ∀ i < nodes.size,
      pnodeOK n w ps inXP outXP allowPW allowInX allowU cS nodes (pcN n w nodes) wcs i = true) :
    censusOKW n ps inX outX allowPW allowInX allowU (sG.map (unpackP n w)) roots
      (nodes.map (NodeP.toMain n w)) (cS.toMain n w)
      (wcs.map fun cs => cs.map (ArrCertP.toMain n w)) = true := by
  have C := SP.canon_of hc
  have hS' := hS
  unfold penumOK at hS'
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hS'
  obtain ⟨-, ⟨⟨h0, hid⟩, -⟩, -⟩ := hS'
  have hv0 := pvalid_pts_of_penumOK hS cS.pts[0]! (by
    rw [getElem!_pos cS.pts 0 h0]
    exact Array.getElem_mem_toList h0)
  rw [hid] at hv0
  obtain ⟨e1, e2⟩ := SP.pid_good hw hv0
  have G : SP.Good n w := ⟨hn, hw, e1, e2⟩
  unfold censusOKW
  simp only [Bool.and_eq_true, allLt_iff]
  refine ⟨⟨SP.enumOKK_of_penumOK G C.sG C.cS hS, fun p hp => ?_⟩, fun i hi => ?_⟩
  · have hp' : p < cS.pts.size := by simpa [ArrCertP.toMain] using hp
    rw [SP.getPts hp']
    exact SP.rootOK_of G C.basis (SP.canon_get C.cS p hp')
      (List.all_eq_true.1 hR p (List.mem_range.2 hp'))
  · have hi' : i < nodes.size := by simpa using hi
    exact SP.nodeOKW_of G hin hout C hi' (hN i hi')

end CFSG.KC.Census

end
