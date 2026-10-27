module

public import Certificates.Data.Kernel.SporSch.LyGLQ
public import CFSG.Certificates.Kernel.SporSch.LySylDefs
public import CFSG.Sporadic.Schreier.LyCheckGLQ
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.KS.SporSch.LyGLQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySyl CFSG.Sporadic.LySchreier.Native

@[expose] noncomputable def unpk (y : Nat) : Nat × Nat × Nat := (b8 y 0, b8 y 1, b8 y 2)

theorem b8_lt (x j : Nat) : b8 x j < 256 := by
  unfold b8
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem tbl_tm {MT : Nat → Nat} {i j : Nat} (hi : i < 256) (hj : j < 256) :
    tm (TBL MT 256) i j = tmK MT i j := by
  unfold tm TBL
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem tpowK_succ (MT : Nat → Nat) (x e : Nat) : tpowK MT x (e + 1) = tmK MT (tpowK MT x e) x := by
  change strictN (tpowK MT x e) (fun a => tmK MT a x) = _
  exact LyLoop.strictN_eqP _ _

theorem tpowK_lt (MT : Nat → Nat) (x : Nat) : ∀ e, tpowK MT x e < 256
  | 0 => (by decide : (0 : Nat) < 256)
  | e + 1 => by
    rw [tpowK_succ]
    exact b8_lt _ _

theorem tpow_eq {MT : Nat → Nat} {x : Nat} (hx : x < 256) :
    ∀ e, tpow (TBL MT 256) x e = tpowK MT x e
  | 0 => rfl
  | e + 1 => by
    rw [tpowK_succ, ← tbl_tm (tpowK_lt MT x e) hx, ← tpow_eq hx e]
    rfl

theorem nIf_eq0 (a t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t (Nat.beq a 0) = if a = 0 then t else e := by
  cases h : Nat.beq a 0
  · have ha : a ≠ 0 := fun h' => by simp [h'] at h
    simp [ha]
  · simp [Nat.eq_of_beq_eq_true h]

theorem sig_eq {MT : Nat → Nat} {SG : Nat} (h : allN 256 (sigQ MT SG) = true) {x : Nat}
    (hx : x < 256) :
    sgK SG x = (if tpow (TBL MT 256) x 2 = 0 then 2 else 0) +
      (if tpow (TBL MT 256) x 4 = 0 then 1 else 0) := by
  have c := allN_spec h x hx
  unfold sigQ at c
  rw [tpow_eq hx, tpow_eq hx]
  rw [Nat.eq_of_beq_eq_true c, nIf_eq0, nIf_eq0]
  rfl

private theorem ksGWlenL (L : List Nat) : lenL L = L.length := by
  induction L with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem ksGWgetW (W : List (List Nat)) (t : Nat) : getW W t = W.getD t [] := by
  induction W generalizing t with
  | nil => rfl
  | cons w W ih =>
    cases t with
    | zero => rfl
    | succ t => rw [List.getD_cons_succ]; exact ih t

private theorem ksGWgetQ (Q : List Nat) (t : Nat) : getQ Q t = Q.getD t 0 := by
  induction Q generalizing t with
  | nil => rfl
  | cons q Q ih =>
    cases t with
    | zero => rfl
    | succ t => rw [List.getD_cons_succ]; exact ih t

private theorem ksGWeqL : ∀ {a b : List Nat}, eqL a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h
  | x :: a, z :: b, h => by
    have h' : bAnd(Nat.beq x z, eqL a b) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rw [Nat.eq_of_beq_eq_true h1, ksGWeqL h2]

private theorem ksGWhasBit_one (z : Nat) : hasBit 1 z = decide (z = 0) := by
  rw [CFSG.KS.Raw.Orb.hasBit_eq]
  have e : (1 : Nat) = 2 ^ 0 := rfl
  rw [e, Nat.testBit_two_pow]
  exact decide_eq_decide.mpr eq_comm

private theorem ksGWhasBit_or (M z w : Nat) :
    hasBit (Nat.lor M (Nat.shiftLeft 1 z)) w = (hasBit M w || decide (z = w)) := by
  rw [CFSG.KS.Raw.Orb.hasBit_eq, CFSG.KS.Raw.Orb.hasBit_eq]
  change (M ||| Nat.shiftLeft 1 z).testBit w = (M.testBit w || decide (z = w))
  rw [Nat.testBit_or, show Nat.shiftLeft 1 z = 2 ^ z by exact Nat.one_shiftLeft z,
    Nat.testBit_two_pow]

private noncomputable def ksGWwPair (MT : Nat → Nat) (k x : Nat) (p : List Nat × Nat) :
    List Nat × Nat :=
  if (hasBit p.2 (tmK MT (b8 gK k) x)) = true then p
  else (p.1 ++ [tmK MT (b8 gK k) x],
    Nat.lor p.2 (Nat.shiftLeft (nat_lit 1) (tmK MT (b8 gK k) x)))

private noncomputable def ksGWw3 (MT : Nat → Nat) (x : Nat) (p : List Nat × Nat) :
    List Nat × Nat :=
  ksGWwPair MT 2 x (ksGWwPair MT 1 x (ksGWwPair MT 0 x p))

private noncomputable def ksGWwNext (MT : Nat → Nat) (h : Nat) (p : List Nat × Nat) :
    List Nat × Nat :=
  if h < lenL p.1 then ksGWw3 MT (getQ p.1 h) p else p

private noncomputable def ksGWwRec (MT : Nat → Nat) : Nat → List Nat × Nat :=
  Nat.rec (motive := fun _ => List Nat × Nat) ([nat_lit 0], nat_lit 1)
    (fun h ih => ksGWwNext MT h ih)

private noncomputable def ksGWlPair (T : Array (Array Nat)) (k x : Nat) (wx : List Nat)
    (s : Array (Option (List Nat)) × Array Nat) :
    Array (Option (List Nat)) × Array Nat :=
  let z := tm T (pickY glqGens k) x
  if (decide (z < 256) && (s.1[z]!).isNone) = true then
    (s.1.set! z (some (k :: wx)), s.2.push z)
  else s

private noncomputable def ksGWl3 (T : Array (Array Nat)) (x : Nat) (wx : List Nat)
    (s : Array (Option (List Nat)) × Array Nat) :
    Array (Option (List Nat)) × Array Nat :=
  ksGWlPair T 2 x wx (ksGWlPair T 1 x wx (ksGWlPair T 0 x wx s))

private noncomputable def ksGWlStep (T : Array (Array Nat)) (h : Nat)
    (s : Array (Option (List Nat)) × Array Nat) :
    Array (Option (List Nat)) × Array Nat :=
  if h < s.2.size then
    let x := s.2[h]!
    let wx := s.1[x]!.getD []
    ksGWl3 T x wx s
  else s

private noncomputable def ksGWlRec (T : Array (Array Nat)) :
    Nat → Array (Option (List Nat)) × Array Nat :=
  Nat.rec (motive := fun _ => Array (Option (List Nat)) × Array Nat)
    ((Array.replicate 256 none).set! 0 (some []), #[0])
    (fun h ih => ksGWlStep T h ih)

private noncomputable def ksGWlBody (T : Array (Array Nat)) (k x : Nat) (wx : List Nat)
    (s : Array (Option (List Nat)) × Array Nat) :
    Id (ForInStep (Array (Option (List Nat)) × Array Nat)) :=
  let z := tm T (pickY glqGens k) x
  if (decide (z < 256) && (s.1[z]!).isNone) = true then
    pure (ForInStep.yield (s.1.set! z (some (k :: wx)), s.2.push z))
  else pure (ForInStep.yield s)

private noncomputable def ksGWlOuter (T : Array (Array Nat)) (h : Nat)
    (s : Array (Option (List Nat)) × Array Nat) :
    Id (ForInStep (Array (Option (List Nat)) × Array Nat)) :=
  if h < s.2.size then
    let x := s.2[h]!
    let wx := s.1[x]!.getD []
    let s' := forIn (m := Id) [:3] s fun k s => ksGWlBody T k x wx s
    pure (ForInStep.yield s')
  else pure (ForInStep.yield s)

private theorem ksGWl3_eq_fold (T : Array (Array Nat)) (x : Nat) (wx : List Nat)
    (s : Array (Option (List Nat)) × Array Nat) :
    ksGWl3 T x wx s = (List.range' 0 3 1).foldl (fun s k => ksGWlPair T k x wx s) s := rfl

private theorem ksGWlBody_eq (T : Array (Array Nat)) (k x : Nat) (wx : List Nat)
    (s : Array (Option (List Nat)) × Array Nat) :
    ksGWlBody T k x wx s = pure (ForInStep.yield (ksGWlPair T k x wx s)) := by
  unfold ksGWlBody ksGWlPair
  by_cases hc : (decide (tm T (pickY glqGens k) x < 256) &&
      (s.1[tm T (pickY glqGens k) x]!).isNone) = true
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]

private theorem ksGWl_forIn3 (T : Array (Array Nat)) (x : Nat) (wx : List Nat)
    (s : Array (Option (List Nat)) × Array Nat) :
    forIn (m := Id) [:3] s (fun k s => ksGWlBody T k x wx s) = ksGWl3 T x wx s := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  change forIn (List.range' 0 3 1) s (fun k s => ksGWlBody T k x wx s) = ksGWl3 T x wx s
  rw [show (fun k s => ksGWlBody T k x wx s) =
      (fun k s => pure (ForInStep.yield (ksGWlPair T k x wx s))) from
    funext fun k => funext fun s => ksGWlBody_eq T k x wx s]
  rw [List.forIn_pure_yield_eq_foldl]
  exact (ksGWl3_eq_fold T x wx s).symm

private theorem ksGWlOuter_eq (T : Array (Array Nat)) (h : Nat)
    (s : Array (Option (List Nat)) × Array Nat) :
    ksGWlOuter T h s = pure (ForInStep.yield (ksGWlStep T h s)) := by
  unfold ksGWlOuter ksGWlStep
  by_cases hh : h < s.2.size
  · rw [if_pos hh, if_pos hh]
    dsimp only
    rw [ksGWl_forIn3]
  · rw [if_neg hh, if_neg hh]

private def ksGWMatch (W : List (List Nat)) (M : Nat)
    (A : Array (Option (List Nat))) : Prop :=
  A.size = 256 ∧ ∀ z < 256,
    (hasBit M z = true → A[z]! = some (getW W z)) ∧
    (hasBit M z = false → A[z]! = none)

private theorem ksGWMatch_set {W : List (List Nat)} {M : Nat}
    {A : Array (Option (List Nat))} {z : Nat} {v : List Nat}
    (hA : ksGWMatch W M A) (_hz : z < 256) (hv : v = getW W z) :
    ksGWMatch W (Nat.lor M (Nat.shiftLeft 1 z)) (A.set! z (some v)) := by
  refine ⟨by rw [Array.size_set!]; exact hA.1, ?_⟩
  intro w hw
  by_cases hwz : z = w
  · subst hwz
    constructor
    · intro _
      rw [Array.getElem!_set!_self A z (some v) (by rw [hA.1]; exact hw), hv]
    · intro hb
      rw [ksGWhasBit_or] at hb
      simp at hb
  · have hget : (A.set! z (some v))[w]! = A[w]! :=
      Array.getElem!_set!_ne A z w (some v) hwz
    have hb : hasBit (Nat.lor M (Nat.shiftLeft 1 z)) w = hasBit M w := by
      rw [ksGWhasBit_or]
      simp [hwz]
    rw [hget, hb]
    exact hA.2 w hw

private theorem ksGWmatch_init {W : List (List Nat)} (h0 : getW W 0 = []) :
    ksGWMatch W 1 ((Array.replicate 256 none).set! 0 (some [])) := by
  refine ⟨by rw [Array.size_set!, Array.size_replicate], ?_⟩
  intro z hz
  rw [ksGWhasBit_one]
  by_cases hz0 : z = 0
  · subst hz0
    constructor
    · intro _
      rw [Array.getElem!_set!_self (Array.replicate 256 none) 0 (some [])
        (by rw [Array.size_replicate]; decide), h0]
    · intro hb
      simp at hb
  · have hdec : decide (z = 0) = false := by simp [hz0]
    rw [hdec]
    constructor
    · intro hb
      simp at hb
    · intro _
      rw [Array.getElem!_set!_ne (Array.replicate 256 none) 0 z (some [])
        (Ne.symm hz0), Array.getElem!_eq_getD]
      simp [Array.getD, hz]

private theorem ksGWpickY {k : Nat} (hk : k < 3) : pickY glqGens k = b8 gK k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> rfl

private theorem ksGWlPair_step {MT : Nat → Nat} {W : List (List Nat)} {k x : Nat}
    {wx : List Nat} {A : Array (Option (List Nat))} {q : Array Nat} {Q : List Nat}
    {M : Nat} (hk : k < 3) (hx : x < 256) (hwx : wx = getW W x)
    (hA : ksGWMatch W M A) (hq : q.toList = Q)
    (hcheck : hasBit M (tmK MT (b8 gK k) x) = false →
      eqL (getW W (tmK MT (b8 gK k) x)) (k :: getW W x) = true) :
    ksGWMatch W (ksGWwPair MT k x (Q, M)).2
        (ksGWlPair (TBL MT 256) k x wx (A, q)).1 ∧
      (ksGWlPair (TBL MT 256) k x wx (A, q)).2.toList =
        (ksGWwPair MT k x (Q, M)).1 := by
  let z := tmK MT (b8 gK k) x
  have hz : z < 256 := b8_lt _ _
  have hzt : tm (TBL MT 256) (pickY glqGens k) x = z := by
    rw [ksGWpickY hk, tbl_tm (b8_lt _ _) hx]
  by_cases hb : hasBit M z = true
  · have hnone : (A[z]!).isNone = false := by
      rw [(hA.2 z hz).1 hb]; rfl
    have hcond : ¬ ((decide (z < 256) && (A[z]!).isNone) = true) := by
      rw [hnone]; simp
    have hp : ksGWlPair (TBL MT 256) k x wx (A, q) = (A, q) := by
      unfold ksGWlPair
      rw [hzt, if_neg hcond]
    rw [hp]
    refine ⟨?_, ?_⟩
    · unfold ksGWwPair
      rw [if_pos hb]
      exact hA
    · unfold ksGWwPair
      rw [if_pos hb, hq]
  · have hbf : hasBit M z = false := by
      cases h : hasBit M z <;> simp_all
    have hnone : (A[z]!).isNone = true := by
      rw [(hA.2 z hz).2 hbf]; rfl
    have hcond : (decide (z < 256) && (A[z]!).isNone) = true := by
      rw [hnone]; simp [hz]
    have hp : ksGWlPair (TBL MT 256) k x wx (A, q) =
        (A.set! z (some (k :: wx)), q.push z) := by
      unfold ksGWlPair
      rw [hzt, if_pos hcond]
    rw [hp]
    have hv : k :: wx = getW W z := by
      rw [hwx]
      exact (ksGWeqL (hcheck hbf)).symm
    unfold ksGWwPair
    rw [if_neg (by rw [hbf]; simp)]
    refine ⟨ksGWMatch_set hA hz hv, ?_⟩
    rw [Array.toList_push, hq]

private theorem ksGWQ_bits {Q : List Nat} {M z : Nat}
    (hQ : ∀ w, w ∈ Q ↔ hasBit M w = true) :
    ∀ w, w ∈ (if (hasBit M z) = true then Q else Q ++ [z]) ↔
      hasBit (if (hasBit M z) = true then M else Nat.lor M (Nat.shiftLeft 1 z)) w = true := by
  intro w
  by_cases hb : hasBit M z = true
  · simp [hb, hQ w]
  · rw [if_neg hb, if_neg hb, List.mem_append, List.mem_singleton, ksGWhasBit_or,
      Bool.or_eq_true]
    constructor
    · rintro (h | h)
      · exact Or.inl ((hQ w).1 h)
      · exact Or.inr (by simpa [eq_comm] using h)
    · rintro (h | h)
      · exact Or.inl ((hQ w).2 h)
      · exact Or.inr (by simpa [eq_comm] using h)

private theorem ksGWwPair_bits {MT : Nat → Nat} {k x : Nat} {Q : List Nat} {M : Nat}
    (hQ : ∀ w, w ∈ Q ↔ hasBit M w = true) :
    ∀ w, w ∈ (ksGWwPair MT k x (Q, M)).1 ↔
      hasBit (ksGWwPair MT k x (Q, M)).2 w = true := by
  unfold ksGWwPair
  by_cases hb : hasBit M (tmK MT (b8 gK k) x) = true
  · rw [if_pos hb]
    simpa [hb] using ksGWQ_bits (Q := Q) (M := M) (z := tmK MT (b8 gK k) x) hQ
  · rw [if_neg hb]
    simpa [hb] using ksGWQ_bits (Q := Q) (M := M) (z := tmK MT (b8 gK k) x) hQ

private theorem ksGWw3_bits {MT : Nat → Nat} {x : Nat} {Q : List Nat} {M : Nat}
    (hQ : ∀ w, w ∈ Q ↔ hasBit M w = true) :
    ∀ w, w ∈ (ksGWw3 MT x (Q, M)).1 ↔ hasBit (ksGWw3 MT x (Q, M)).2 w = true := by
  have h0 := ksGWwPair_bits (MT := MT) (k := 0) (x := x) (Q := Q) (M := M) hQ
  have h1 := ksGWwPair_bits (MT := MT) (k := 1) (x := x)
    (Q := (ksGWwPair MT 0 x (Q, M)).1) (M := (ksGWwPair MT 0 x (Q, M)).2) h0
  have h2 := ksGWwPair_bits (MT := MT) (k := 2) (x := x)
    (Q := (ksGWwPair MT 1 x (ksGWwPair MT 0 x (Q, M))).1)
    (M := (ksGWwPair MT 1 x (ksGWwPair MT 0 x (Q, M))).2) h1
  simpa [ksGWw3] using h2

private theorem ksGWwPair_check {MT : Nat → Nat} {W : List (List Nat)} {x k M : Nat}
    {Q : List Nat}
    {cont : List Nat → Nat → Bool} (hw : wStep MT W x k Q M cont = true) :
    hasBit M (tmK MT (b8 gK k) x) = false →
      eqL (getW W (tmK MT (b8 gK k) x)) (k :: getW W x) = true := by
  intro hb
  unfold wStep at hw
  rw [LyLoop.strictB_eqB, LyLoop.bIf_eqP] at hw
  have hbn : ¬ (hasBit M (tmK MT (b8 gK k) x) = true) := by rw [hb]; simp
  rw [if_neg hbn] at hw
  exact (bAnd_iff _ _).1 hw |>.1

private theorem ksGWwPair_cont {MT : Nat → Nat} {W : List (List Nat)} {x k M : Nat}
    {Q : List Nat}
    {cont : List Nat → Nat → Bool} (hw : wStep MT W x k Q M cont = true) :
    cont (ksGWwPair MT k x (Q, M)).1 (ksGWwPair MT k x (Q, M)).2 = true := by
  unfold wStep at hw
  rw [LyLoop.strictB_eqB, LyLoop.bIf_eqP] at hw
  unfold ksGWwPair
  by_cases hb : hasBit M (tmK MT (b8 gK k) x) = true
  · rw [if_pos hb] at hw
    rw [if_pos hb]
    exact hw
  · rw [if_neg hb] at hw
    rw [if_neg hb]
    exact (bAnd_iff _ _).1 hw |>.2

private theorem ksGWwPair_fst_lt {MT : Nat → Nat} {k x : Nat} {Q : List Nat} {M : Nat}
    (hQ : ∀ y ∈ Q, y < 256) :
    ∀ y ∈ (ksGWwPair MT k x (Q, M)).1, y < 256 := by
  intro y hy
  unfold ksGWwPair at hy
  by_cases hb : hasBit M (tmK MT (b8 gK k) x) = true
  · rw [if_pos hb] at hy
    exact hQ y hy
  · rw [if_neg hb] at hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hQ y hy
    · exact b8_lt _ _

private theorem ksGWw3_fst_lt {MT : Nat → Nat} {x : Nat} {Q : List Nat} {M : Nat}
    (hQ : ∀ y ∈ Q, y < 256) :
    ∀ y ∈ (ksGWw3 MT x (Q, M)).1, y < 256 := by
  have h0 := ksGWwPair_fst_lt (MT := MT) (k := 0) (x := x) (Q := Q) (M := M) hQ
  have h1 := ksGWwPair_fst_lt (MT := MT) (k := 1) (x := x)
    (Q := (ksGWwPair MT 0 x (Q, M)).1) (M := (ksGWwPair MT 0 x (Q, M)).2) h0
  have h2 := ksGWwPair_fst_lt (MT := MT) (k := 2) (x := x)
    (Q := (ksGWwPair MT 1 x (ksGWwPair MT 0 x (Q, M))).1)
    (M := (ksGWwPair MT 1 x (ksGWwPair MT 0 x (Q, M))).2) h1
  simpa [ksGWw3] using h2

private theorem ksGWwNext_fst_lt {MT : Nat → Nat} {h : Nat} {Q : List Nat} {M : Nat}
    (hQ : ∀ y ∈ Q, y < 256) :
    ∀ y ∈ (ksGWwNext MT h (Q, M)).1, y < 256 := by
  unfold ksGWwNext
  by_cases hh : h < lenL Q
  · rw [if_pos hh]
    exact ksGWw3_fst_lt hQ
  · rw [if_neg hh]
    exact hQ

private theorem ksGWwRec_fst_lt (MT : Nat → Nat) (h : Nat) :
    ∀ y ∈ (ksGWwRec MT h).1, y < 256 := by
  induction h with
  | zero =>
    intro y hy
    simp [ksGWwRec] at hy
    omega
  | succ h ih =>
    simpa [ksGWwRec] using ksGWwNext_fst_lt (MT := MT) (h := h) ih

private theorem ksGWwPair_zero_mem {MT : Nat → Nat} {k x : Nat} {Q : List Nat} {M : Nat}
    (h0 : 0 ∈ Q) : 0 ∈ (ksGWwPair MT k x (Q, M)).1 := by
  unfold ksGWwPair
  by_cases hb : hasBit M (tmK MT (b8 gK k) x) = true
  · rw [if_pos hb]
    exact h0
  · rw [if_neg hb]
    exact List.mem_append_left _ h0

private theorem ksGWw3_zero_mem {MT : Nat → Nat} {x : Nat} {Q : List Nat} {M : Nat}
    (h0 : 0 ∈ Q) : 0 ∈ (ksGWw3 MT x (Q, M)).1 := by
  have h0' := ksGWwPair_zero_mem (MT := MT) (k := 0) (x := x) (Q := Q) (M := M) h0
  have h1' := ksGWwPair_zero_mem (MT := MT) (k := 1) (x := x)
    (Q := (ksGWwPair MT 0 x (Q, M)).1) (M := (ksGWwPair MT 0 x (Q, M)).2) h0'
  have h2' := ksGWwPair_zero_mem (MT := MT) (k := 2) (x := x)
    (Q := (ksGWwPair MT 1 x (ksGWwPair MT 0 x (Q, M))).1)
    (M := (ksGWwPair MT 1 x (ksGWwPair MT 0 x (Q, M))).2) h1'
  simpa [ksGWw3] using h2'

private theorem ksGWwNext_zero_mem {MT : Nat → Nat} {h : Nat} {Q : List Nat} {M : Nat}
    (h0 : 0 ∈ Q) : 0 ∈ (ksGWwNext MT h (Q, M)).1 := by
  unfold ksGWwNext
  by_cases hh : h < lenL Q
  · rw [if_pos hh]
    exact ksGWw3_zero_mem h0
  · rw [if_neg hh]
    exact h0

private theorem ksGWwRec_zero_mem (MT : Nat → Nat) (h : Nat) :
    0 ∈ (ksGWwRec MT h).1 := by
  induction h with
  | zero => simp [ksGWwRec]
  | succ h ih => simpa [ksGWwRec] using ksGWwNext_zero_mem (MT := MT) (h := h) ih

attribute [irreducible] ksGWlPair ksGWwPair

private theorem ksGWl3_step {MT : Nat → Nat} {W : List (List Nat)} {x : Nat}
    {wx : List Nat} {A : Array (Option (List Nat))} {q : Array Nat} {Q : List Nat}
    {M : Nat} (hx : x < 256) (hwx : wx = getW W x)
    (hA : ksGWMatch W M A) (hq : q.toList = Q)
    (h0 : hasBit M (tmK MT (b8 gK 0) x) = false →
      eqL (getW W (tmK MT (b8 gK 0) x)) (0 :: getW W x) = true)
    (h1 : hasBit (ksGWwPair MT 0 x (Q, M)).2 (tmK MT (b8 gK 1) x) = false →
      eqL (getW W (tmK MT (b8 gK 1) x)) (1 :: getW W x) = true)
    (h2 : hasBit (ksGWwPair MT 1 x (ksGWwPair MT 0 x (Q, M))).2
        (tmK MT (b8 gK 2) x) = false →
      eqL (getW W (tmK MT (b8 gK 2) x)) (2 :: getW W x) = true) :
    ksGWMatch W (ksGWw3 MT x (Q, M)).2 (ksGWl3 (TBL MT 256) x wx (A, q)).1 ∧
      (ksGWl3 (TBL MT 256) x wx (A, q)).2.toList = (ksGWw3 MT x (Q, M)).1 := by
  obtain ⟨hA0, hq0⟩ := ksGWlPair_step (MT := MT) (k := 0) (hk := by decide) hx hwx hA hq h0
  set A1 := (ksGWlPair (TBL MT 256) 0 x wx (A, q)).1 with hA1e
  set q1 := (ksGWlPair (TBL MT 256) 0 x wx (A, q)).2 with hq1e
  set Q1 := (ksGWwPair MT 0 x (Q, M)).1 with hQ1e
  set M1 := (ksGWwPair MT 0 x (Q, M)).2 with hM1e
  have hA1 : ksGWMatch W M1 A1 := by rw [hA1e, hM1e]; exact hA0
  have hq1 : q1.toList = Q1 := by rw [hq1e, hQ1e]; exact hq0
  have h1' : hasBit M1 (tmK MT (b8 gK 1) x) = false →
      eqL (getW W (tmK MT (b8 gK 1) x)) (1 :: getW W x) = true := by
    rw [hM1e]; exact h1
  obtain ⟨hA1', hq1'⟩ := ksGWlPair_step (MT := MT) (k := 1) (hk := by decide)
    (A := A1) (q := q1) (Q := Q1) (M := M1) hx hwx hA1 hq1 h1'
  set A2 := (ksGWlPair (TBL MT 256) 1 x wx (A1, q1)).1 with hA2e
  set q2 := (ksGWlPair (TBL MT 256) 1 x wx (A1, q1)).2 with hq2e
  set Q2 := (ksGWwPair MT 1 x (Q1, M1)).1 with hQ2e
  set M2 := (ksGWwPair MT 1 x (Q1, M1)).2 with hM2e
  have hA2 : ksGWMatch W M2 A2 := by rw [hA2e, hM2e]; exact hA1'
  have hq2 : q2.toList = Q2 := by rw [hq2e, hQ2e]; exact hq1'
  have h2' : hasBit M2 (tmK MT (b8 gK 2) x) = false →
      eqL (getW W (tmK MT (b8 gK 2) x)) (2 :: getW W x) = true := by
    rw [hM2e]; exact h2
  obtain ⟨hA2', hq2'⟩ := ksGWlPair_step (MT := MT) (k := 2) (hk := by decide)
    (A := A2) (q := q2) (Q := Q2) (M := M2) hx hwx hA2 hq2 h2'
  set A3 := (ksGWlPair (TBL MT 256) 2 x wx (A2, q2)).1 with hA3e
  set q3 := (ksGWlPair (TBL MT 256) 2 x wx (A2, q2)).2 with hq3e
  set Q3 := (ksGWwPair MT 2 x (Q2, M2)).1 with hQ3e
  set M3 := (ksGWwPair MT 2 x (Q2, M2)).2 with hM3e
  have hA3 : ksGWMatch W M3 A3 := by rw [hA3e, hM3e]; exact hA2'
  have hq3 : q3.toList = Q3 := by rw [hq3e, hQ3e]; exact hq2'
  have ep : ksGWl3 (TBL MT 256) x wx (A, q) = (A3, q3) := by rw [ksGWl3]
  have ew : ksGWw3 MT x (Q, M) = (Q3, M3) := by rw [ksGWw3]
  rw [ep, ew]
  refine ⟨?_, ?_⟩
  · exact hA3
  · exact hq3

private theorem ksGWwRun_succ (MT : Nat → Nat) (W : List (List Nat)) (n h : Nat)
    (Q : List Nat) (M : Nat) :
    wRun MT W (n + 1) h Q M =
      bIf(Nat.blt h (lenL Q),
        strictB (getQ Q h) (fun x => wStep MT W x 0 Q M (fun Q M =>
          wStep MT W x 1 Q M (fun Q M => wStep MT W x 2 Q M (wRun MT W n (h + 1))))),
        wRun MT W n (h + 1) Q M) := rfl

private theorem ksGWwRun_cont {MT : Nat → Nat} {W : List (List Nat)} {n h : Nat}
    {Q : List Nat} {M x : Nat} (hx : x = getQ Q h)
    (hw : wRun MT W (n + 1) h Q M = true) (hh : h < lenL Q) :
    wStep MT W x 0 Q M (fun Q' M' =>
      wStep MT W x 1 Q' M' (fun Q'' M'' =>
        wStep MT W x 2 Q'' M'' (wRun MT W n (h + 1)))) = true := by
  subst hx
  rw [ksGWwRun_succ] at hw
  rw [LyLoop.bIf_eqP, if_pos (Nat.blt_eq.mpr hh), LyLoop.strictB_eqB] at hw
  simpa using hw

private theorem ksGWwRun_step {MT : Nat → Nat} {W : List (List Nat)} {h : Nat}
    {Q : List Nat} {M : Nat} (hw : wRun MT W (256 - h) h Q M = true)
    (hh : h < 256) :
    wRun MT W (256 - (h + 1)) (h + 1) (ksGWwNext MT h (Q, M)).1
      (ksGWwNext MT h (Q, M)).2 = true := by
  have hn : 256 - h = (256 - (h + 1)) + 1 := by omega
  by_cases hs : h < lenL Q
  · have hw' : wRun MT W ((256 - (h + 1)) + 1) h Q M = true := by rwa [← hn]
    have h0 := ksGWwRun_cont (MT := MT) (W := W) (n := 256 - (h + 1)) (h := h)
      (Q := Q) (M := M) (x := getQ Q h) rfl hw' hs
    have h1 := ksGWwPair_cont h0
    have h2 := ksGWwPair_cont h1
    have h3 := ksGWwPair_cont h2
    simpa [ksGWwNext, ksGWw3, if_pos hs] using h3
  · have hw' : wRun MT W ((256 - (h + 1)) + 1) h Q M = true := by rwa [← hn]
    rw [ksGWwRun_succ] at hw'
    rw [LyLoop.bIf_eqP, if_neg (by rw [Nat.blt_eq]; exact hs)] at hw'
    simpa [ksGWwNext, if_neg hs] using hw'

private theorem ksGWq_get {Q : List Nat} {q : Array Nat} (hq : q.toList = Q)
    {h : Nat} (hh : h < q.size) : q[h]! = getQ Q h := by
  have hlen : h < Q.length := by rw [← hq, Array.length_toList]; exact hh
  have htl : h < q.toList.length := by rwa [Array.length_toList]
  rw [getElem!_pos q h hh, ← Array.getElem_toList (xs := q) (i := h) htl]
  subst hq
  rw [ksGWgetQ, List.getD_eq_getElem _ _ hlen]

private theorem ksGWlStep_sound {MT : Nat → Nat} {W : List (List Nat)} {h : Nat}
    {A : Array (Option (List Nat))} {q : Array Nat} {Q : List Nat} {M : Nat}
    (hA : ksGWMatch W M A) (hq : q.toList = Q)
    (hQbits : ∀ w, w ∈ Q ↔ hasBit M w = true) (hQlt : ∀ y ∈ Q, y < 256)
    (hw : wRun MT W (256 - h) h Q M = true) (hh : h < 256) (hsmall : h < lenL Q) :
    ksGWMatch W (ksGWwNext MT h (Q, M)).2 (ksGWlStep (TBL MT 256) h (A, q)).1 ∧
      (ksGWlStep (TBL MT 256) h (A, q)).2.toList = (ksGWwNext MT h (Q, M)).1 ∧
      (∀ w, w ∈ (ksGWwNext MT h (Q, M)).1 ↔
        hasBit (ksGWwNext MT h (Q, M)).2 w = true) := by
  have hlen : h < Q.length := by rwa [ksGWlenL] at hsmall
  have hsize : q.size = Q.length := by rw [← hq, Array.length_toList]
  have hqs : h < q.size := by rwa [hsize]
  have hxmem : getQ Q h ∈ Q := by
    rw [ksGWgetQ, List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  have hx : getQ Q h < 256 := hQlt _ hxmem
  have hwx : (A[getQ Q h]!).getD [] = getW W (getQ Q h) := by
    have hbit : hasBit M (getQ Q h) = true := (hQbits _).1 hxmem
    rw [(hA.2 _ hx).1 hbit]
    rfl
  have hn : 256 - h = (256 - (h + 1)) + 1 := by omega
  have hw' : wRun MT W ((256 - (h + 1)) + 1) h Q M = true := by rwa [← hn]
  have h0 := ksGWwRun_cont (MT := MT) (W := W) (n := 256 - (h + 1)) (h := h)
    (Q := Q) (M := M) (x := getQ Q h) rfl hw' hsmall
  have hc0 := ksGWwPair_check h0
  have h1 := ksGWwPair_cont h0
  have hc1 := ksGWwPair_check h1
  have h2 := ksGWwPair_cont h1
  have hc2 := ksGWwPair_check h2
  have h3 := ksGWwPair_cont h2
  have hstep := ksGWl3_step (MT := MT) (W := W) (x := getQ Q h)
    (wx := (A[getQ Q h]!).getD []) (A := A) (q := q) (Q := Q) (M := M)
    hx hwx hA hq hc0 hc1 hc2
  have hqget : q[h]! = getQ Q h := ksGWq_get hq hqs
  have hep : ksGWlStep (TBL MT 256) h (A, q) =
      ksGWl3 (TBL MT 256) (getQ Q h) (A[getQ Q h]!.getD []) (A, q) := by
    unfold ksGWlStep
    rw [if_pos hqs]
    dsimp only
    rw [hqget]
  have hnext : ksGWwNext MT h (Q, M) = ksGWw3 MT (getQ Q h) (Q, M) := by
    unfold ksGWwNext
    rw [if_pos hsmall]
  refine ⟨?_, ?_, ?_⟩
  · rw [hep, hnext]
    exact hstep.1
  · rw [hep, hnext]
    exact hstep.2
  · rw [hnext]
    exact ksGWw3_bits (MT := MT) (x := getQ Q h) hQbits

private structure ksGWGood (MT : Nat → Nat) (W : List (List Nat)) (h : Nat)
    (s : Array (Option (List Nat)) × Array Nat) : Prop where
  queue : s.2.toList = (ksGWwRec MT h).1
  matchA : ksGWMatch W (ksGWwRec MT h).2 s.1
  bits : ∀ w, w ∈ (ksGWwRec MT h).1 ↔ hasBit (ksGWwRec MT h).2 w = true

private theorem ksGWwRec_zero (MT : Nat → Nat) :
    ksGWwRec MT 0 = ([0], 1) := by
  rw [ksGWwRec, Nat.rec_zero]

private theorem ksGWgood_zero {MT : Nat → Nat} {W : List (List Nat)}
    (h0 : getW W 0 = []) :
    ksGWGood MT W 0 ((Array.replicate 256 none).set! 0 (some []), #[0]) := by
  have hQ : (#[0] : Array Nat).toList = (ksGWwRec MT 0).1 := by
    rw [ksGWwRec_zero]
  have hA : ksGWMatch W (ksGWwRec MT 0).2
      ((Array.replicate 256 none).set! 0 (some [])) := by
    rw [ksGWwRec_zero]
    exact ksGWmatch_init h0
  have hb : ∀ w, w ∈ (ksGWwRec MT 0).1 ↔ hasBit (ksGWwRec MT 0).2 w = true := by
    rw [ksGWwRec_zero]
    intro w
    rw [ksGWhasBit_one]
    simp
  refine { queue := ?_, matchA := ?_, bits := ?_ }
  · simp [ksGWwRec_zero]
  · simpa [ksGWwRec_zero] using hA
  · simpa [ksGWwRec_zero] using hb

private theorem ksGWgood_succ {MT : Nat → Nat} {W : List (List Nat)} {h : Nat}
    {s : Array (Option (List Nat)) × Array Nat} (hg : ksGWGood MT W h s)
    (hh : h < 256)
    (hw : wRun MT W (256 - h) h (ksGWwRec MT h).1 (ksGWwRec MT h).2 = true) :
    ksGWGood MT W (h + 1) (ksGWlStep (TBL MT 256) h s) := by
  obtain ⟨hQ, hA, hbits⟩ := hg
  by_cases hs : h < lenL (ksGWwRec MT h).1
  · have hstep := ksGWlStep_sound (MT := MT) (W := W) (h := h) (A := s.1)
      (q := s.2) (Q := (ksGWwRec MT h).1) (M := (ksGWwRec MT h).2)
      hA hQ hbits (ksGWwRec_fst_lt MT h) hw hh hs
    exact ⟨hstep.2.1, hstep.1, hstep.2.2⟩
  · have hqlen : ¬ h < s.2.size := by
      have hsz : s.2.size = (ksGWwRec MT h).1.length := by
        rw [← hQ, Array.length_toList]
      rw [hsz, ← ksGWlenL]
      exact hs
    have hstepeq : ksGWlStep (TBL MT 256) h s = s := by
      unfold ksGWlStep
      rw [if_neg hqlen]
    have hrec : ksGWwRec MT (h + 1) = ksGWwRec MT h := by
      change ksGWwNext MT h (ksGWwRec MT h) = ksGWwRec MT h
      unfold ksGWwNext
      rw [if_neg hs]
    rw [hstepeq]
    exact { queue := by rw [hrec]; exact hQ
            matchA := by rw [hrec]; exact hA
            bits := by rw [hrec]; exact hbits }

private theorem ksGWgood_iter {MT : Nat → Nat} {W : List (List Nat)}
    (h0 : getW W 0 = []) (hw : wRun MT W 256 0 [0] 1 = true) :
    ∀ h ≤ 256, ksGWGood MT W h (ksGWlRec (TBL MT 256) h) ∧
      wRun MT W (256 - h) h (ksGWwRec MT h).1 (ksGWwRec MT h).2 = true := by
  intro h
  induction h with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · simpa [ksGWlRec] using ksGWgood_zero h0
    · simpa [ksGWwRec] using hw
  | succ h ih =>
    intro hh
    obtain ⟨hg, hwr⟩ := ih (by omega)
    exact ⟨ksGWgood_succ hg (by omega) hwr, ksGWwRun_step hwr (by omega)⟩

private theorem ksGWl_final {MT : Nat → Nat} {W : List (List Nat)} {M : Nat}
    {Q : List Nat} {A : Array (Option (List Nat))} (hlen : W.length = 256)
    (hA : ksGWMatch W M A) (hbits : ∀ w, w ∈ Q ↔ hasBit M w = true)
    (hzero : 0 ∈ Q) (hEval : ∀ x < 256, evK MT gK (getW W x) = x)
    (hf : wRun MT W 0 256 Q M = true) :
    A.map (fun x => x.getD []) = W.toArray := by
  have hsome : ∀ z < 256, A[z]! = some (getW W z) := by
    intro z hz
    by_cases hb : hasBit M z = true
    · exact (hA.2 z hz).1 hb
    · have hbf : hasBit M z = false := by cases h : hasBit M z <;> simp_all
      have hf' : allN 256 (fun x => bIf(hasBit M x, true, eqL (getW W x) [])) = true := by
        change allN 256 (fun x => bIf(hasBit M x, true, eqL (getW W x) [])) = true at hf
        exact hf
      have htest := allN_spec hf' z hz
      rw [LyLoop.bIf_eqP, if_neg (by rw [hbf]; simp)] at htest
      have hzempty : getW W z = [] := ksGWeqL htest
      have hz0 : z = 0 := by
        have hev := hEval z hz
        rw [hzempty] at hev
        change 0 = z at hev
        omega
      have hzmem : z ∈ Q := by rw [hz0]; exact hzero
      have hbit := (hbits z).1 hzmem
      rw [hbf] at hbit
      contradiction
  apply Array.ext
  · simp [hA.1, hlen]
  · intro i hi1 hi2
    have hi : i < 256 := by
      simpa [hA.1] using hi1
    rw [Array.getElem_map]
    have hiA : i < A.size := by simpa [Array.size_map] using hi1
    rw [← getElem!_pos A i hiA, hsome i hi,
      List.getElem_toArray (xs := W) (i := i) hi2, ksGWgetW,
      List.getD_eq_getElem _ _ (by rwa [hlen])]
    rfl

private theorem ksGWl_forIn256 (T : Array (Array Nat)) :
    forIn (m := Id) [:256]
        (((Array.replicate 256 none).set! 0 (some []), #[0]) :
          Array (Option (List Nat)) × Array Nat)
        (fun h s => ksGWlOuter T h s) = ksGWlRec T 256 := by
  refine LyLoop.forIn_range_spec (R := fun h s => s = ksGWlRec T h) 256 _ _ rfl ?_
  intro h s _ hs
  subst hs
  exact ⟨ksGWlRec T (h + 1), ksGWlOuter_eq T h (ksGWlRec T h), rfl⟩

private theorem ksGWl_glqWords (T : Array (Array Nat)) :
    glqWords T = (ksGWlRec T 256).1.map (fun x => x.getD []) := by
  unfold glqWords
  change (Array.map (fun x => x.getD [])
      (forIn (m := Id) [:256]
        (((Array.replicate 256 none).set! 0 (some []), #[0]) :
          Array (Option (List Nat)) × Array Nat)
        (fun h s => ksGWlOuter T h s)).1) = _
  rw [ksGWl_forIn256]

theorem words_sound {MT : Nat → Nat} {W : List (List Nat)} (h : wordsK MT W = true) :
    glqWords (TBL MT 256) = W.toArray := by
  unfold wordsK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨hwrun, hall⟩ := (bAnd_iff _ _).1 h3
  have h0 : getW W 0 = [] := ksGWeqL h2
  have hlen : W.length = 256 := by
    have e := Nat.eq_of_beq_eq_true h1
    rwa [ksGWlenL, List.length_map] at e
  have hEval : ∀ x < 256, evK MT gK (getW W x) = x := fun x hx =>
    Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec hall x hx)).1
  obtain ⟨hgood, hwr⟩ := ksGWgood_iter h0 hwrun 256 (by decide)
  have hfinal := ksGWl_final hlen hgood.matchA hgood.bits (ksGWwRec_zero_mem MT 256) hEval hwr
  rw [ksGWl_glqWords]
  exact hfinal

theorem b8_div (x j : Nat) : b8 x j = x / 256 ^ j % 256 := by
  change (x >>> (8 * j)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem b8_three {a b c : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    b8 (Nat.add (Nat.add a (Nat.mul 256 b)) (Nat.mul 65536 c)) 0 = a ∧
      b8 (Nat.add (Nat.add a (Nat.mul 256 b)) (Nat.mul 65536 c)) 1 = b ∧
      b8 (Nat.add (Nat.add a (Nat.mul 256 b)) (Nat.mul 65536 c)) 2 = c ∧
      b8 (Nat.add a (Nat.mul 256 b)) 0 = a ∧ b8 (Nat.add a (Nat.mul 256 b)) 1 = b ∧
      b8 (Nat.add a (Nat.mul 65536 c)) 0 = a ∧ b8 (Nat.add a (Nat.mul 65536 c)) 2 = c ∧
      b8 a 0 = a := by
  simp only [b8_div, Nat.pow_zero, Nat.pow_one, Nat.div_one, Nat.add_eq, Nat.mul_eq,
    (by decide : (256 : Nat) ^ 2 = 65536)]
  omega

theorem evK_nil (MT : Nat → Nat) (y : Nat) : evK MT y [] = 0 := rfl

theorem evK_cons (MT : Nat → Nat) (y k : Nat) (w : List Nat) :
    evK MT y (k :: w) = tmK MT (b8 y k) (evK MT y w) :=
  LyLoop.strictN_eqP _ _

theorem tmK_lt (MT : Nat → Nat) (i j : Nat) : tmK MT i j < 256 := b8_lt _ _

theorem evK_lt (MT : Nat → Nat) (y : Nat) : ∀ w, evK MT y w < 256
  | [] => by rw [evK_nil]; decide
  | k :: w => by
    rw [evK_cons]
    exact tmK_lt _ _ _

theorem evalY_at {MT : Nat → Nat} {t : Nat × Nat × Nat} {y : Nat} :
    ∀ w : List Nat, (∀ k ∈ w, k < 3 ∧ pickY t k = b8 y k) →
    evalY (TBL MT 256) t w = evK MT y w
  | [], _ => rfl
  | k :: w, hw => by
    have e : evalY (TBL MT 256) t (k :: w) =
        tm (TBL MT 256) (pickY t k) (evalY (TBL MT 256) t w) := rfl
    rw [e, evK_cons, evalY_at w (fun j hj => hw j (by simp [hj])), (hw k (by simp)).2,
      tbl_tm (b8_lt _ _) (evK_lt _ _ _)]

theorem sg_beq {MT : Nat → Nat} {SG : Nat} (h : allN 256 (sigQ MT SG) = true) {x z : Nat}
    (hx : x < 256) (hz : z < 256) :
    Nat.beq (sgK SG x) (sgK SG z) = (sigT (TBL MT 256) x == sigT (TBL MT 256) z) := by
  rw [sig_eq h hx, sig_eq h hz]
  unfold sigT
  apply Bool.eq_iff_iff.mpr
  rw [Nat.beq_eq, beq_iff_eq]
  by_cases a1 : tpow (TBL MT 256) x 2 = 0 <;> by_cases a2 : tpow (TBL MT 256) x 4 = 0 <;>
    by_cases a3 : tpow (TBL MT 256) z 2 = 0 <;> by_cases a4 : tpow (TBL MT 256) z 4 = 0 <;>
    simp [a1, a2, a3, a4]

theorem tst_eq {MT : Nat → Nat} {SG : Nat} (h : allN 256 (sigQ MT SG) = true)
    {t : Nat × Nat × Nat} {y : Nat} (w : List Nat) (hw : ∀ k ∈ w, k < 3 ∧ pickY t k = b8 y k) :
    tstK MT SG y w =
      (sigT (TBL MT 256) (evalY (TBL MT 256) t w) ==
        sigT (TBL MT 256) (evalY (TBL MT 256) glqGens w)) := by
  have hg : ∀ k ∈ w, k < 3 ∧ pickY glqGens k = b8 gK k := fun k hk => by
    refine ⟨(hw k hk).1, ?_⟩
    rcases (by have := (hw k hk).1; omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> rfl
  unfold tstK
  rw [sg_beq h (evK_lt _ _ _) (evK_lt _ _ _), evalY_at w hw, evalY_at w hg]

theorem lv_eq {MT : Nat → Nat} {SG : Nat} (h : allN 256 (sigQ MT SG) = true) {k : Nat}
    (hk : k < 3) : glqLevel (TBL MT 256) k = lvK SG k := by
  unfold glqLevel lvK
  refine List.filter_congr fun x hx => ?_
  rw [List.mem_range] at hx
  have hg : pickY glqGens k = b8 gK k := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> rfl
  have e0 : (x != 0) = Bool.not (Nat.beq x 0) := by
    cases e : Nat.beq x 0
    · simp [Nat.ne_of_beq_eq_false e]
    · simp [Nat.eq_of_beq_eq_true e]
  rw [LyLoop.bAnd_eqP, sg_beq h hx (b8_lt _ _), hg, e0]

theorem lv_lt {SG k x : Nat} (hx : x ∈ lvK SG k) : x < 256 := by
  unfold lvK at hx
  exact List.mem_range.mp (List.mem_filter.mp hx).1

theorem fm_congr {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp),
      fm_congr fun y hy => h y (by simp [hy])]

theorem fm_filter {α β : Type} (p : α → Bool) (f : α → List β) :
    ∀ l : List α, (l.filter p).flatMap f = l.flatMap fun x => if p x = true then f x else []
  | [] => rfl
  | x :: l => by
    rw [List.filter_cons, List.flatMap_cons]
    by_cases hp : p x = true
    · rw [if_pos hp, if_pos hp, List.flatMap_cons, fm_filter p f l]
    · rw [if_neg hp, if_neg hp, List.nil_append, fm_filter p f l]

theorem fm_map_eq {α β : Type} {p q : α → Bool} {f g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → (∀ x ∈ l, f x = g x) →
      (l.filter p).map f = (l.filter q).map g
  | [], _, _ => rfl
  | x :: l, hp, hf => by
    rw [List.filter_cons, List.filter_cons, hp x (by simp)]
    have ih := fm_map_eq (l := l) (fun y hy => hp y (by simp [hy])) (fun y hy => hf y (by simp [hy]))
    by_cases hq : q x = true
    · rw [if_pos hq, if_pos hq, List.map_cons, List.map_cons, hf x (by simp), ih]
    · rw [if_neg hq, if_neg hq, ih]

theorem tests_eq {MT : Nat → Nat} {SG : Nat} (h : allN 256 (sigQ MT SG) = true) {a b c : Nat}
    (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    (glqTests.all fun w => sigT (TBL MT 256) (evalY (TBL MT 256) (a, b, c) w) ==
        sigT (TBL MT 256) (evalY (TBL MT 256) glqGens w)) =
      (grp0 MT SG a && grp1 MT SG (Nat.add a (Nat.mul 256 b)) &&
        grp2a MT SG (Nat.add a (Nat.mul 65536 c)) &&
        grp2b MT SG (Nat.add (Nat.add a (Nat.mul 256 b)) (Nat.mul 65536 c))) := by
  obtain ⟨e0, e1, e2, f0, f1, g0, g2, h0⟩ := b8_three ha hb hc
  simp only [Nat.add_eq, Nat.mul_eq] at e0 e1 e2 f0 f1 g0 g2
  have p0 : pickY (a, b, c) 0 = a := rfl
  have p1 : pickY (a, b, c) 1 = b := rfl
  have p2 : pickY (a, b, c) 2 = c := rfl
  unfold grp0 grp1 grp2a grp2b
  simp only [LyLoop.bAnd_eqP]
  rw [tst_eq h (t := (a, b, c)) [0] (by simp [p0, h0]),
    tst_eq h (t := (a, b, c)) [1] (by simp [p1, f1]),
    tst_eq h (t := (a, b, c)) [0, 1] (by simp [p0, p1, f0, f1]),
    tst_eq h (t := (a, b, c)) [1, 0] (by simp [p0, p1, f0, f1]),
    tst_eq h (t := (a, b, c)) [0, 2] (by simp [p0, p2, g0, g2]),
    tst_eq h (t := (a, b, c)) [2, 0] (by simp [p0, p2, g0, g2]),
    tst_eq h (t := (a, b, c)) [2] (by simp [p2, e2]),
    tst_eq h (t := (a, b, c)) [1, 2] (by simp [p1, p2, e1, e2]),
    tst_eq h (t := (a, b, c)) [2, 1] (by simp [p1, p2, e1, e2]),
    tst_eq h (t := (a, b, c)) [0, 1, 2] (by simp [p0, p1, p2, e0, e1, e2])]
  simp only [glqTests, List.all_cons, List.all_nil, Bool.and_true]
  have r : ∀ x0 x1 x2 x01 x02 x12 x10 x20 x21 x012 : Bool,
      (x0 && (x1 && (x2 && (x01 && (x02 && (x12 && (x10 && (x20 && (x21 && x012))))))))) =
        (x0 && (x1 && (x01 && x10)) && (x02 && x20) && (x2 && (x12 && (x21 && x012)))) := by
    decide
  exact r _ _ _ _ _ _ _ _ _ _

theorem cands_sound {MT : Nat → Nat} {SG : Nat} (h : allN 256 (sigQ MT SG) = true) :
    glqCands (TBL MT 256) = (candsK MT SG).map unpk := by
  have Q := fun {a b c : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) => tests_eq h ha hb hc
  unfold glqCands
  rw [lv_eq h (k := 0) (by decide), lv_eq h (k := 1) (by decide), lv_eq h (k := 2) (by decide)]
  unfold candsK prodL
  simp only [List.filter_flatMap, List.map_flatMap, List.map_map, List.filter_map,
    Function.comp_def]
  rw [fm_filter]
  refine fm_congr fun a ha => ?_
  have ha' := lv_lt ha
  by_cases h0 : grp0 MT SG a = true
  · rw [if_pos h0]
    unfold stage2
    simp only [List.map_flatMap, List.filter_map, List.flatMap_map, List.filter_filter,
      List.map_map, Function.comp_def]
    rw [fm_filter]
    refine fm_congr fun b hb => ?_
    have hb' := lv_lt hb
    by_cases h1 : grp1 MT SG (Nat.add a (Nat.mul 256 b)) = true
    · rw [if_pos h1]
      refine fm_map_eq (fun c hc => ?_) (fun c hc => ?_)
      · rw [Q ha' hb' (lv_lt hc), h0, h1, Bool.true_and, Bool.true_and, Bool.and_comm]
      · obtain ⟨e0, e1, e2, -⟩ := b8_three ha' hb' (lv_lt hc)
        simp only [unpk, e0, e1, e2]
    · rw [if_neg h1, List.map_eq_nil_iff, List.filter_eq_nil_iff]
      intro c hc
      have h1' : grp1 MT SG (Nat.add a (Nat.mul 256 b)) = false := by simpa using h1
      rw [Q ha' hb' (lv_lt hc), h0, h1']
      simp
  · rw [if_neg h0, List.flatMap_eq_nil_iff]
    intro b' hb2
    rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro c hc
    have h0' : grp0 MT SG a = false := by simpa using h0
    rw [Q ha' (lv_lt hb2) (lv_lt hc), h0']
    simp

theorem auts_split {MT : Nat → Nat} {W : List (List Nat)} {p : Nat → Bool} :
    ∀ {C A : List Nat}, autsK MT W C A = true →
    (∀ y ∈ C, critK MT W y = true → p y = true) →
    (∀ y ∈ C, failK MT W y 768 = true → p y = false) → C.filter p = A
  | [], A, h, _, _ => by
    cases A with
    | nil => rfl
    | cons _ _ => exact absurd h (by simp [autsK])
  | y :: C, A, h, hc, hf => by
    have hc' : ∀ z ∈ C, critK MT W z = true → p z = true := fun z hz => hc z (by simp [hz])
    have hf' : ∀ z ∈ C, failK MT W z 768 = true → p z = false := fun z hz => hf z (by simp [hz])
    cases A with
    | nil =>
      have h' : bAnd(failK MT W y 768, autsK MT W C []) = true := h
      obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
      rw [List.filter_cons, hf y (by simp) h1]
      exact auts_split h2 hc' hf'
    | cons a A =>
      have h' : bIf(Nat.beq y a, bAnd(critK MT W y, autsK MT W C A),
          bAnd(failK MT W y 768, autsK MT W C (a :: A))) = true := h
      cases e : Nat.beq y a
      · rw [e] at h'
        obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
        rw [List.filter_cons, hf y (by simp) h1]
        exact auts_split h2 hc' hf'
      · rw [e] at h'
        obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
        rw [List.filter_cons, hc y (by simp) h1, Nat.eq_of_beq_eq_true e]
        simp only [if_true]
        exact congrArg _ (auts_split h2 hc' hf')

theorem invoCnt_cons (MT : Nat → Nat) (W : List (List Nat)) (P : List Nat) (y : Nat)
    (A : List Nat) : invoCnt MT W P (y :: A) =
      if invoF (fK MT W y) = true then
        (if fixF P (fK MT W y) = true then invoCnt MT W P A + 1 else 1048576)
      else invoCnt MT W P A := by
  change strictN (fK MT W y) (fun F => nIf(invoF F, nIf(fixF P F, Nat.succ (invoCnt MT W P A),
    nat_lit 1048576), invoCnt MT W P A)) = _
  rw [LyLoop.strictN_eqP]
  cases invoF (fK MT W y) <;> cases fixF P (fK MT W y) <;> rfl

theorem invoCnt_big (MT : Nat → Nat) (W : List (List Nat)) (P : List Nat) :
    ∀ A : List Nat, invoCnt MT W P A < 1048576 →
      (∀ y ∈ A, invoF (fK MT W y) = true → fixF P (fK MT W y) = true) ∧
      invoCnt MT W P A = (A.filter fun y => invoF (fK MT W y)).length
  | [], _ => ⟨by simp, rfl⟩
  | y :: A, h => by
    rw [invoCnt_cons] at h ⊢
    by_cases h1 : invoF (fK MT W y) = true
    · rw [if_pos h1] at h ⊢
      by_cases h2 : fixF P (fK MT W y) = true
      · rw [if_pos h2] at h ⊢
        obtain ⟨r1, r2⟩ := invoCnt_big MT W P A (by omega)
        refine ⟨?_, ?_⟩
        · intro z hz hzi
          rcases List.mem_cons.mp hz with rfl | hz
          · exact h2
          · exact r1 z hz hzi
        · rw [List.filter_cons, if_pos h1, List.length_cons, r2]
      · rw [if_neg h2] at h
        omega
    · rw [if_neg h1] at h ⊢
      obtain ⟨r1, r2⟩ := invoCnt_big MT W P A h
      refine ⟨?_, ?_⟩
      · intro z hz hzi
        rcases List.mem_cons.mp hz with rfl | hz
        · exact absurd hzi h1
        · exact r1 z hz hzi
      · rw [List.filter_cons, if_neg h1, r2]

theorem invo_sound {MT : Nat → Nat} {W : List (List Nat)} {P A : List Nat}
    (h : Nat.beq (invoCnt MT W P A) 176 = true) :
    (A.filter fun y => invoF (fK MT W y)).length = 176 ∧
      ∀ y ∈ A, invoF (fK MT W y) = true → fixF P (fK MT W y) = true := by
  have e := Nat.eq_of_beq_eq_true h
  obtain ⟨r1, r2⟩ := invoCnt_big MT W P A (by omega)
  exact ⟨r2 ▸ e, r1⟩

end CFSG.KS.SporSch.LyGLQ

end
