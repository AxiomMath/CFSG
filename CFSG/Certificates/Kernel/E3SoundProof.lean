module

public import CFSG.Certificates.Kernel.E3Sound
import CFSG.Certificates.Kernel.Co3BfsSound
import CFSG.Certificates.Kernel.Spor.KeyBfsGen
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Data.Finset.Card
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentRigidCheckInputs
public import Certificates.Data.Kernel.E3
import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
import CFSG.Sporadic.Schreier.MathieuOddCoreWords

namespace CFSG.KC.E3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.KC.Child3
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident
open CFSG.KS.KeyBfsG
open CFSG.KS.KeyBfs (forIn_range'_yield push_lt push_eq)

abbrev Cn3 (X : ℕ) : Prop := canonK 276 9 (mask 9) (276 * 9) X = true

theorem strictB_e3 (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem unpack_get3 (P : ℕ) {p : ℕ} (hp : p < 276) : (unpack 276 9 P)[p]! = pg 9 (mask 9) P p := by
  rw [unpack, getElem!_pos _ p (by simpa using hp), Array.getElem_ofFn]

theorem pg_lt3 {P : ℕ} (h : Cn3 P) {p : ℕ} (hp : p < 276) : pg 9 (mask 9) P p < 276 :=
  Nat.blt_eq.mp (allN_spec (range_of_canonK h) p hp)

theorem compA_get3 (t u : Array ℕ) {p : ℕ} (hp : p < 276) : (compA 276 t u)[p]! = t[u[p]!]! := by
  unfold compA
  rw [getElem!_pos _ p (by rw [Array.size_ofFn]; exact hp), Array.getElem_ofFn]

theorem cmp3 {p q : ℕ} (hp : Cn3 p) (hq : Cn3 q) :
    compA 276 (unpack 276 9 p) (unpack 276 9 q) = unpack 276 9 (pc p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

theorem assoc3 (a b : Array ℕ) {r : ℕ} (hr : Cn3 r) :
    compA 276 a (compA 276 b (unpack 276 9 r)) = compA 276 (compA 276 a b) (unpack 276 9 r) := by
  have e : ∀ i : Fin 276, a[(compA 276 b (unpack 276 9 r))[i.val]!]! =
      (compA 276 a b)[(unpack 276 9 r)[i.val]!]! := by
    intro i
    have hu : (unpack 276 9 r)[i.val]! < 276 := by
      rw [unpack_get3 r i.isLt]
      exact pg_lt3 hr i.isLt
    rw [compA_get3 b _ i.isLt, compA_get3 a b hu]
  unfold compA
  exact congrArg (Array.ofFn (n := 276)) (funext e)

theorem conj3 {g X gi : ℕ} (hg : Cn3 g) (hX : Cn3 X) (hgi : Cn3 gi) :
    compA 276 (unpack 276 9 g) (compA 276 (unpack 276 9 X) (unpack 276 9 gi)) =
      unpack 276 9 (pc (pc g X) gi) := by
  rw [assoc3 _ _ hgi, cmp3 hg hX, cmp3 (CFSG.KC.Co3Bfs.canon_pc hg hX) hgi]

theorem lexLtK_iff3 (a b c d : ℕ) : lexLtK a b c d = true ↔ a < c ∨ (a = c ∧ b < d) := by
  have e1 : Nat.blt a c = decide (a < c) :=
    Bool.eq_iff_iff.mpr (by rw [Nat.blt_eq, decide_eq_true_iff])
  have e2 : Nat.beq a c = decide (a = c) :=
    Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, decide_eq_true_iff])
  have e3 : Nat.blt b d = decide (b < d) :=
    Bool.eq_iff_iff.mpr (by rw [Nat.blt_eq, decide_eq_true_iff])
  unfold lexLtK
  rw [e1, e2, e3]
  by_cases p : a < c <;> by_cases q : a = c <;> by_cases r : b < d <;> simp [p, q, r]

theorem lget_eq3 : ∀ (L : List ℕ) (i : ℕ), lget L i = L.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => lget_eq3 L i

theorem offR_facts3 {N : ℕ} : ∀ (CS : List ℕ) (s : ℕ) (O : List ℕ),
    List.rec (motive := fun _ => ℕ → List ℕ → Bool)
      (fun s O => bAnd(Nat.beq s N, List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) O))
      (fun c _ ih s O => List.rec (motive := fun _ => Bool) false
        (fun o O' _ => bAnd(Nat.beq o s, ih (Nat.add s c) O')) O) CS s O = true →
    (∀ i < CS.length, O.getD i 0 = s + (CS.take i).sum) ∧ s + CS.sum = N
  | [], s, O, h => by
    obtain ⟨h1, -⟩ := (bAnd_iff _ _).1 h
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero i), by simpa using Nat.eq_of_beq_eq_true h1⟩
  | c :: CS, s, O, h => by
    cases O with
    | nil => exact absurd h Bool.false_ne_true
    | cons o O =>
      obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
      obtain ⟨ih1, ih2⟩ := offR_facts3 CS (s + c) O h2
      refine ⟨fun i hi => ?_, by rw [List.sum_cons, ← ih2]; omega⟩
      rcases i with _ | i
      · simpa using Nat.eq_of_beq_eq_true h1
      · rw [List.getD_cons_succ, ih1 i (by simpa using hi), List.take_succ_cons, List.sum_cons]
        omega

theorem offOK_facts3 {CS OFF : List ℕ} {N : ℕ} (h : offOK CS OFF N = true) :
    (∀ i < CS.length, lget OFF i = (CS.take i).sum) ∧ CS.sum = N := by
  obtain ⟨h1, h2⟩ := offR_facts3 CS 0 OFF h
  exact ⟨fun i hi => by rw [lget_eq3, h1 i hi, Nat.zero_add], by simpa using h2⟩

theorem sum_take_succ3 (CS : List ℕ) {i : ℕ} (hi : i < CS.length) :
    (CS.take (i + 1)).sum = (CS.take i).sum + lget CS i := by
  rw [List.sum_take_succ _ _ hi, lget_eq3, List.getD_eq_getElem _ _ hi]

theorem sum_take_mono3 (CS : List ℕ) {a b : ℕ} (h : a ≤ b) :
    (CS.take a).sum ≤ (CS.take b).sum := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.sum_append]
  omega

theorem sum_take_le3 (CS : List ℕ) (a : ℕ) : (CS.take a).sum ≤ CS.sum := by
  conv_rhs => rw [← List.take_append_drop a CS]
  rw [List.sum_append]
  omega

theorem forIn_sim2 {β γ : Type} : ∀ (n s : ℕ) (Rl : ℕ → β → γ → Prop)
    (f : ℕ → β → Id (ForInStep β)) (g : ℕ → γ → Id (ForInStep γ)),
    (∀ i < n, ∀ b c, Rl i b c → ∃ b' c', f (s + i) b = pure (ForInStep.yield b') ∧
      g (s + i) c = pure (ForInStep.yield c') ∧ Rl (i + 1) b' c') →
    ∀ b c, Rl 0 b c → Rl n (Id.run (forIn (List.range' s n) b f)) (Id.run (forIn (List.range' s n) c g))
  | 0, _, _, _, _, _, _, _, h0 => h0
  | n + 1, s, Rl, f, g, h, b, c, h0 => by
    obtain ⟨b', c', hf, hg, h1⟩ := h 0 (Nat.succ_pos _) b c h0
    rw [Nat.add_zero] at hf hg
    rw [List.range'_succ, List.forIn_cons, List.forIn_cons, hf, hg]
    exact forIn_sim2 n (s + 1) (fun i => Rl (i + 1)) f g (fun i hi b c hr => by
      obtain ⟨b'', c'', e1, e2, e3⟩ := h (i + 1) (by omega) b c hr
      have e : s + 1 + i = s + (i + 1) := by omega
      exact ⟨b'', c'', by rw [e]; exact e1, by rw [e]; exact e2, e3⟩) b' c' h1

theorem fr {β : Type} (n : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β)) :
    forIn [:n] init f = forIn (List.range' 0 n) init f := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]

def bodyI (L G : Array (Array ℕ)) (idx : Array ℕ → ℕ) (k : ℕ) (pc : ℕ × Array ℕ) (i : ℕ)
    (__s : Array ℕ × Array ℕ × Array Bool × Array (ℕ × Array ℕ)) :
    Id (ForInStep (Array ℕ × Array ℕ × Array Bool × Array (ℕ × Array ℕ))) :=
  have ck := __s.1
  have __s := __s.2
  have ci := __s.1
  have __s := __s.2
  have done := __s.1
  have queue := __s.2
  have g := G[i]!
  have p' := compA 276 g (compA 276 L[pc.1]! (invCand 276 g))
  have ip := idx p'
  if (decide (ip < 4608) && !done[ip]!) = true then
    have done := done.set! ip true
    have c' := compA 276 g pc.2
    have ck := ck.set! ip k
    have ci := ci.set! ip (idx (invCand 276 c'))
    have queue := queue.push (ip, c')
    pure (ForInStep.yield (ck, ci, done, queue))
  else pure (ForInStep.yield (ck, ci, done, queue))

def bodyH (L G : Array (Array ℕ)) (idx : Array ℕ → ℕ) (k : ℕ) (_ : ℕ)
    (__s : Array ℕ × Array ℕ × Array Bool × Array (ℕ × Array ℕ) × ℕ) :
    Id (ForInStep (Array ℕ × Array ℕ × Array Bool × Array (ℕ × Array ℕ) × ℕ)) :=
  have ck := __s.1
  have __s := __s.2
  have ci := __s.1
  have __s := __s.2
  have done := __s.1
  have __s := __s.2
  have queue := __s.1
  have q := __s.2
  if q < queue.size then
    have pc := queue[q]!
    have q := q + 1
    do
    let __s ← forIn [:3] (ck, ci, done, queue) (bodyI L G idx k pc)
    have ck : Array ℕ := __s.1
    have __s : Array ℕ × Array Bool × Array (ℕ × Array ℕ) := __s.2
    have ci : Array ℕ := __s.1
    have __s : Array Bool × Array (ℕ × Array ℕ) := __s.2
    have done : Array Bool := __s.1
    have queue : Array (ℕ × Array ℕ) := __s.2
    pure (ForInStep.yield (ck, ci, done, queue, q))
  else pure (ForInStep.yield (ck, ci, done, queue, q))

def bodyO (L G : Array (Array ℕ)) (idx : Array ℕ → ℕ) (tst : Array ℕ → Bool) (j : ℕ)
    (__s : Array ℕ × Array ℕ × Array ℕ × Array Bool) :
    Id (ForInStep (Array ℕ × Array ℕ × Array ℕ × Array Bool)) :=
  have reps := __s.1
  have __s := __s.2
  have ck := __s.1
  have __s := __s.2
  have ci := __s.1
  have done := __s.2
  if (!done[j]! && tst L[j]!) = true then
    have k := reps.size
    have reps := reps.push j
    have done := done.set! j true
    have ck := ck.set! j k
    have queue := #[(j, idA 276)]
    have q := 0
    do
    let __s ← forIn [:4608] (ck, ci, done, queue, q) (bodyH L G idx k)
    have ck : Array ℕ := __s.1
    have __s : Array ℕ × Array Bool × Array (ℕ × Array ℕ) × ℕ := __s.2
    have ci : Array ℕ := __s.1
    have __s : Array Bool × Array (ℕ × Array ℕ) × ℕ := __s.2
    have done : Array Bool := __s.1
    pure (ForInStep.yield (reps, ck, ci, done))
  else pure (ForInStep.yield (reps, ck, ci, done))

def classDataN (L G : Array (Array ℕ)) (idx : Array ℕ → ℕ) (tst : Array ℕ → Bool) :
    Array ℕ × Array ℕ × Array ℕ :=
  (have reps := (#[] : Array ℕ)
    have ck := Array.replicate 4608 0
    have ci := Array.replicate 4608 0
    have done := Array.replicate 4608 false
    do
    let __s ← forIn [:4608] (reps, ck, ci, done) (bodyO L G idx tst)
    have reps : Array ℕ := __s.1
    have __s : Array ℕ × Array ℕ × Array Bool := __s.2
    have ck : Array ℕ := __s.1
    have __s : Array ℕ × Array Bool := __s.2
    have ci : Array ℕ := __s.1
    pure (reps, ck, ci)).run

theorem classDataG_N (L G : Array (Array ℕ)) (idx : Array ℕ → ℕ) (tst : Array ℕ → Bool) :
    classDataG L G idx tst = classDataN L G idx tst := rfl

def stE (L G : Array (Array ℕ)) (idx : Array ℕ → ℕ) (i : ℕ) (x : ℕ × Array ℕ) :
    ℕ × Array ℕ :=
  (idx (compA 276 G[i]! (compA 276 L[x.1]! (invCand 276 G[i]!))), compA 276 G[i]! x.2)

def bodyIT (idx : Array ℕ → ℕ) (k ip : ℕ) (c' : Array ℕ)
    (s : Array ℕ × Array ℕ × Array Bool × Array (ℕ × Array ℕ)) :
    Id (ForInStep (Array ℕ × Array ℕ × Array Bool × Array (ℕ × Array ℕ))) :=
  if (decide (ip < 4608) && !s.2.2.1[ip]!) = true then
    pure (ForInStep.yield (s.1.set! ip k, s.2.1.set! ip (idx (invCand 276 c')),
      s.2.2.1.set! ip true, s.2.2.2.push (ip, c')))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

theorem bodyI_eqT (L G : Array (Array ℕ)) (idx : Array ℕ → ℕ) (k : ℕ) (pc : ℕ × Array ℕ)
    (i : ℕ) (s : Array ℕ × Array ℕ × Array Bool × Array (ℕ × Array ℕ)) :
    bodyI L G idx k pc i s = bodyIT idx k (idx (compA 276 G[i]! (compA 276 L[pc.1]!
      (invCand 276 G[i]!)))) (compA 276 G[i]! pc.2) s := rfl

theorem bodyH_eq (L G : Array (Array ℕ)) (idx : Array ℕ → ℕ) (k x : ℕ)
    (s : Array ℕ × Array ℕ × Array Bool × Array (ℕ × Array ℕ) × ℕ) : bodyH L G idx k x s =
      if s.2.2.2.2 < s.2.2.2.1.size then
        pure (ForInStep.yield
          ((Id.run (forIn (List.range' 0 3) (s.1, s.2.1, s.2.2.1, s.2.2.2.1)
            (bodyI L G idx k s.2.2.2.1[s.2.2.2.2]!))).1,
          (Id.run (forIn (List.range' 0 3) (s.1, s.2.1, s.2.2.1, s.2.2.2.1)
            (bodyI L G idx k s.2.2.2.1[s.2.2.2.2]!))).2.1,
          (Id.run (forIn (List.range' 0 3) (s.1, s.2.1, s.2.2.1, s.2.2.2.1)
            (bodyI L G idx k s.2.2.2.1[s.2.2.2.2]!))).2.2.1,
          (Id.run (forIn (List.range' 0 3) (s.1, s.2.1, s.2.2.1, s.2.2.2.1)
            (bodyI L G idx k s.2.2.2.1[s.2.2.2.2]!))).2.2.2, s.2.2.2.2 + 1))
      else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2)) := by
  unfold bodyH
  simp only [fr]
  rfl

def runC (L G : Array (Array ℕ)) (idx : Array ℕ → ℕ) (k j : ℕ) (ck ci : Array ℕ)
    (done : Array Bool) : Array ℕ × Array ℕ × Array Bool × Array (ℕ × Array ℕ) × ℕ :=
  Id.run (forIn (List.range' 0 4608) (ck.set! j k, ci, done.set! j true, #[(j, idA 276)], 0)
    (bodyH L G idx k))

theorem bodyO_eq (L G : Array (Array ℕ)) (idx : Array ℕ → ℕ) (tst : Array ℕ → Bool) (j : ℕ)
    (s : Array ℕ × Array ℕ × Array ℕ × Array Bool) : bodyO L G idx tst j s =
      if (!s.2.2.2[j]! && tst L[j]!) = true then
        pure (ForInStep.yield (s.1.push j, (runC L G idx s.1.size j s.2.1 s.2.2.1 s.2.2.2).1,
          (runC L G idx s.1.size j s.2.1 s.2.2.1 s.2.2.2).2.1,
          (runC L G idx s.1.size j s.2.1 s.2.2.1 s.2.2.2).2.2.1))
      else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2)) := by
  unfold bodyO
  simp only [fr]
  rfl

theorem classDataN_eq (L G : Array (Array ℕ)) (idx : Array ℕ → ℕ) (tst : Array ℕ → Bool) :
    classDataN L G idx tst =
      ((Id.run (forIn (List.range' 0 4608) ((#[] : Array ℕ), Array.replicate 4608 0,
          Array.replicate 4608 0, Array.replicate 4608 false) (bodyO L G idx tst))).1,
        (Id.run (forIn (List.range' 0 4608) ((#[] : Array ℕ), Array.replicate 4608 0,
          Array.replicate 4608 0, Array.replicate 4608 false) (bodyO L G idx tst))).2.1,
        (Id.run (forIn (List.range' 0 4608) ((#[] : Array ℕ), Array.replicate 4608 0,
          Array.replicate 4608 0, Array.replicate 4608 false) (bodyO L G idx tst))).2.2.1) := by
  unfold classDataN
  simp only [fr, Id.run, bind, pure]

section Inner

variable {L G : Array (Array ℕ)} {idx : Array ℕ → ℕ} {k j cnt : ℕ} {T : ℕ → ℕ × Array ℕ}
  {P L' POS : ℕ → ℕ} {ciV : ℕ → ℕ} {ck0 ci0 : Array ℕ} {done0 : Array Bool}

abbrev Cor (k j : ℕ) (ciV : ℕ → ℕ) (ck0 ci0 : Array ℕ) (done0 : Array Bool)
    (seen : Std.HashSet ℕ) (ck ci : Array ℕ) (done : Array Bool) : Prop :=
  ck.size = 4608 ∧ ci.size = 4608 ∧ done.size = 4608 ∧ ∀ x < 4608,
    (seen.contains x = true → done[x]! = true ∧ ck[x]! = k ∧
      ci[x]! = (if x = j then ci0[x]! else ciV x)) ∧
    (seen.contains x = false → done[x]! = done0[x]! ∧ ck[x]! = ck0[x]! ∧ ci[x]! = ci0[x]!)

theorem inner_step (R : GRec Prod.fst (stE L G idx) 3 (j, idA 276) j cnt (3 * cnt) T P L' POS)
    (hT : ∀ i < cnt, (T i).1 < 4608)
    (hciV : ∀ i, 0 < i → i < cnt → idx (invCand 276 (T i).2) = ciV (T i).1)
    (hd0 : ∀ i < cnt, done0[(T i).1]! = false)
    {h i : ℕ} (hi : i < 3) {g : GSt (ℕ × Array ℕ)}
    {t : Array ℕ × Array ℕ × Array Bool × Array (ℕ × Array ℕ)}
    (hI : AInv Prod.fst 3 cnt (3 * cnt) T P L' (3 * h + i) g) (hq : t.2.2.2 = g.1)
    (hc : Cor k j ciV ck0 ci0 done0 g.2.2.2 t.1 t.2.1 t.2.2.1) (hh : h < g.1.size) :
    ∃ g' t', innerG Prod.fst (stE L G idx) h i g = pure (ForInStep.yield g') ∧
      bodyI L G idx k (T h) i t = pure (ForInStep.yield t') ∧
      AInv Prod.fst 3 cnt (3 * cnt) T P L' (3 * h + (i + 1)) g' ∧ t'.2.2.2 = g'.1 ∧
      Cor k j ciV ck0 ci0 done0 g'.2.2.2 t'.1 t'.2.1 t'.2.2.1 ∧ h < g'.1.size := by
  have hI0 := hI
  obtain ⟨-, -, hget, hC, -⟩ := hI0
  obtain ⟨hK, hle, -⟩ := hC (Or.inr (Nat.le_refl _))
  have hhc : h < cnt := by omega
  have hTh : g.1[h]! = T h := (hget h hh hhc).1
  obtain ⟨s', hs', hI', -⟩ := ainv_inner R hi hh hI
  have he : 3 * h + i < 3 * cnt := by omega
  obtain ⟨hqc, hx, -⟩ := R.close _ he
  have e1 : (3 * h + i) % 3 = i := by omega
  have e2 : (3 * h + i) / 3 = h := by omega
  rw [e1, e2] at hx
  generalize POS (3 * h + i) = q at hqc hx
  have hy : (stE L G idx i (T h)).1 < 4608 := by
    rw [hx]
    exact hT q hqc
  have hy0 : done0[(stE L G idx i (T h)).1]! = false := by
    rw [hx]
    exact hd0 q hqc
  have hy1 : (stE L G idx i (T h)).1 =
      idx (compA 276 G[i]! (compA 276 L[(T h).1]! (invCand 276 G[i]!))) := by
    simp only [stE]
  have hy2 : (stE L G idx i (T h)).2 = compA 276 G[i]! (T h).2 := by
    simp only [stE]
  obtain ⟨hcs, hcis, hds, hcor⟩ := hc
  have hj0 : g.2.2.2.contains j = true := by
    rw [hK]
    exact ⟨0, by omega, by rw [R.root_eq]⟩
  by_cases hcon : g.2.2.2.contains (stE L G idx i (T h)).1 = true
  · have hgi : innerG Prod.fst (stE L G idx) h i g =
        pure (ForInStep.yield (g.1, g.2.1, g.2.2.1, g.2.2.2)) := by
      unfold innerG
      rw [hTh, hcon]
      rfl
    have hdn : t.2.2.1[(stE L G idx i (T h)).1]! = true := ((hcor _ hy).1 hcon).1
    have hbi : bodyI L G idx k (T h) i t = pure (ForInStep.yield (t.1, t.2.1, t.2.2.1, t.2.2.2)) := by
      rw [bodyI_eqT, ← hy1, ← hy2]
      unfold bodyIT
      rw [hdn]
      simp
    have hs'' : s' = (g.1, g.2.1, g.2.2.1, g.2.2.2) := ForInStep.yield.inj (hs'.symm.trans hgi)
    rw [hs''] at hI'
    exact ⟨_, _, hgi, hbi, hI', hq, ⟨hcs, hcis, hds, hcor⟩, hh⟩
  · have hnc : g.2.2.2.contains (stE L G idx i (T h)).1 = false := Bool.eq_false_iff.2 hcon
    have hgi : innerG Prod.fst (stE L G idx) h i g =
        pure (ForInStep.yield (g.1.push (stE L G idx i (T h)), g.2.1.push h, g.2.2.1.push i,
          g.2.2.2.insert (stE L G idx i (T h)).1)) := by
      unfold innerG
      rw [hTh, hnc]
      rfl
    have hdf : t.2.2.1[(stE L G idx i (T h)).1]! = false := by
      rw [((hcor _ hy).2 hnc).1, hy0]
    have hbi : bodyI L G idx k (T h) i t = pure (ForInStep.yield
        (t.1.set! (stE L G idx i (T h)).1 k,
          t.2.1.set! (stE L G idx i (T h)).1 (idx (invCand 276 (stE L G idx i (T h)).2)),
          t.2.2.1.set! (stE L G idx i (T h)).1 true, t.2.2.2.push (stE L G idx i (T h)))) := by
      rw [bodyI_eqT, ← hy1, ← hy2]
      unfold bodyIT
      rw [hdf, decide_eq_true hy]
      simp only [Bool.not_false, Bool.and_self, ↓reduceIte, Prod.mk.eta]
    have hs'' : s' = (g.1.push (stE L G idx i (T h)), g.2.1.push h, g.2.2.1.push i,
        g.2.2.2.insert (stE L G idx i (T h)).1) := ForInStep.yield.inj (hs'.symm.trans hgi)
    rw [hs''] at hI'
    refine ⟨_, _, hgi, hbi, hI', ?_, ?_, ?_⟩
    · dsimp only
      rw [hq]
    · obtain ⟨-, -, hget', hC', -⟩ := hI'
      obtain ⟨-, hle', -⟩ := hC' (Or.inr (Nat.le_refl _))
      dsimp only at hget' hle' ⊢
      rw [Array.size_push] at hle'
      have hm : g.1.size < cnt := by omega
      have hyT : stE L G idx i (T h) = T g.1.size := by
        have := (hget' g.1.size (by rw [Array.size_push]; omega) hm).1
        rwa [push_eq] at this
      have hyj : (stE L G idx i (T h)).1 ≠ j := by
        intro e
        rw [e, hj0] at hnc
        exact Bool.noConfusion hnc
      have hciy : idx (invCand 276 (stE L G idx i (T h)).2) = ciV (stE L G idx i (T h)).1 := by
        rw [hyT]
        exact hciV _ (by omega) hm
      generalize stE L G idx i (T h) = y at hy hyj hciy hnc ⊢
      refine ⟨by rw [Array.size_set!, hcs], by rw [Array.size_set!, hcis],
        by rw [Array.size_set!, hds], fun x hx => ?_⟩
      by_cases hxy : y.1 = x
      · subst hxy
        have hins : (g.2.2.2.insert y.1).contains y.1 = true := by
          rw [Std.HashSet.contains_insert, beq_self_eq_true, Bool.true_or]
        refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun hf => Bool.noConfusion (hins.symm.trans hf)⟩
        · exact Array.getElem!_set!_self _ _ _ (by rw [hds]; exact hy)
        · exact Array.getElem!_set!_self _ _ _ (by rw [hcs]; exact hy)
        · rw [Array.getElem!_set!_self _ _ _ (by rw [hcis]; exact hy), hciy]
          simp only [hyj, ↓reduceIte]
      · have hins : (g.2.2.2.insert y.1).contains x = g.2.2.2.contains x := by
          rw [Std.HashSet.contains_insert, beq_eq_false_iff_ne.2 hxy, Bool.false_or]
        rw [hins, Array.getElem!_set!_ne _ _ _ _ hxy, Array.getElem!_set!_ne _ _ _ _ hxy,
          Array.getElem!_set!_ne _ _ _ _ hxy]
        exact hcor x hx
    · dsimp only
      rw [Array.size_push]
      omega

abbrev RelH (k j cnt : ℕ) (T : ℕ → ℕ × Array ℕ) (P L' : ℕ → ℕ) (ciV : ℕ → ℕ)
    (ck0 ci0 : Array ℕ) (done0 : Array Bool) (h : ℕ) (g : GSt (ℕ × Array ℕ))
    (t : Array ℕ × Array ℕ × Array Bool × Array (ℕ × Array ℕ) × ℕ) : Prop :=
  AInv Prod.fst 3 cnt (3 * cnt) T P L' (3 * h) g ∧ t.2.2.2.1 = g.1 ∧
    t.2.2.2.2 = min h g.1.size ∧ Cor k j ciV ck0 ci0 done0 g.2.2.2 t.1 t.2.1 t.2.2.1

theorem head_step (R : GRec Prod.fst (stE L G idx) 3 (j, idA 276) j cnt (3 * cnt) T P L' POS)
    (hT : ∀ i < cnt, (T i).1 < 4608)
    (hciV : ∀ i, 0 < i → i < cnt → idx (invCand 276 (T i).2) = ciV (T i).1)
    (hd0 : ∀ i < cnt, done0[(T i).1]! = false)
    {h : ℕ} {g : GSt (ℕ × Array ℕ)} {t : Array ℕ × Array ℕ × Array Bool × Array (ℕ × Array ℕ) × ℕ}
    (hr : RelH k j cnt T P L' ciV ck0 ci0 done0 h g t) :
    ∃ g' t', outerG Prod.fst (stE L G idx) 3 h g = pure (ForInStep.yield g') ∧
      bodyH L G idx k h t = pure (ForInStep.yield t') ∧
      RelH k j cnt T P L' ciV ck0 ci0 done0 (h + 1) g' t' := by
  obtain ⟨hI, hq, hqq, hc⟩ := hr
  by_cases hh : h < g.1.size
  · have hqh : t.2.2.2.2 = h := by
      rw [hqq]
      exact Nat.min_eq_left (Nat.le_of_lt hh)
    have hlt : t.2.2.2.2 < t.2.2.2.1.size := by
      rw [hqh, hq]
      exact hh
    have hTh : t.2.2.2.1[t.2.2.2.2]! = T h := by
      rw [hqh, hq]
      obtain ⟨-, -, hget, hC, -⟩ := hI
      obtain ⟨-, hle, -⟩ := hC (Or.inr (Nat.le_refl _))
      exact (hget h hh (by omega)).1
    have hsim := forIn_sim2 3 0 (fun i (b : GSt (ℕ × Array ℕ))
        (c : Array ℕ × Array ℕ × Array Bool × Array (ℕ × Array ℕ)) =>
        AInv Prod.fst 3 cnt (3 * cnt) T P L' (3 * h + i) b ∧ c.2.2.2 = b.1 ∧
          Cor k j ciV ck0 ci0 done0 b.2.2.2 c.1 c.2.1 c.2.2.1 ∧ h < b.1.size)
      (innerG Prod.fst (stE L G idx) h) (bodyI L G idx k (T h))
      (fun i hi b c hr => by
        rw [Nat.zero_add]
        exact inner_step R hT hciV hd0 hi hr.1 hr.2.1 hr.2.2.1 hr.2.2.2)
      (g.1, g.2.1, g.2.2.1, g.2.2.2) (t.1, t.2.1, t.2.2.1, t.2.2.2.1)
      ⟨by rw [Nat.add_zero]; exact hI, hq, hc, hh⟩
    obtain ⟨h1, h2, h3, h4⟩ := hsim
    refine ⟨Id.run (forIn (List.range' 0 3) (g.1, g.2.1, g.2.2.1, g.2.2.2)
        (innerG Prod.fst (stE L G idx) h)),
      ((Id.run (forIn (List.range' 0 3) (t.1, t.2.1, t.2.2.1, t.2.2.2.1)
        (bodyI L G idx k (T h)))).1,
      (Id.run (forIn (List.range' 0 3) (t.1, t.2.1, t.2.2.1, t.2.2.2.1)
        (bodyI L G idx k (T h)))).2.1,
      (Id.run (forIn (List.range' 0 3) (t.1, t.2.1, t.2.2.1, t.2.2.2.1)
        (bodyI L G idx k (T h)))).2.2.1,
      (Id.run (forIn (List.range' 0 3) (t.1, t.2.1, t.2.2.1, t.2.2.2.1)
        (bodyI L G idx k (T h)))).2.2.2, h + 1),
      by simp only [outerG, hh, ↓reduceIte], ?_, ?_⟩
    · rw [bodyH_eq]
      simp only [hlt, ↓reduceIte]
      rw [hTh, hqh]
    · refine ⟨by rw [Nat.mul_succ]; exact h1, h2, ?_, h3⟩
      dsimp only
      exact (Nat.min_eq_left (by omega)).symm
  · have hqs : t.2.2.2.2 = g.1.size := by
      rw [hqq]
      exact Nat.min_eq_right (by omega)
    have hnlt : ¬ t.2.2.2.2 < t.2.2.2.1.size := by
      rw [hqs, hq]
      exact Nat.lt_irrefl _
    have hgo : outerG Prod.fst (stE L G idx) 3 h g =
        pure (ForInStep.yield (g.1, g.2.1, g.2.2.1, g.2.2.2)) := by
      simp only [outerG, hh, ↓reduceIte]
    obtain ⟨s', hs', hI'⟩ := ainv_head R hI
    have hs'' : s' = (g.1, g.2.1, g.2.2.1, g.2.2.2) := ForInStep.yield.inj (hs'.symm.trans hgo)
    rw [hs''] at hI'
    refine ⟨_, (t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2), hgo, ?_, hI', hq, ?_, hc⟩
    · rw [bodyH_eq]
      simp only [hnlt, ↓reduceIte]
    · dsimp only
      rw [hqs]
      exact (Nat.min_eq_right (by omega)).symm

theorem class_bfs (R : GRec Prod.fst (stE L G idx) 3 (j, idA 276) j cnt (3 * cnt) T P L' POS)
    (hT : ∀ i < cnt, (T i).1 < 4608)
    (hciV : ∀ i, 0 < i → i < cnt → idx (invCand 276 (T i).2) = ciV (T i).1)
    (hd0 : ∀ i < cnt, done0[(T i).1]! = false)
    (hcs : ck0.size = 4608) (hcis : ci0.size = 4608) (hds : done0.size = 4608) :
    (runC L G idx k j ck0 ci0 done0).1.size = 4608 ∧
      (runC L G idx k j ck0 ci0 done0).2.1.size = 4608 ∧
      (runC L G idx k j ck0 ci0 done0).2.2.1.size = 4608 ∧ ∀ x < 4608,
      ((∃ i < cnt, (T i).1 = x) → (runC L G idx k j ck0 ci0 done0).2.2.1[x]! = true ∧
        (runC L G idx k j ck0 ci0 done0).1[x]! = k ∧
        (runC L G idx k j ck0 ci0 done0).2.1[x]! = (if x = j then ci0[x]! else ciV x)) ∧
      ((¬ ∃ i < cnt, (T i).1 = x) → (runC L G idx k j ck0 ci0 done0).2.2.1[x]! = done0[x]! ∧
        (runC L G idx k j ck0 ci0 done0).1[x]! = ck0[x]! ∧
        (runC L G idx k j ck0 ci0 done0).2.1[x]! = ci0[x]!) := by
  have hc0 := R.cnt_pos
  have hj : j < 4608 := by
    have := hT 0 hc0
    rw [R.root_eq] at this
    exact this
  have hcnt : cnt ≤ 4608 := by
    have hm : Set.MapsTo (fun i => (T i).1) (Finset.range cnt : Set ℕ)
        (Finset.range 4608 : Set ℕ) := by
      intro a ha
      simp only [Finset.coe_range, Set.mem_Iio] at ha ⊢
      exact hT a ha
    have hinj : Set.InjOn (fun i => (T i).1) (Finset.range cnt : Set ℕ) := by
      intro a ha b hb e
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      exact R.inj a ha b hb e
    have := Finset.card_le_card_of_injOn (fun i => (T i).1) hm hinj
    simpa using this
  have hinit : RelH k j cnt T P L' ciV ck0 ci0 done0 0 (initG (j, idA 276) j)
      (ck0.set! j k, ci0, done0.set! j true, #[(j, idA 276)], 0) := by
    refine ⟨by rw [Nat.mul_zero]; exact ainv_init R, rfl, rfl, ?_, ?_, ?_, fun x hx => ?_⟩
    · change (ck0.set! j k).size = 4608
      rw [Array.size_set!, hcs]
    · exact hcis
    · change (done0.set! j true).size = 4608
      rw [Array.size_set!, hds]
    · change (((∅ : Std.HashSet ℕ).insert j).contains x = true → _) ∧
        (((∅ : Std.HashSet ℕ).insert j).contains x = false → _)
      rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
      by_cases e : j = x
      · subst e
        rw [beq_self_eq_true]
        refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun hf => Bool.noConfusion hf⟩
        · exact Array.getElem!_set!_self _ _ _ (by rw [hds]; exact hj)
        · exact Array.getElem!_set!_self _ _ _ (by rw [hcs]; exact hj)
        · simp only [↓reduceIte]
      · rw [beq_eq_false_iff_ne.2 e]
        refine ⟨fun hf => Bool.noConfusion hf, fun _ => ⟨?_, ?_, rfl⟩⟩
        · exact Array.getElem!_set!_ne _ _ _ _ e
        · exact Array.getElem!_set!_ne _ _ _ _ e
  have hsim := forIn_sim2 4608 0 (fun h g t => RelH k j cnt T P L' ciV ck0 ci0 done0 h g t)
    (outerG Prod.fst (stE L G idx) 3) (bodyH L G idx k)
    (fun h _ g t hr => by
      rw [Nat.zero_add]
      exact head_step R hT hciV hd0 hr) _ _ hinit
  obtain ⟨hI, -, -, hcs', hcis', hds', hcor⟩ := hsim
  obtain ⟨-, -, -, hC, hD⟩ := hI
  have hge := hD (by omega)
  obtain ⟨hK, hle, -⟩ := hC (Or.inr (Nat.le_refl _))
  have hK' : ∀ x, (Id.run (forIn (List.range' 0 4608) (initG (j, idA 276) j)
      (outerG Prod.fst (stE L G idx) 3))).2.2.2.contains x = true ↔ ∃ i < cnt, (T i).1 = x := by
    intro x
    rw [hK]
    constructor
    · rintro ⟨i, hi, e⟩
      exact ⟨i, by omega, e⟩
    · rintro ⟨i, hi, e⟩
      exact ⟨i, by omega, e⟩
  refine ⟨hcs', hcis', hds', fun x hx => ⟨fun hin => (hcor x hx).1 ((hK' x).2 hin),
    fun hnin => (hcor x hx).2 (Bool.eq_false_iff.2 fun hc => hnin ((hK' x).1 hc))⟩⟩

end Inner

abbrev OInv (CS OFF : List ℕ) (CI M CV MI : ℕ → ℕ) (N C j : ℕ)
    (s : Array ℕ × Array ℕ × Array ℕ × Array Bool) : Prop :=
  s.1 = ((List.range C).map fun c => M (lget OFF c)).toArray ∧ s.2.1.size = 4608 ∧
    s.2.2.1.size = 4608 ∧ s.2.2.2.size = 4608 ∧ C ≤ CS.length ∧
    (∀ c < C, M (lget OFF c) < j) ∧ (C < CS.length → j ≤ M (lget OFF C)) ∧ ∀ x < 4608,
      ((MI x < N ∧ CI (MI x) < C) → s.2.2.2[x]! = true ∧ s.2.1[x]! = ckF CI MI N x ∧
        s.2.2.1[x]! = ciF CS OFF CI CV MI N x) ∧
      (¬ (MI x < N ∧ CI (MI x) < C) → s.2.2.2[x]! = false ∧ s.2.1[x]! = 0 ∧ s.2.2.1[x]! = 0)

theorem ckF_of {CI MI : ℕ → ℕ} {N x : ℕ} (h : MI x < N) : ckF CI MI N x = CI (MI x) := by
  unfold ckF
  rw [Nat.blt_eq.mpr h]

theorem ckF_not {CI MI : ℕ → ℕ} {N x : ℕ} (h : ¬ MI x < N) : ckF CI MI N x = 0 := by
  unfold ckF
  rw [Bool.eq_false_iff.2 fun e => h (Nat.blt_eq.mp e)]

theorem ciF_rep {CS OFF : List ℕ} {CI CV MI : ℕ → ℕ} {N x : ℕ} (h : MI x < N)
    (e : lget OFF (CI (MI x)) = MI x) : ciF CS OFF CI CV MI N x = 0 := by
  unfold ciF
  rw [Nat.blt_eq.mpr h, e, Nat.beq_refl]

theorem ciF_step {CS OFF : List ℕ} {CI CV MI : ℕ → ℕ} {N x : ℕ} (h : MI x < N)
    (e : lget OFF (CI (MI x)) ≠ MI x) : ciF CS OFF CI CV MI N x = CV (MI x) := by
  unfold ciF
  rw [Nat.blt_eq.mpr h, Bool.eq_false_iff.2 fun b => e (Nat.eq_of_beq_eq_true b)]

theorem ciF_not {CS OFF : List ℕ} {CI CV MI : ℕ → ℕ} {N x : ℕ} (h : ¬ MI x < N) :
    ciF CS OFF CI CV MI N x = 0 := by
  unfold ciF
  rw [Bool.eq_false_iff.2 fun e => h (Nat.blt_eq.mp e)]

theorem lit_get0 {α : Type} [Inhabited α] (a : α) : (#[a] : Array α)[0]! = a := rfl

theorem arr_eq3 {α : Type} [Inhabited α] {A : Array α} {c : ℕ} {f : ℕ → α}
    (hs : A.size = c) (he : ∀ i < c, A[i]! = f i) :
    A = Array.ofFn (n := c) fun k => f k.val := by
  apply Array.ext
  · rw [hs, Array.size_ofFn]
  · intro i h1 h2
    rw [Array.getElem_ofFn, ← getElem!_pos A i h1]
    exact he i (by omega)

end CFSG.KC.E3

public section

namespace CFSG.KC.E3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.KC.Child3
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident
open CFSG.KS.KeyBfsG
open CFSG.KS.KeyBfs (forIn_range'_yield push_lt push_eq)

theorem classData_rec {L G : Array (Array ℕ)} {idx : Array ℕ → ℕ} {tst : Array ℕ → Bool}
    {E GP GIP TB CI M PA LB CC CV K MI : ℕ → ℕ} {CS OFF : List ℕ} {N : ℕ}
    (hL : ∀ j < 4608, L[j]! = unpack 276 9 (E j))
    (hG : ∀ i < 3, G[i]! = unpack 276 9 (GP i) ∧ invCand 276 G[i]! = unpack 276 9 (GIP i))
    (hGc : ∀ i < 3, canonK 276 9 (mask 9) (276 * 9) (GP i) = true ∧
      canonK 276 9 (mask 9) (276 * 9) (GIP i) = true)
    (hidx : ∀ k < 4608, idx (unpack 276 9 (E k)) = k)
    (hE : ∀ k < 4608, canonK 276 9 (mask 9) (276 * 9) (E k) = true)
    (htst : ∀ j < 4608, tst L[j]! = (TB j == 1))
    (hoff : offOK CS OFF N = true)
    (hcs : allN CS.length (fun c => Nat.blt 0 (lget CS c)) = true)
    (hMI : allN 4608 (fun j => bIf(Nat.blt (MI j) N, Nat.beq (M (MI j)) j, true)) = true)
    (hpos : ∀ p < N, cdPosK E GP GIP TB CS OFF CI M PA LB CC CV K MI N p = true)
    (hmem : ∀ j < 4608, cdMemK TB CS OFF CI M MI N j = true) :
    classDataG L G idx tst =
      ((CS.length |> List.range |>.map fun c => M (lget OFF c)).toArray,
        Array.ofFn (n := 4608) (fun j => ckF CI MI N j.val),
        Array.ofFn (n := 4608) (fun j => ciF CS OFF CI CV MI N j.val)) := by
  have hid : unpack 276 9 (pidn 276 9) = idA 276 := idK_sound (by quickRfl)
  obtain ⟨hOFF, hsum⟩ := offOK_facts3 hoff
  have hcs' : ∀ c < CS.length, 0 < lget CS c := fun c hc => Nat.blt_eq.mp (allN_spec hcs c hc)
  have PF : ∀ p < N, CI p < CS.length ∧ lget OFF (CI p) ≤ p ∧
      p - lget OFF (CI p) < lget CS (CI p) ∧ M p < 4608 ∧ MI (M p) = p ∧
      (p - lget OFF (CI p) = 0 → repPos TB CS OFF M CC (CI p) (M p) p = true) ∧
      (p - lget OFF (CI p) ≠ 0 →
        stepPos E GP GIP M PA LB CC CV (lget OFF (CI p)) (p - lget OFF (CI p)) (M p) p = true) ∧
      lexPos PA LB (lget CS (CI p)) (p - lget OFF (CI p)) p = true ∧
      ∀ i < 3, cloPos E GP GIP M PA LB K (lget OFF (CI p)) (lget CS (CI p))
        (p - lget OFF (CI p)) (M p) p i = true := by
    intro p hp
    have h := hpos p hp
    unfold cdPosK at h
    simp only [strictB_e3] at h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h5, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h6, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h7, h8⟩ := (bAnd_iff _ _).1 h
    refine ⟨Nat.blt_eq.mp h1, Nat.le_of_ble_eq_true h2, Nat.blt_eq.mp h3, Nat.blt_eq.mp h4,
      Nat.eq_of_beq_eq_true h5, fun hk => ?_, fun hk => ?_, h7, fun i hi => allN_spec h8 i hi⟩
    · have hb : Nat.beq (Nat.sub p (lget OFF (CI p))) 0 = true := by
        rw [Nat.beq_eq]
        exact hk
      rw [hb] at h6
      exact h6
    · have hb : Nat.beq (Nat.sub p (lget OFF (CI p))) 0 = false :=
        Bool.eq_false_iff.2 fun e => hk (Nat.eq_of_beq_eq_true e)
      rw [hb] at h6
      exact h6
  have hend : ∀ c < CS.length, lget OFF c + lget CS c ≤ N := by
    intro c hc
    rw [hOFF c hc, ← sum_take_succ3 CS hc, ← hsum]
    exact sum_take_le3 CS _
  have huniq : ∀ c < CS.length, ∀ c' < CS.length, ∀ p, lget OFF c ≤ p →
      p < lget OFF c + lget CS c → lget OFF c' ≤ p → p < lget OFF c' + lget CS c' → c = c' := by
    intro c hc c' hc' p h1 h2 h1' h2'
    rw [hOFF c hc] at h1 h2
    rw [hOFF c' hc'] at h1' h2'
    rcases Nat.lt_trichotomy c c' with hlt | heq | hgt
    · have := sum_take_mono3 CS (Nat.succ_le_of_lt hlt)
      rw [sum_take_succ3 CS hc] at this
      omega
    · exact heq
    · have := sum_take_mono3 CS (Nat.succ_le_of_lt hgt)
      rw [sum_take_succ3 CS hc'] at this
      omega
  have hpart : ∀ c < CS.length, ∀ i < lget CS c,
      lget OFF c + i < N ∧ CI (lget OFF c + i) = c := by
    intro c hc i hi
    have hlt : lget OFF c + i < N := by have := hend c hc; omega
    obtain ⟨a1, a2, a3, -⟩ := PF _ hlt
    exact ⟨hlt, (huniq c hc _ a1 _ (by omega) (by omega) a2 (by omega)).symm⟩
  have hrep : ∀ c < CS.length, lget OFF c < N ∧ CI (lget OFF c) = c ∧
      CC (lget OFF c) = pidn 276 9 ∧ TB (M (lget OFF c)) = 1 ∧ M (lget OFF c) < 4608 ∧
      MI (M (lget OFF c)) = lget OFF c ∧
      (c + 1 < CS.length → M (lget OFF c) < M (lget OFF (c + 1))) := by
    intro c hc
    obtain ⟨h1, h2⟩ := hpart c hc 0 (hcs' c hc)
    rw [Nat.add_zero] at h1 h2
    obtain ⟨-, -, -, a4, a5, a6, -⟩ := PF _ h1
    have hr := a6 (by rw [h2]; exact Nat.sub_self _)
    rw [h2] at hr
    unfold repPos at hr
    obtain ⟨r1, hr⟩ := (bAnd_iff _ _).1 hr
    obtain ⟨r2, r3⟩ := (bAnd_iff _ _).1 hr
    refine ⟨h1, h2, Nat.eq_of_beq_eq_true r1, Nat.eq_of_beq_eq_true r2, a4, a5, fun hc1 => ?_⟩
    have hb : Nat.blt (Nat.succ c) CS.length = true := Nat.blt_eq.mpr hc1
    rw [hb] at r3
    dsimp only at r3
    exact Nat.blt_eq.mp r3
  have hmono : ∀ a b, a < b → b < CS.length → M (lget OFF a) < M (lget OFF b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
      · exact Nat.lt_trans (ih h (by omega)) ((hrep b (by omega)).2.2.2.2.2.2 hb)
      · subst h
        exact (hrep a (by omega)).2.2.2.2.2.2 hb
  have hmem' : ∀ j < 4608, (MI j < N → M (MI j) = j) ∧ (TB j = 1 → MI j < N ∧ M (MI j) = j ∧
      M (lget OFF (CI (MI j))) ≤ j) := by
    intro j hj
    have h1 := allN_spec hMI j hj
    have h2 := hmem j hj
    unfold cdMemK at h2
    refine ⟨fun hlt => ?_, fun ht => ?_⟩
    · rw [Nat.blt_eq.mpr hlt] at h1
      dsimp only at h1
      exact Nat.eq_of_beq_eq_true h1
    · have hb : Nat.beq (TB j) 1 = true := by
        rw [Nat.beq_eq]
        exact ht
      rw [hb] at h2
      dsimp only at h2
      rw [strictB_e3] at h2
      obtain ⟨m1, h2⟩ := (bAnd_iff _ _).1 h2
      obtain ⟨m2, m3⟩ := (bAnd_iff _ _).1 h2
      exact ⟨Nat.blt_eq.mp m1, Nat.eq_of_beq_eq_true m2, Nat.le_of_ble_eq_true m3⟩
  have hrec : ∀ c < CS.length, GRec Prod.fst (stE L G idx) 3 (M (lget OFF c), idA 276)
      (M (lget OFF c)) (lget CS c) (3 * lget CS c)
      (fun i => (M (lget OFF c + i), unpack 276 9 (CC (lget OFF c + i))))
      (fun i => if i = 0 then 0 else PA (lget OFF c + i))
      (fun i => if i = 0 then 0 else LB (lget OFF c + i))
      (fun e => K (3 * (lget OFF c + e / 3) + e % 3)) := by
    intro c hc
    have hs0 := hcs' c hc
    obtain ⟨-, -, hCC0, -, -, -, -⟩ := hrep c hc
    have ST : ∀ i, 0 < i → i < lget CS c → PA (lget OFF c + i) < i ∧ LB (lget OFF c + i) < 3 ∧
        stE L G idx (LB (lget OFF c + i)) (M (lget OFF c + PA (lget OFF c + i)),
          unpack 276 9 (CC (lget OFF c + PA (lget OFF c + i)))) =
          (M (lget OFF c + i), unpack 276 9 (CC (lget OFF c + i))) := by
      intro i hi0 hi
      obtain ⟨hlt, hci⟩ := hpart c hc i hi
      obtain ⟨-, -, -, a4, -, -, a7, -⟩ := PF _ hlt
      have hk : lget OFF c + i - lget OFF (CI (lget OFF c + i)) = i := by rw [hci]; omega
      have h := a7 (by rw [hk]; omega)
      rw [hk, hci] at h
      unfold stepPos at h
      simp only [Nat.add_eq] at h
      obtain ⟨s1, h⟩ := (bAnd_iff _ _).1 h
      obtain ⟨s2, h⟩ := (bAnd_iff _ _).1 h
      obtain ⟨s3, h⟩ := (bAnd_iff _ _).1 h
      obtain ⟨s4, -⟩ := (bAnd_iff _ _).1 h
      have hpa : PA (lget OFF c + i) < i := Nat.blt_eq.mp s1
      have hlb : LB (lget OFF c + i) < 3 := Nat.blt_eq.mp s2
      obtain ⟨hpl, -⟩ := hpart c hc _ (by omega : PA (lget OFF c + i) < lget CS c)
      obtain ⟨-, -, -, b4, -⟩ := PF _ hpl
      refine ⟨hpa, hlb, ?_⟩
      unfold stE
      dsimp only
      rw [hL _ b4, (hG _ hlb).2, (hG _ hlb).1,
        conj3 (hGc _ hlb).1 (hE _ b4) (hGc _ hlb).2]
      have e3 := Nat.eq_of_beq_eq_true s3
      unfold cnj at e3
      rw [← e3, hidx _ a4, compEqK_sound (n := 276) (w := 9) s4]
    refine ⟨by omega, hs0, ?_, rfl, rfl, rfl, fun a ha b hb e => ?_, fun i hi0 hi => ?_,
      fun i hi0 hi => ?_, ?_, fun e he => ?_⟩
    · simp only [Nat.add_zero, hCC0, hid]
    · obtain ⟨ha', -⟩ := hpart c hc a ha
      obtain ⟨hb', -⟩ := hpart c hc b hb
      have e' : M (lget OFF c + a) = M (lget OFF c + b) := e
      have := (PF _ ha').2.2.2.2.1
      rw [e', (PF _ hb').2.2.2.2.1] at this
      omega
    · obtain ⟨s1, s2, s3⟩ := ST i hi0 hi
      have hne : i ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      exact ⟨s1, s2, s3.symm⟩
    · obtain ⟨hlt, hci⟩ := hpart c hc i (by omega)
      obtain ⟨-, -, -, -, -, -, -, a8, -⟩ := PF _ hlt
      have hk : lget OFF c + i - lget OFF (CI (lget OFF c + i)) = i := by rw [hci]; omega
      rw [hk, hci] at a8
      unfold lexPos at a8
      have hb0 : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun e => by
        have := Nat.eq_of_beq_eq_true e; omega
      have hb1 : Nat.blt (Nat.succ i) (lget CS c) = true := Nat.blt_eq.mpr (by omega)
      rw [hb0, hb1] at a8
      dsimp only at a8
      have hl := (lexLtK_iff3 _ _ _ _).1 a8
      obtain ⟨-, l1, -⟩ := ST i hi0 (by omega)
      obtain ⟨-, l2, -⟩ := ST (i + 1) (by omega) hi
      have hne : i ≠ 0 := by omega
      have hne' : i + 1 ≠ 0 := by omega
      simp only [hne, hne', ↓reduceIte]
      have e : Nat.succ (lget OFF c + i) = lget OFF c + (i + 1) := rfl
      rw [e] at hl
      omega
    · have hc1 : lget CS c - 1 < lget CS c := by omega
      by_cases h0 : lget CS c - 1 = 0
      · simp only [h0, ↓reduceIte]
        omega
      · obtain ⟨s1, s2, -⟩ := ST _ (by omega) hc1
        simp only [h0, ↓reduceIte]
        omega
    · have hq : e / 3 < lget CS c := by omega
      have hi : e % 3 < 3 := Nat.mod_lt _ (by norm_num)
      obtain ⟨hlt, hci⟩ := hpart c hc _ hq
      obtain ⟨-, -, -, a4, -, -, -, -, a9⟩ := PF _ hlt
      have hk : lget OFF c + e / 3 - lget OFF (CI (lget OFF c + e / 3)) = e / 3 := by
        rw [hci]; omega
      have h := a9 _ hi
      rw [hk, hci] at h
      unfold cloPos at h
      rw [strictB_e3] at h
      simp only [Nat.add_eq, Nat.mul_eq] at h
      dsimp only
      generalize K (3 * (lget OFF c + e / 3) + e % 3) = q at h ⊢
      obtain ⟨c1, h⟩ := (bAnd_iff _ _).1 h
      obtain ⟨c2, c3⟩ := (bAnd_iff _ _).1 h
      have hql : q < lget CS c := Nat.blt_eq.mp c1
      obtain ⟨hqn, -⟩ := hpart c hc q hql
      obtain ⟨-, -, -, b4, -⟩ := PF _ hqn
      refine ⟨hql, ?_, ?_⟩
      · unfold stE
        dsimp only
        rw [hL _ a4, (hG _ hi).2, (hG _ hi).1, conj3 (hGc _ hi).1 (hE _ a4) (hGc _ hi).2]
        have e3 := Nat.eq_of_beq_eq_true c2
        unfold cnj at e3
        rw [← e3]
        exact hidx _ b4
      · by_cases hq0 : q = 0
        · exact Or.inl hq0
        · right
          have hb0 : Nat.beq q 0 = false :=
            Bool.eq_false_iff.2 fun e => hq0 (Nat.eq_of_beq_eq_true e)
          rw [hb0] at c3
          dsimp only at c3
          simp only [hq0, ↓reduceIte]
          obtain ⟨-, hlb, -⟩ := ST q (by omega) hql
          cases hx : lexLtK (e / 3) (e % 3) (PA (lget OFF c + q)) (LB (lget OFF c + q))
          · have := (lexLtK_iff3 _ _ _ _).not.1 (by rw [hx]; exact Bool.false_ne_true)
            omega
          · rw [hx] at c3
            dsimp only at c3
            exact absurd c3 Bool.false_ne_true
  have hO : ∃ C, OInv CS OFF CI M CV MI N C 4608
      (Id.run (forIn (List.range' 0 4608) ((#[] : Array ℕ), Array.replicate 4608 0,
        Array.replicate 4608 0, Array.replicate 4608 false) (bodyO L G idx tst))) := by
    refine forIn_range'_yield 4608 0 _ (bodyO L G idx tst)
      (fun j s => ∃ C, OInv CS OFF CI M CV MI N C j s) (fun j hj s hs => ?_) ⟨0, ?_⟩
    · rw [Nat.zero_add]
      obtain ⟨C, hr, hcks, hcis, hds, hCl, hlo, hhi, hx⟩ := hs
      have htj := htst j hj
      by_cases hb : (!s.2.2.2[j]! && tst L[j]!) = true
      · have hdj : s.2.2.2[j]! = false := by
          cases h' : s.2.2.2[j]!
          · rfl
          · rw [h'] at hb
            simp at hb
        have htj' : TB j = 1 := by
          rw [hdj, htj] at hb
          simpa using hb
        obtain ⟨hmj, hMj, hRj⟩ := (hmem' j hj).2 htj'
        have hCp : C ≤ CI (MI j) := by
          refine Nat.le_of_not_lt fun hlt => ?_
          rw [((hx j hj).1 ⟨hmj, hlt⟩).1] at hdj
          exact Bool.noConfusion hdj
        have hCn := (PF _ hmj).1
        have hCe : CI (MI j) = C := by
          refine Nat.le_antisymm (Nat.le_of_not_lt fun hlt => ?_) hCp
          have := hmono C (CI (MI j)) hlt hCn
          have := hhi (by omega)
          omega
        have hCl' : C < CS.length := by omega
        have hRe : M (lget OFF C) = j := by
          rw [hCe] at hRj
          have := hhi hCl'
          omega
        obtain ⟨hoN, hoC, -, -, hoM, hoMI, hoS⟩ := hrep C hCl'
        have hsz : s.1.size = C := by rw [hr]; simp
        have hbr : bodyO L G idx tst j s = pure (ForInStep.yield (s.1.push j,
            (runC L G idx C j s.2.1 s.2.2.1 s.2.2.2).1,
            (runC L G idx C j s.2.1 s.2.2.1 s.2.2.2).2.1,
            (runC L G idx C j s.2.1 s.2.2.1 s.2.2.2).2.2.1)) := by
          rw [bodyO_eq, hdj, htj, (beq_iff_eq).mpr htj', hsz]
          rfl
        refine ⟨_, hbr, C + 1, ?_⟩
        have R := hrec C hCl'
        rw [hRe] at R
        have hT : ∀ i < lget CS C, (M (lget OFF C + i), unpack 276 9 (CC (lget OFF C + i))).1 <
            4608 := fun i hi => (PF _ (hpart C hCl' i hi).1).2.2.2.1
        have hciV : ∀ i, 0 < i → i < lget CS C →
            idx (invCand 276 (M (lget OFF C + i), unpack 276 9 (CC (lget OFF C + i))).2) =
              (fun x => CV (MI x)) (M (lget OFF C + i), unpack 276 9 (CC (lget OFF C + i))).1 := by
          intro i hi0 hi
          obtain ⟨hlt, hci⟩ := hpart C hCl' i hi
          obtain ⟨-, -, -, -, a5, -, a7, -⟩ := PF _ hlt
          have hk : lget OFF C + i - lget OFF (CI (lget OFF C + i)) = i := by rw [hci]; omega
          have h := a7 (by rw [hk]; omega)
          rw [hk, hci] at h
          unfold stepPos at h
          obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
          obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
          obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
          obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
          obtain ⟨s5, h⟩ := (bAnd_iff _ _).1 h
          obtain ⟨s6, s7⟩ := (bAnd_iff _ _).1 h
          dsimp only
          rw [a5, (invEqK_sound (n := 276) (w := 9) s5).1, ← Nat.eq_of_beq_eq_true s7,
            hidx _ (Nat.blt_eq.mp s6)]
        have hd0 : ∀ i < lget CS C,
            s.2.2.2[(M (lget OFF C + i), unpack 276 9 (CC (lget OFF C + i))).1]! = false := by
          intro i hi
          obtain ⟨hlt, hci⟩ := hpart C hCl' i hi
          obtain ⟨-, -, -, a4, a5, -⟩ := PF _ hlt
          dsimp only
          refine ((hx _ a4).2 fun hh => ?_).1
          rw [a5, hci] at hh
          exact Nat.lt_irrefl _ hh.2
        obtain ⟨z1, z2, z3, z4⟩ := class_bfs (k := C) (ciV := fun x => CV (MI x)) R hT hciV hd0
          hcks hcis hds
        have hin : ∀ x < 4608, ((∃ i < lget CS C, (M (lget OFF C + i),
            unpack 276 9 (CC (lget OFF C + i))).1 = x) ↔ (MI x < N ∧ CI (MI x) = C)) := by
          intro x hx'
          constructor
          · rintro ⟨i, hi, e⟩
            dsimp only at e
            obtain ⟨hlt, hci⟩ := hpart C hCl' i hi
            rw [← e, (PF _ hlt).2.2.2.2.1]
            exact ⟨hlt, hci⟩
          · rintro ⟨hlt, hci⟩
            obtain ⟨a1, a2, a3, -⟩ := PF _ hlt
            rw [hci] at a2 a3
            refine ⟨MI x - lget OFF C, a3, ?_⟩
            dsimp only
            rw [Nat.add_sub_cancel' a2]
            exact (hmem' x hx').1 hlt
        refine ⟨?_, z1, z2, z3, by omega, fun c hc => ?_, fun hc1 => ?_, fun x hx' => ?_⟩
        · dsimp only
          rw [hr, ← hRe, List.push_toArray, List.range_succ, List.map_append]
          rfl
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h | h
          · have := hlo c h
            omega
          · rw [h, hRe]
            omega
        · have := hoS hc1
          omega
        · dsimp only
          obtain ⟨w1, w2⟩ := z4 x hx'
          by_cases hxc : MI x < N ∧ CI (MI x) = C
          · obtain ⟨u1, u2, u3⟩ := w1 ((hin x hx').2 hxc)
            refine ⟨fun _ => ⟨u1, ?_, ?_⟩, fun hn => absurd ⟨hxc.1, by omega⟩ hn⟩
            · rw [u2, ckF_of hxc.1, hxc.2]
            · rw [u3]
              by_cases hxj : x = j
              · subst hxj
                simp only [↓reduceIte]
                rw [((hx _ hx').2 fun hh => by omega).2.2, ciF_rep hxc.1]
                rw [hxc.2, ← hRe, hoMI]
              · simp only [hxj, ↓reduceIte]
                rw [ciF_step hxc.1]
                intro e
                apply hxj
                rw [← (hmem' x hx').1 hxc.1, ← e, hxc.2, hRe]
          · have hnin : ¬ ∃ i < lget CS C, (M (lget OFF C + i),
                unpack 276 9 (CC (lget OFF C + i))).1 = x := fun h => hxc ((hin x hx').1 h)
            obtain ⟨u1, u2, u3⟩ := w2 hnin
            rw [u1, u2, u3]
            constructor
            · intro hh
              exact (hx x hx').1 ⟨hh.1, by
                rcases Nat.lt_succ_iff_lt_or_eq.1 hh.2 with h | h
                · exact h
                · exact absurd ⟨hh.1, h⟩ hxc⟩
            · intro hh
              exact (hx x hx').2 fun h' => hh ⟨h'.1, by omega⟩
      · have hbr : bodyO L G idx tst j s =
            pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2)) := by
          rw [bodyO_eq]
          simp only [hb, Bool.false_eq_true, ↓reduceIte]
        refine ⟨_, hbr, C, hr, hcks, hcis, hds, hCl, fun c hc => by have := hlo c hc; omega,
          fun hc => ?_, hx⟩
        have h1 := hhi hc
        refine Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h1 fun e => hb ?_)
        obtain ⟨hoN, hoC, -, hoT, hoM, hoMI, -⟩ := hrep C hc
        have hj' : M (lget OFF C) = j := e.symm
        rw [hj'] at hoT hoMI
        have hdj : s.2.2.2[j]! = false := ((hx j hj).2 fun hh => by
          rw [hoMI, hoC] at hh
          exact Nat.lt_irrefl _ hh.2).1
        rw [Bool.and_eq_true, hdj, htj]
        exact ⟨rfl, beq_iff_eq.mpr hoT⟩
    · refine ⟨rfl, by simp, by simp, by simp, Nat.zero_le _,
        fun c hc => absurd hc (Nat.not_lt_zero _), fun _ => Nat.zero_le _,
        fun x hx => ⟨fun hh => absurd hh.2 (Nat.not_lt_zero _), fun _ => ⟨?_, ?_, ?_⟩⟩⟩
      · dsimp only
        rw [getElem!_pos _ x (by rw [Array.size_replicate]; exact hx), Array.getElem_replicate]
      · dsimp only
        rw [getElem!_pos _ x (by rw [Array.size_replicate]; exact hx), Array.getElem_replicate]
      · dsimp only
        rw [getElem!_pos _ x (by rw [Array.size_replicate]; exact hx), Array.getElem_replicate]
  obtain ⟨C, hr, hcks, hcis, -, hCl, -, hhi, hx⟩ := hO
  have hCe : C = CS.length := by
    refine Nat.le_antisymm hCl (Nat.le_of_not_lt fun hlt => ?_)
    have := hhi hlt
    have := (hrep C hlt).2.2.2.2.1
    omega
  subst hCe
  rw [classDataG_N, classDataN_eq]
  simp only [Prod.mk.injEq]
  refine ⟨hr, ?_, ?_⟩
  · refine arr_eq3 (f := fun x => ckF CI MI N x) hcks fun x hx' => ?_
    by_cases hm : MI x < N
    · exact ((hx x hx').1 ⟨hm, (PF _ hm).1⟩).2.1
    · rw [((hx x hx').2 fun hh => hm hh.1).2.1, ckF_not hm]
  · refine arr_eq3 (f := fun x => ciF CS OFF CI CV MI N x) hcis fun x hx' => ?_
    by_cases hm : MI x < N
    · exact ((hx x hx').1 ⟨hm, (PF _ hm).1⟩).2.2
    · rw [((hx x hx').2 fun hh => hm hh.1).2.2, ciF_not hm]

theorem sigmaTab_tree {P L : Array ℕ} {Y : Array (Array ℕ)} {PP LL YP DD : ℕ → ℕ}
    (hP : ∀ j < 4608, P[j]! = PP j) (hL : ∀ j < 4608, L[j]! = LL j)
    (hY : ∀ i < 3, Y[i]! = unpack 276 9 (YP i))
    (hYc : ∀ i < 3, canonK 276 9 (mask 9) (276 * 9) (YP i) = true)
    (hD0 : DD 0 = 0)
    (hs : ∀ j, 0 < j → j < 4608 → PP j < j ∧ LL j < 3 ∧ DD j = DD (PP j) + 1) :
    sigmaTabG P L Y =
      Array.ofFn (n := 4608) (fun j => unpack 276 9 (treeP PP LL YP (DD j.val) j.val)) := by
  have hid : unpack 276 9 (pidn 276 9) = idA 276 := idK_sound (by quickRfl)
  have kc : Cn3 (pidn 276 9) := by quickRfl
  have hstep : ∀ j, 0 < j → j < 4608 → treeP PP LL YP (DD j) j =
      pc (treeP PP LL YP (DD (PP j)) (PP j)) (YP (LL j)) := by
    intro j h0 hj
    have hb : Nat.beq j 0 = false := Bool.eq_false_iff.2 fun e => by
      have := Nat.eq_of_beq_eq_true e; omega
    have e : treeP PP LL YP (DD (PP j) + 1) j =
        nIf(Nat.beq j 0, pidn 276 9, pc (treeP PP LL YP (DD (PP j)) (PP j)) (YP (LL j))) := rfl
    rw [(hs j h0 hj).2.2, e, hb]
  have hc' : ∀ m j, j < m → j < 4608 → Cn3 (treeP PP LL YP (DD j) j) := by
    intro m
    induction m with
    | zero => exact fun j hj => absurd hj (Nat.not_lt_zero _)
    | succ m ih =>
      intro j hjm hj
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0
        rw [hD0]
        exact kc
      · obtain ⟨hp, hl, -⟩ := hs j h0 hj
        rw [hstep j h0 hj]
        exact CFSG.KC.Co3Bfs.canon_pc (ih _ (by omega) (by omega)) (hYc _ hl)
  have hc : ∀ j < 4608, Cn3 (treeP PP LL YP (DD j) j) := fun j hj => hc' (j + 1) j (by omega) hj
  have e : sigmaTabG P L Y = Id.run (forIn (List.range' 1 4607) #[idA 276]
      (fun j (T : Array (Array ℕ)) =>
        (pure (ForInStep.yield (T.push (compA 276 T[P[j]!]! Y[L[j]!]!))) :
          Id (ForInStep (Array (Array ℕ)))))) := by
    unfold sigmaTabG
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
      Nat.add_sub_cancel, Nat.div_one]
    rfl
  have inv := forIn_range'_yield 4607 1 #[idA 276]
    (fun j (T : Array (Array ℕ)) =>
      (pure (ForInStep.yield (T.push (compA 276 T[P[j]!]! Y[L[j]!]!))) :
        Id (ForInStep (Array (Array ℕ)))))
    (fun n T => T.size = n + 1 ∧ ∀ i < n + 1, T[i]! = unpack 276 9 (treeP PP LL YP (DD i) i))
    (fun n hn T hT => by
      refine ⟨_, rfl, ?_, fun i hi => ?_⟩
      · rw [Array.size_push, hT.1]
      · have hm0 : 0 < 1 + n := by omega
        have hm : 1 + n < 4608 := by omega
        obtain ⟨hp, hl, -⟩ := hs _ hm0 hm
        rcases Nat.lt_or_ge i (n + 1) with a | a
        · rw [push_lt (by rw [hT.1]; exact a)]
          exact hT.2 i a
        · have ei : i = T.size := by rw [hT.1]; omega
          rw [ei, push_eq, hP _ hm, hL _ hm, hT.2 (PP (1 + n)) (by omega), hY _ hl,
            cmp3 (hc (PP (1 + n)) (by omega)) (hYc _ hl), ← hstep _ hm0 hm, ← ei]
          have e2 : 1 + n = i := by omega
          rw [e2])
    ⟨rfl, fun i hi => by
      have : i = 0 := by omega
      subst this
      have e0 : treeP PP LL YP 0 0 = pidn 276 9 := rfl
      rw [hD0, e0, hid]
      exact lit_get0 _⟩
  rw [e]
  exact arr_eq3 (c := 4608) (f := fun i => unpack 276 9 (treeP PP LL YP (DD i) i)) inv.1 inv.2

end CFSG.KC.E3

end
