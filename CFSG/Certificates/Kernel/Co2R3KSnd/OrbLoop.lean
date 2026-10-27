module

public import Certificates.Data.CFSGNative.Co2Rank3.Orbits
public import CFSG.Certificates.Kernel.Fi22LH.Loops
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KC.Co2R3.Snd

open CFSG.Sporadic.Co2Rank3.Native CFSG.KS.Fi22LH

@[expose] def key (m : Nat) (D P V pos : Nat → Nat) (y : Nat) : Nat :=
  if D y = 1 then pos y * (m + 1) else pos (P y) * (m + 1) + V y + 1

structure Facts (n m : Nat) (T : Nat → Nat → Nat) (L D P V pts pos : Nat → Nat) : Prop where
  pts_lt : ∀ i < n, pts i < n
  pos_pts : ∀ i < n, pos (pts i) = i
  dep_pos : ∀ y < n, 1 ≤ D y
  root : ∀ y < n, D y = 1 → L y = y ∧ P y = 0 ∧ V y = 0 ∧ ∀ v < y, pos v < pos y
  step : ∀ y < n, D y ≠ 1 → V y < m ∧ P y < n ∧ T (V y) (P y) = y ∧ L y = L (P y) ∧
    D y = D (P y) + 1 ∧ pos (P y) < pos y
  key_lt : ∀ i, i + 1 < n → key m D P V pos (pts i) < key m D P V pos (pts (i + 1))
  edge : ∀ k < m, ∀ x < n, T k x < n → (D (T k x) = 1 → pos (T k x) ≤ pos x) ∧
    (D (T k x) ≠ 1 → key m D P V pos (T k x) ≤ pos x * (m + 1) + k + 1)

private abbrev St4 : Type := Array Nat × Array Nat × Array Nat × Array Nat

private abbrev St5 : Type := Array Nat × Array Nat × Array Nat × Array Nat × Array Nat

private abbrev St6 : Type := Array Nat × Array Nat × Array Nat × Array Nat × Array Nat × Nat

private def kBody (n : Nat) (gens : Array (Array Nat)) (r x k : Nat) (s : St5) :
    Id (ForInStep St5) :=
  if (decide ((gens[k]!)[x]! < n) && s.2.1[(gens[k]!)[x]!]! == 0) = true then
    pure (ForInStep.yield (s.1.set! ((gens[k]!)[x]!) r,
      s.2.1.set! ((gens[k]!)[x]!) (s.2.1[x]! + 1), s.2.2.1.set! ((gens[k]!)[x]!) x,
      s.2.2.2.1.set! ((gens[k]!)[x]!) k, s.2.2.2.2.push ((gens[k]!)[x]!)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

private def qBody (n : Nat) (gens : Array (Array Nat)) (r : Nat) (_ : Nat) (s : St6) :
    Id (ForInStep St6) :=
  if s.2.2.2.2.2 < s.2.2.2.2.1.size then do
    let t ← forIn (List.range' 0 gens.size) ((s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1) : St5)
      (kBody n gens r (s.2.2.2.2.1[s.2.2.2.2.2]!))
    pure (ForInStep.yield (t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2, s.2.2.2.2.2 + 1))
  else pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2))

private def rBody (n : Nat) (gens : Array (Array Nat)) (r : Nat) (s : St4) :
    Id (ForInStep St4) :=
  if (s.2.1[r]! == 0) = true then do
    let t ← forIn (List.range' 0 n)
      ((s.1.set! r r, s.2.1.set! r 1, s.2.2.1, s.2.2.2, #[r], 0) : St6) (qBody n gens r)
    pure (ForInStep.yield (t.1, t.2.1, t.2.2.1, t.2.2.2.1))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

private theorem orbitSearch_eq_loop (n : Nat) (gens : Array (Array Nat)) :
    orbitSearch n gens = Id.run (forIn (List.range' 0 n)
      ((Array.replicate n n, Array.replicate n 0, Array.replicate n 0, Array.replicate n 0) : St4)
      (rBody n gens)) := by
  unfold orbitSearch
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl


private theorem getSet {xs : Array Nat} {i j : Nat} (hi : i < xs.size) (hj : j < xs.size)
    (v : Nat) : (xs.set! i v)[j]! = if i = j then v else xs[j]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ j (by rw [Array.size_setIfInBounds]; exact hj)]
  by_cases e : i = j
  · subst e
    rw [if_pos rfl, Array.getElem_setIfInBounds_self]
  · rw [if_neg e, Array.getElem_setIfInBounds_ne hj e, getElem!_pos xs j hj]

private theorem sizeSet (xs : Array Nat) (i v : Nat) : (xs.set! i v).size = xs.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

private theorem getPushLt (xs : Array Nat) (x : Nat) {i : Nat} (h : i < xs.size) :
    (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos (xs.push x) i (by rw [Array.size_push]; omega), getElem!_pos xs i h,
    Array.getElem_push_lt h]

private theorem getPushEq (xs : Array Nat) (x : Nat) : (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]

private theorem getReplicate {n z v : Nat} (hz : z < n) : (Array.replicate n v)[z]! = v := by
  rw [getElem!_pos _ z (by rw [Array.size_replicate]; exact hz), Array.getElem_replicate]

private theorem lstep_yield {β : Type} {I Q : β → Prop} {b : β} (h : I b) :
    LStep I Q (pure (ForInStep.yield b) : Id (ForInStep β)) := h

private theorem lstep_done {β : Type} {I Q : β → Prop} {b : β} (h : Q b) :
    LStep I Q (pure (ForInStep.done b) : Id (ForInStep β)) := h

section

variable {n m : Nat} {T : Nat → Nat → Nat} {L D P V pts pos : Nat → Nat}

private theorem pos_lt (hF : Facts n m T L D P V pts pos) {y : Nat} (hy : y < n) :
    pos y < n ∧ pts (pos y) = y := by
  let f : Fin n → Fin n := fun i => ⟨pts i.val, hF.pts_lt i.val i.isLt⟩
  have hinj : Function.Injective f := by
    intro a b e
    have e' : pts a.val = pts b.val := congrArg Fin.val e
    apply Fin.ext
    rw [← hF.pos_pts a.val a.isLt, ← hF.pos_pts b.val b.isLt, e']
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hinj ⟨y, hy⟩
  have e : pts i.val = y := congrArg Fin.val hi
  rw [← e, hF.pos_pts i.val i.isLt]
  exact ⟨i.isLt, rfl⟩

private theorem key_mono (hF : Facts n m T L D P V pts pos) {i j : Nat} (hij : i < j)
    (hj : j < n) : key m D P V pos (pts i) < key m D P V pos (pts j) := by
  induction j with
  | zero => exact absurd hij (Nat.not_lt_zero i)
  | succ j ih =>
    rcases Nat.lt_or_ge i j with h | h
    · exact Nat.lt_trans (ih h (by omega)) (hF.key_lt j hj)
    · have e : i = j := by omega
      subst e
      exact hF.key_lt i hj

private theorem eq_of_key (hF : Facts n m T L D P V pts pos) {i j : Nat} (hi : i < n)
    (hj : j < n) (h : key m D P V pos (pts i) = key m D P V pos (pts j)) : i = j := by
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · exact absurd h (Nat.ne_of_lt (key_mono hF h' hj))
  · exact h'
  · exact absurd h.symm (Nat.ne_of_lt (key_mono hF h' hi))

private theorem slot_eq {a b c d M : Nat} (hc : c < M) (hd : d < M) (h : a * M + c = b * M + d) :
    a = b ∧ c = d := by
  have h1 : (a * M + c) % M = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have h2 : (b * M + d) % M = d := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]
  have e2 : c = d := by rw [← h1, h, h2]
  subst e2
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel h), rfl⟩

private theorem key_root {y : Nat} (h : D y = 1) : key m D P V pos y = pos y * (m + 1) := by
  unfold key
  rw [if_pos h]

private theorem key_step {y : Nat} (h : D y ≠ 1) :
    key m D P V pos y = pos (P y) * (m + 1) + V y + 1 := by
  unfold key
  rw [if_neg h]

private theorem key_slot (hF : Facts n m T L D P V pts pos) {z p k : Nat} (hz : z < n)
    (hk : k < m) (h : key m D P V pos z = p * (m + 1) + k + 1) :
    D z ≠ 1 ∧ pos (P z) = p ∧ V z = k := by
  by_cases hd : D z = 1
  · rw [key_root hd] at h
    have := (slot_eq (a := pos z) (b := p) (M := m + 1) (c := 0) (d := k + 1) (by omega)
      (by omega) (by omega)).2
    exact absurd this (by omega)
  · rw [key_step hd] at h
    have hv := (hF.step z hz hd).1
    obtain ⟨e1, e2⟩ := slot_eq (a := pos (P z)) (b := p) (M := m + 1) (c := V z + 1)
      (d := k + 1) (by omega) (by omega) (by omega)
    exact ⟨hd, e1, by omega⟩

private def Ent (n : Nat) (pos : Nat → Nat) (c : Nat) (f : Nat → Nat) (d : Nat)
    (xs : Array Nat) : Prop :=
  xs.size = n ∧ ∀ z < n, xs[z]! = if pos z < c then f z else d

private abbrev Arr (n : Nat) (L D P V pos : Nat → Nat) (c : Nat) (la de pa va : Array Nat) :
    Prop :=
  Ent n pos c L n la ∧ Ent n pos c D 0 de ∧ Ent n pos c P 0 pa ∧ Ent n pos c V 0 va

private abbrev Bd (n m : Nat) (D P V pts pos : Nat → Nat) (c B : Nat) : Prop :=
  c ≤ n ∧ ∀ j < n, (j < c ↔ key m D P V pos (pts j) < B)

private abbrev Que (L pts : Nat → Nat) (r s c : Nat) (q : Array Nat) : Prop :=
  s < c ∧ q.size = c - s ∧ (∀ j < c - s, q[j]! = pts (s + j)) ∧
    ∀ j, s ≤ j → j < c → L (pts j) = r

private abbrev KInv (n m : Nat) (L D P V pts pos : Nat → Nat) (r s p k : Nat) (t : St5) : Prop :=
  ∃ c, p < c ∧ Arr n L D P V pos c t.1 t.2.1 t.2.2.1 t.2.2.2.1 ∧ Que L pts r s c t.2.2.2.2 ∧
    Bd n m D P V pts pos c (p * (m + 1) + k + 1)

private abbrev QInv (n m : Nat) (L D P V pts pos : Nat → Nat) (r s i : Nat) (t : St6) : Prop :=
  t.2.2.2.2.2 = i ∧ ∃ c, s + i ≤ c ∧ Arr n L D P V pos c t.1 t.2.1 t.2.2.1 t.2.2.2.1 ∧
    Que L pts r s c t.2.2.2.2.1 ∧ (s + i < c → Bd n m D P V pts pos c ((s + i) * (m + 1) + 1)) ∧
    (s + i = c → Bd n m D P V pts pos c (c * (m + 1)))

private abbrev QPost (n m : Nat) (L D P V pts pos : Nat → Nat) (s : Nat) (t : St6) : Prop :=
  ∃ c, s < c ∧ Arr n L D P V pos c t.1 t.2.1 t.2.2.1 t.2.2.2.1 ∧
    Bd n m D P V pts pos c (c * (m + 1))

private abbrev RInv (n m : Nat) (L D P V pts pos : Nat → Nat) (r : Nat) (t : St4) : Prop :=
  ∃ c, Arr n L D P V pos c t.1 t.2.1 t.2.2.1 t.2.2.2 ∧ Bd n m D P V pts pos c (c * (m + 1)) ∧
    ∀ v < r, pos v < c

private theorem ent_init {f : Nat → Nat} (d : Nat) : Ent n pos 0 f d (Array.replicate n d) :=
  ⟨Array.size_replicate, fun z hz => by rw [getReplicate hz, if_neg (Nat.not_lt_zero _)]⟩

private theorem ent_set (hF : Facts n m T L D P V pts pos) {c d y v : Nat} {f : Nat → Nat}
    {xs : Array Nat} (h : Ent n pos c f d xs) (hy : y < n) (hc : pos y = c) (hv : v = f y) :
    Ent n pos (c + 1) f d (xs.set! y v) := by
  obtain ⟨hs, he⟩ := h
  refine ⟨by rw [sizeSet, hs], fun z hz => ?_⟩
  rw [getSet (by rw [hs]; exact hy) (by rw [hs]; exact hz)]
  by_cases e : y = z
  · subst e
    rw [if_pos rfl, if_pos (by omega), hv]
  · rw [if_neg e, he z hz]
    have hne : pos z ≠ c := fun h' =>
      e (by rw [← (pos_lt hF hy).2, ← (pos_lt hF hz).2, hc, h'])
    by_cases h1 : pos z < c
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]

private theorem ent_keep (hF : Facts n m T L D P V pts pos) {c d y : Nat} {f : Nat → Nat}
    {xs : Array Nat} (h : Ent n pos c f d xs) (hy : y < n) (hc : pos y = c) (hv : d = f y) :
    Ent n pos (c + 1) f d xs := by
  obtain ⟨hs, he⟩ := h
  refine ⟨hs, fun z hz => ?_⟩
  rw [he z hz]
  by_cases e : y = z
  · subst e
    rw [if_neg (by omega), if_pos (by omega), hv]
  · have hne : pos z ≠ c := fun h' =>
      e (by rw [← (pos_lt hF hy).2, ← (pos_lt hF hz).2, hc, h'])
    by_cases h1 : pos z < c
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]

private theorem ent_full (hF : Facts n m T L D P V pts pos) {d : Nat} {f : Nat → Nat}
    {xs : Array Nat} (h : Ent n pos n f d xs) : xs = Array.ofFn (n := n) fun i => f i.val := by
  apply Array.ext (by rw [h.1, Array.size_ofFn])
  intro i hi1 _
  have hin : i < n := h.1 ▸ hi1
  rw [Array.getElem_ofFn, ← getElem!_pos xs i hi1, h.2 i hin, if_pos (pos_lt hF hin).1]

private theorem bd_succ (hF : Facts n m T L D P V pts pos) {c b : Nat}
    (hB : Bd n m D P V pts pos c (b * (m + 1))) (hbc : b < c) :
    Bd n m D P V pts pos c (b * (m + 1) + 1) := by
  obtain ⟨hcn, hBi⟩ := hB
  refine ⟨hcn, fun j hj => ⟨fun h => by have := (hBi j hj).1 h; omega, fun h => ?_⟩⟩
  rcases Nat.lt_or_ge (key m D P V pos (pts j)) (b * (m + 1)) with h1 | h1
  · exact (hBi j hj).2 h1
  · have hk : key m D P V pos (pts j) = b * (m + 1) := by omega
    have hz := hF.pts_lt j hj
    by_cases hd : D (pts j) = 1
    · rw [key_root hd, hF.pos_pts j hj] at hk
      have := Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) hk
      omega
    · rw [key_step hd] at hk
      have hv := (hF.step _ hz hd).1
      have := (slot_eq (M := m + 1) (c := V (pts j) + 1) (d := 0) (by omega) (by omega)
        (by rw [Nat.add_zero, ← Nat.add_assoc]; exact hk)).2
      omega

private theorem bd_next (hF : Facts n m T L D P V pts pos) {c p : Nat}
    (hB : Bd n m D P V pts pos c (p * (m + 1) + m + 1)) :
    Bd n m D P V pts pos c ((p + 1) * (m + 1)) := by
  have e : (p + 1) * (m + 1) = p * (m + 1) + m + 1 := by
    rw [Nat.add_mul p 1 (m + 1), Nat.one_mul, Nat.add_assoc]
  rw [e]
  exact hB

private theorem kStep (hF : Facts n m T L D P V pts pos) {gens : Array (Array Nat)}
    (hT : ∀ k < m, ∀ x < n, (gens[k]!)[x]! = T k x) {r s p k : Nat} (hk : k < m) (hsp : s ≤ p)
    {Q : St5 → Prop} {t : St5} (hI : KInv n m L D P V pts pos r s p k t) :
    LStep (KInv n m L D P V pts pos r s p (k + 1)) Q (kBody n gens r (pts p) k t) := by
  obtain ⟨c, hpc, ⟨hEl, hEd, hEp, hEv⟩, ⟨hsc, hqs, hqe, hql⟩, hcn, hBi⟩ := hI
  have hpn : p < n := by omega
  have hx : pts p < n := hF.pts_lt p hpn
  have hxp : pos (pts p) = p := hF.pos_pts p hpn
  have hy := hT k hk (pts p) hx
  unfold kBody
  rw [hy]
  by_cases hc : (decide (T k (pts p) < n) && t.2.1[T k (pts p)]! == 0) = true
  · rw [if_pos hc]
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨hyn, hd0⟩ := hc
    obtain ⟨he1, he2⟩ := hF.edge k hk (pts p) hx hyn
    have hdy : ¬ pos (T k (pts p)) < c := by
      intro hlt
      rw [hEd.2 _ hyn, if_pos hlt] at hd0
      have := hF.dep_pos _ hyn
      omega
    obtain ⟨hpy, hpty⟩ := pos_lt hF hyn
    have hkB : p * (m + 1) + k + 1 ≤ key m D P V pos (T k (pts p)) := by
      have := (hBi _ hpy).not.1 hdy
      rw [hpty] at this
      omega
    have hdne : D (T k (pts p)) ≠ 1 := by
      intro hd1
      have h1 := he1 hd1
      rw [hxp] at h1
      rw [key_root hd1] at hkB
      have h2 : pos (T k (pts p)) * (m + 1) ≤ p * (m + 1) := Nat.mul_le_mul_right (m + 1) h1
      omega
    have hkey : key m D P V pos (T k (pts p)) = p * (m + 1) + k + 1 := by
      have := he2 hdne
      rw [hxp] at this
      omega
    have hposy : pos (T k (pts p)) = c := by
      by_contra hne
      have hcy : c < pos (T k (pts p)) := by omega
      have h1 := key_mono hF hcy hpy
      rw [hpty, hkey] at h1
      exact (hBi c (by omega)).not.1 (Nat.lt_irrefl c) h1
    obtain ⟨-, hPy, hVy⟩ := key_slot hF hyn hk hkey
    obtain ⟨-, hPn, -, hLy, hDy, -⟩ := hF.step _ hyn hdne
    have hPx : P (T k (pts p)) = pts p := by
      rw [← (pos_lt hF hPn).2, hPy]
    have hdx : t.2.1[pts p]! = D (pts p) := by rw [hEd.2 _ hx, if_pos (by omega)]
    have hLr : L (T k (pts p)) = r := by rw [hLy, hPx, hql p hsp hpc]
    refine lstep_yield ⟨c + 1, by omega, ⟨ent_set hF hEl hyn hposy hLr.symm,
      ent_set hF hEd hyn hposy (by rw [hdx, hDy, hPx]), ent_set hF hEp hyn hposy hPx.symm,
      ent_set hF hEv hyn hposy hVy.symm⟩, ⟨by omega, ?_, ?_, ?_⟩, by omega, fun j hj => ?_⟩
    · dsimp only
      rw [Array.size_push, hqs]
      omega
    · intro j hj
      dsimp only
      rcases Nat.lt_or_ge j (c - s) with hj' | hj'
      · rw [getPushLt _ _ (by rw [hqs]; exact hj'), hqe j hj']
      · have ej : j = t.2.2.2.2.size := by rw [hqs]; omega
        rw [ej, getPushEq, hqs, Nat.add_sub_cancel' (by omega : s ≤ c), ← hposy, hpty]
    · intro j h1 h2
      rcases Nat.lt_or_ge j c with h3 | h3
      · exact hql j h1 h3
      · have e : j = c := by omega
        rw [e, ← hposy, hpty, hLr]
    · constructor
      · intro h1
        rcases Nat.lt_or_ge j c with h2 | h2
        · have := (hBi j hj).1 h2
          omega
        · have e : j = c := by omega
          rw [e, ← hposy, hpty, hkey]
          omega
      · intro h1
        rcases Nat.lt_or_ge (key m D P V pos (pts j)) (p * (m + 1) + k + 1) with h2 | h2
        · have := (hBi j hj).2 h2
          omega
        · have e : key m D P V pos (pts j) = key m D P V pos (pts c) := by
            rw [← hposy, hpty, hkey]
            omega
          have := eq_of_key hF hj (by omega) e
          omega
  · rw [if_neg hc]
    refine lstep_yield ⟨c, hpc, ⟨hEl, hEd, hEp, hEv⟩, ⟨hsc, hqs, hqe, hql⟩, hcn, fun j hj => ?_⟩
    constructor
    · intro h1
      have := (hBi j hj).1 h1
      omega
    · intro h1
      by_contra h2
      have h3 := (hBi j hj).not.1 h2
      have hkey : key m D P V pos (pts j) = p * (m + 1) + k + 1 := by omega
      have hz := hF.pts_lt j hj
      obtain ⟨hdz, hPz, hVz⟩ := key_slot hF hz hk hkey
      obtain ⟨-, hPn, hTz, -, -, -⟩ := hF.step _ hz hdz
      have hPx : P (pts j) = pts p := by rw [← (pos_lt hF hPn).2, hPz]
      rw [hVz, hPx] at hTz
      apply hc
      rw [hTz, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      refine ⟨hz, ?_⟩
      rw [hEd.2 _ hz, if_neg (by rw [hF.pos_pts j hj]; omega)]

private theorem qStep (hF : Facts n m T L D P V pts pos) {gens : Array (Array Nat)}
    (hT : ∀ k < m, ∀ x < n, (gens[k]!)[x]! = T k x) (hgs : gens.size = m) {r s i : Nat}
    {t : St6} (hI : QInv n m L D P V pts pos r s i t) :
    LStep (QInv n m L D P V pts pos r s (i + 1)) (QPost n m L D P V pts pos s)
      (qBody n gens r i t) := by
  obtain ⟨hhi, c, hsic, hA, ⟨hsc, hqs, hqe, hql⟩, hB1, hB2⟩ := hI
  by_cases hlt : t.2.2.2.2.2 < t.2.2.2.2.1.size
  · have hic : s + i < c := by
      rw [hqs, hhi] at hlt
      omega
    have hx : t.2.2.2.2.1[t.2.2.2.2.2]! = pts (s + i) := by
      rw [hhi]
      exact hqe i (by omega)
    obtain ⟨u, hu, hK⟩ : ∃ u : St5, forIn (List.range' 0 gens.size)
        ((t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1) : St5) (kBody n gens r (pts (s + i))) = u ∧
        KInv n m L D P V pts pos r s (s + i) m u := by
      refine ⟨_, rfl, ?_⟩
      rw [hgs]
      exact range'_loop (KInv n m L D P V pts pos r s (s + i))
        (KInv n m L D P V pts pos r s (s + i) m) (kBody n gens r (pts (s + i))) m 0 _
        (fun q b _ hq hb => kStep hF hT (by omega) (by omega) hb)
        (fun b hb => by rwa [Nat.zero_add] at hb)
        ⟨c, hic, hA, ⟨hsc, hqs, hqe, hql⟩, hB1 hic⟩
    have hstep : qBody n gens r i t =
        pure (ForInStep.yield (u.1, u.2.1, u.2.2.1, u.2.2.2.1, u.2.2.2.2, t.2.2.2.2.2 + 1)) := by
      simp only [qBody, hlt, ↓reduceIte, hx, hu] <;> rfl
    rw [hstep]
    obtain ⟨c', hpc', hA', hQ', hB'⟩ := hK
    have hB'' := bd_next hF hB'
    have e : s + (i + 1) = s + i + 1 := by omega
    refine lstep_yield ⟨by rw [hhi], c', by omega, hA', hQ', fun h => ?_, fun h => ?_⟩
    · rw [e]
      exact bd_succ hF hB'' (by omega)
    · rw [show c' * (m + 1) = (s + i + 1) * (m + 1) by rw [← h, e]]
      exact hB''
  · have hstep : qBody n gens r i t = pure (ForInStep.done
        (t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) := by
      simp only [qBody, hlt, ↓reduceIte] <;> rfl
    rw [hstep]
    have hsi : s + i = c := by
      rw [hqs, hhi] at hlt
      omega
    exact lstep_done ⟨c, hsc, hA, hB2 hsi⟩

private theorem rStep (hF : Facts n m T L D P V pts pos) {gens : Array (Array Nat)}
    (hT : ∀ k < m, ∀ x < n, (gens[k]!)[x]! = T k x) (hgs : gens.size = m) {r : Nat}
    (hr : r < n) {Q : St4 → Prop} {t : St4} (hI : RInv n m L D P V pts pos r t) :
    LStep (RInv n m L D P V pts pos (r + 1)) Q (rBody n gens r t) := by
  obtain ⟨c, ⟨hEl, hEd, hEp, hEv⟩, ⟨hcn, hBi⟩, hlow⟩ := hI
  by_cases hd : (t.2.1[r]! == 0) = true
  · have hd0 : t.2.1[r]! = 0 := beq_iff_eq.1 hd
    have hrc : ¬ pos r < c := by
      intro h
      rw [hEd.2 r hr, if_pos h] at hd0
      have := hF.dep_pos r hr
      omega
    have hcn' : c < n := by
      have := (pos_lt hF hr).1
      omega
    have hz := hF.pts_lt c hcn'
    have hzp := hF.pos_pts c hcn'
    have hroot : D (pts c) = 1 := by
      by_contra hne
      obtain ⟨hv, -, -, -, -, hposP⟩ := hF.step _ hz hne
      have hk := key_step (m := m) (P := P) (V := V) (pos := pos) hne
      have h1 := (hBi c hcn').not.1 (Nat.lt_irrefl c)
      rw [hzp] at hposP
      have h2 : (pos (P (pts c)) + 1) * (m + 1) ≤ c * (m + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul (pos (P (pts c))) 1 (m + 1), Nat.one_mul] at h2
      omega
    obtain ⟨hLz, hPz, hVz, hlowz⟩ := hF.root _ hz hroot
    have hrz : r = pts c := by
      rcases Nat.lt_trichotomy r (pts c) with h | h | h
      · have := hlowz r h
        rw [hzp] at this
        exact absurd this hrc
      · exact h
      · have := hlow (pts c) h
        rw [hzp] at this
        exact absurd this (Nat.lt_irrefl c)
    subst hrz
    have hBd : Bd n m D P V pts pos (c + 1) (c * (m + 1) + 1) := by
      refine ⟨by omega, fun j hj => ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
      · rcases Nat.lt_or_ge j c with h2 | h2
        · have := (hBi j hj).1 h2
          omega
        · have e : j = c := by omega
          rw [e, key_root hroot, hzp]
          omega
      · rcases Nat.lt_or_ge (key m D P V pos (pts j)) (c * (m + 1)) with h2 | h2
        · have := (hBi j hj).2 h2
          omega
        · have e : key m D P V pos (pts j) = key m D P V pos (pts c) := by
            rw [key_root hroot, hzp]
            omega
          have := eq_of_key hF hj hcn' e
          omega
    have hQ0 : QInv n m L D P V pts pos (pts c) c 0
        ((t.1.set! (pts c) (pts c), t.2.1.set! (pts c) 1, t.2.2.1, t.2.2.2, #[pts c], 0) : St6) := by
      refine ⟨rfl, c + 1, by omega, ⟨ent_set hF hEl hz hzp hLz.symm,
        ent_set hF hEd hz hzp hroot.symm, ent_keep hF hEp hz hzp hPz.symm,
        ent_keep hF hEv hz hzp hVz.symm⟩, ⟨by omega, ?_, ?_, ?_⟩, fun _ => ?_, fun h => ?_⟩
      · show #[pts c].size = c + 1 - c
        rw [Nat.add_sub_cancel_left]
        rfl
      · intro j hj
        have e : j = 0 := by omega
        subst e
        rfl
      · intro j h1 h2
        have e : j = c := by omega
        rw [e]
        exact hLz
      · exact hBd
      · exact absurd h (by omega)
    obtain ⟨u, hu, hQ⟩ : ∃ u : St6, forIn (List.range' 0 n)
        ((t.1.set! (pts c) (pts c), t.2.1.set! (pts c) 1, t.2.2.1, t.2.2.2, #[pts c], 0) : St6)
        (qBody n gens (pts c)) = u ∧ QPost n m L D P V pts pos c u := by
      refine ⟨_, rfl, range'_loop (QInv n m L D P V pts pos (pts c) c)
        (QPost n m L D P V pts pos c) (qBody n gens (pts c)) n 0 _
        (fun q b _ _ hb => qStep hF hT hgs hb) (fun b hb => ?_) hQ0⟩
      obtain ⟨-, c', h1, hA', ⟨hsc', -⟩, hB1', hB2'⟩ := hb
      rcases Nat.lt_or_ge (c + (0 + n)) c' with h2 | h2
      · exact absurd (hB1' h2).1 (by omega)
      · exact ⟨c', hsc', hA', hB2' (by omega)⟩
    have hstep : rBody n gens (pts c) t =
        pure (ForInStep.yield (u.1, u.2.1, u.2.2.1, u.2.2.2.1)) := by
      simp only [rBody, hd, ↓reduceIte, hu] <;> rfl
    rw [hstep]
    obtain ⟨c', hcc', hA', hB'⟩ := hQ
    refine lstep_yield ⟨c', hA', hB', fun v hv => ?_⟩
    rcases Nat.lt_or_ge v (pts c) with h | h
    · have := hlow v h
      omega
    · have e : v = pts c := by omega
      rw [e, hzp]
      exact hcc'
  · have hstep : rBody n gens r t = pure (ForInStep.yield (t.1, t.2.1, t.2.2.1, t.2.2.2)) := by
      simp only [rBody, hd, ↓reduceIte] <;> rfl
    rw [hstep]
    have hrc : pos r < c := by
      by_contra h
      apply hd
      rw [beq_iff_eq, hEd.2 r hr, if_neg h]
    refine lstep_yield ⟨c, ⟨hEl, hEd, hEp, hEv⟩, ⟨hcn, hBi⟩, fun v hv => ?_⟩
    rcases Nat.lt_or_ge v r with h | h
    · exact hlow v h
    · have e : v = r := by omega
      rw [e]
      exact hrc

end

theorem orbitSearch_eq_of_facts {n m : Nat} {gens : Array (Array Nat)} {T : Nat → Nat → Nat}
    {L D P V pts pos : Nat → Nat} (hgs : gens.size = m)
    (hT : ∀ k < m, ∀ x < n, (gens[k]!)[x]! = T k x) (hF : Facts n m T L D P V pts pos) :
    orbitSearch n gens = (Array.ofFn (n := n) fun i => L i.val,
      Array.ofFn (n := n) fun i => D i.val, Array.ofFn (n := n) fun i => P i.val,
      Array.ofFn (n := n) fun i => V i.val) := by
  rw [orbitSearch_eq_loop]
  obtain ⟨t, ht, h⟩ : ∃ t : St4, forIn (List.range' 0 n)
      ((Array.replicate n n, Array.replicate n 0, Array.replicate n 0, Array.replicate n 0) : St4)
      (rBody n gens) = t ∧ RInv n m L D P V pts pos n t :=
    ⟨_, rfl, range'_loop (RInv n m L D P V pts pos) (RInv n m L D P V pts pos n) (rBody n gens)
      n 0 _ (fun r b _ hr hb => rStep hF hT hgs (by omega) hb)
      (fun b hb => by rwa [Nat.zero_add] at hb)
      ⟨0, ⟨ent_init n, ent_init 0, ent_init 0, ent_init 0⟩,
        ⟨Nat.zero_le n, fun j _ => ⟨fun h => absurd h (Nat.not_lt_zero j), fun h => by omega⟩⟩,
        fun v hv => absurd hv (Nat.not_lt_zero v)⟩⟩
  rw [ht]
  obtain ⟨c, ⟨hEl, hEd, hEp, hEv⟩, ⟨hcn, -⟩, hlow⟩ := h
  have hc : c = n := by
    rcases Nat.lt_or_ge c n with h | h
    · have := hlow (pts c) (hF.pts_lt c h)
      rw [hF.pos_pts c h] at this
      exact absurd this (Nat.lt_irrefl c)
    · omega
  rw [hc] at hEl hEd hEp hEv
  show t = _
  rw [show t = (t.1, t.2.1, t.2.2.1, t.2.2.2) from rfl, ent_full hF hEl, ent_full hF hEd,
    ent_full hF hEp, ent_full hF hEv]

end CFSG.KC.Co2R3.Snd

end
