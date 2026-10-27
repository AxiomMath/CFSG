module

public import CFSG.Certificates.Kernel.YModel.BfsDefs
public import Mathlib.Data.Finset.Card
import CFSG.Monster.B.Co2.PermArr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KC.YModel.Bfs

open CFSG.YGroups.ModelNative

theorem get_push (a : Array Nat) (v : Nat) {i : Nat} (hi : i < a.size) : (a.push v)[i]! = a[i]! := by
  rw [getElem!_pos (a.push v) i (by simp; omega), getElem!_pos a i hi, Array.getElem_push_lt hi]

theorem get_push_eq (a : Array Nat) (v : Nat) : (a.push v)[a.size]! = v := by
  rw [getElem!_pos (a.push v) a.size (by simp), Array.getElem_push_eq]

theorem get_set (a : Array Nat) (y v : Nat) {i : Nat} (hy : y < a.size) :
    (a.set! y v)[i]! = if i = y then v else a[i]! := by
  simp only [getElem!_def, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h : i = y
  · subst h
    simp [hy]
  · simp [Ne.symm h, h]

theorem Mem.push {pts : Array Nat} {y : Nat} (v : Nat) (h : Mem pts y) : Mem (pts.push v) y := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, by simp; omega, get_push pts v ha⟩

theorem size_lt {sz n y : Nat} {f g : Nat → Nat} (hf : ∀ a < sz, f a < n ∧ g (f a) = a)
    (hy : y < n) (hfy : ∀ a < sz, f a ≠ y) : sz < n := by
  have hinj : Set.InjOn f (Finset.range sz) := fun a ha b hb e => by
    rw [← (hf a (Finset.mem_range.mp ha)).2, ← (hf b (Finset.mem_range.mp hb)).2, e]
  have hsub : insert y ((Finset.range sz).image f) ⊆ Finset.range n := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_range.mpr hy
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_range.mpr (hf a (Finset.mem_range.mp ha)).1
  have hny : y ∉ (Finset.range sz).image f := fun hz => by
    obtain ⟨a, ha, e⟩ := Finset.mem_image.mp hz
    exact hfy a (Finset.mem_range.mp ha) e
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hny, Finset.card_image_of_injOn hinj, Finset.card_range,
    Finset.card_range] at this
  omega

variable {n root : Nat} {steps : Array (Array Nat)}

structure Inv (n root : Nat) (steps : Array (Array Nat)) (c : Nat) (s : St) : Prop where
  pos_size : s.1.size = n
  par_size : s.2.2.1.size = s.2.1.size
  lab_size : s.2.2.2.size = s.2.1.size
  pos0 : 0 < s.2.1.size ∧ s.2.1[0]! = root
  size_le : s.2.1.size ≤ n
  pts_lt : ∀ a < s.2.1.size, s.2.1[a]! < n ∧ s.1[s.2.1[a]!]! = a
  pos_mem : ∀ y < n, s.1[y]! ≠ n → s.1[y]! < s.2.1.size ∧ s.2.1[s.1[y]!]! = y
  par : ∀ a < s.2.1.size, 0 < a → s.2.2.1[a]! < a ∧ s.2.2.2[a]! < steps.size ∧
    (steps[s.2.2.2[a]!]!)[s.2.1[s.2.2.1[a]!]!]! = s.2.1[a]!
  reach : ∀ a < s.2.1.size, Reach steps root s.2.1[a]!
  closed : ∀ a < c, ∀ j < steps.size, Mem s.2.1 (steps[j]!)[s.2.1[a]!]!
  c_le : c ≤ s.2.1.size

theorem Inv.pos_n {c : Nat} {s : St} (I : Inv n root steps c s) {y : Nat} (hy : y < n) :
    s.1[y]! = n ↔ ¬ Mem s.2.1 y := by
  constructor
  · rintro h ⟨a, ha, rfl⟩
    have := (I.pts_lt a ha).2
    have := I.size_le
    omega
  · intro h
    by_contra h'
    exact h ⟨_, (I.pos_mem y hy h').1, (I.pos_mem y hy h').2⟩

theorem inv_init (hr : root < n) : Inv n root steps 0 (init n root) := by
  have hpos : ∀ y < n, ((Array.replicate n n).set! root 0)[y]! = if y = root then 0 else n := by
    intro y hy
    rw [get_set _ _ _ (by simpa using hr)]
    split
    · rfl
    · rw [getElem!_pos _ _ (by simpa using hy), Array.getElem_replicate]
  refine ⟨by simp [init], rfl, rfl, ⟨by simp [init], rfl⟩, by simp [init]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [init, List.size_toArray, List.length_singleton] at ha ⊢
    have : a = 0 := by omega
    subst this
    refine ⟨hr, ?_⟩
    change ((Array.replicate n n).set! root 0)[root]! = 0
    rw [hpos root hr, if_pos rfl]
  · intro y hy h
    simp only [init] at h ⊢
    rw [hpos y hy] at h ⊢
    split at h
    · subst y
      simp
    · exact absurd rfl h
  · intro a ha h0
    simp only [init, List.size_toArray, List.length_singleton] at ha
    omega
  · intro a ha
    simp only [init, List.size_toArray, List.length_singleton] at ha
    have : a = 0 := by omega
    subst this
    exact Reach.root
  · intro a ha
    omega
  · simp [init]

structure InvJ (n root : Nat) (steps : Array (Array Nat)) (c x j : Nat) (s : St) : Prop where
  inv : Inv n root steps c s
  hc : c < s.2.1.size
  hx : s.2.1[c]! = x
  done : ∀ j' < j, j' < steps.size → Mem s.2.1 (steps[j']!)[x]!

theorem innerF_spec (hs : ∀ j < steps.size, ∀ x < n, (steps[j]!)[x]! < n) {c x j : Nat} {s : St}
    (I : InvJ n root steps c x j s) (hj : j < steps.size) :
    ∃ s', innerF n steps c x j s = ForInStep.yield s' ∧ InvJ n root steps c x (j + 1) s' := by
  obtain ⟨I, hc, hx, hd⟩ := I
  have hxn : x < n := hx ▸ (I.pts_lt c hc).1
  have hyn := hs j hj x hxn
  set y := (steps[j]!)[x]! with hy
  unfold innerF
  by_cases hnew : (s.1[y]! == n) = true
  · rw [if_pos hnew]
    refine ⟨_, rfl, ?_⟩
    have hnm : ¬ Mem s.2.1 y := (I.pos_n hyn).mp (beq_iff_eq.mp hnew)
    have hne : ∀ a < s.2.1.size, s.2.1[a]! ≠ y := fun a ha e => hnm ⟨a, ha, e⟩
    have hlt : s.2.1.size < n :=
      size_lt (f := fun a => s.2.1[a]!) (g := fun z => s.1[z]!) I.pts_lt hyn hne
    have hys : y < s.1.size := by rw [I.pos_size]; exact hyn
    have hps : ∀ i < n, (s.1.set! y s.2.1.size)[i]! = if i = y then s.2.1.size else s.1[i]! :=
      fun i _ => get_set _ _ _ hys
    have hpts : ∀ a < s.2.1.size + 1, (s.2.1.push y)[a]! = if a < s.2.1.size then s.2.1[a]! else y := by
      intro a ha
      split
      · exact get_push _ _ ‹_›
      · rw [show a = s.2.1.size by omega, get_push_eq]
    have hsz : (s.2.1.push y).size = s.2.1.size + 1 := by simp
    have hmem : ∀ z, Mem s.2.1 z → Mem (s.2.1.push y) z := fun z hz => hz.push y
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simp [I.pos_size]
    · simp [I.par_size]
    · simp [I.lab_size]
    · refine ⟨by rw [hsz]; omega, ?_⟩
      rw [get_push _ _ I.pos0.1]
      exact I.pos0.2
    · rw [hsz]
      omega
    · intro a ha
      rw [hsz] at ha
      rw [hpts a ha]
      split
      · rename_i ha'
        refine ⟨(I.pts_lt a ha').1, ?_⟩
        rw [hps _ (I.pts_lt a ha').1, if_neg (hne a ha')]
        exact (I.pts_lt a ha').2
      · refine ⟨hyn, ?_⟩
        rw [hps y hyn, if_pos rfl]
        omega
    · intro z hz h
      rw [hps z hz] at h ⊢
      split at h
      · rename_i e
        subst e
        rw [if_pos rfl, hsz, hpts _ (by omega), if_neg (by omega)]
        exact ⟨by omega, rfl⟩
      · rw [if_neg ‹_›, hsz]
        obtain ⟨h1, h2⟩ := I.pos_mem z hz h
        refine ⟨by omega, ?_⟩
        rw [hpts _ (by omega), if_pos h1]
        exact h2
    · intro a ha h0
      rw [hsz] at ha
      by_cases ha' : a < s.2.1.size
      · rw [get_push _ _ (by rw [I.par_size]; exact ha'), get_push _ _ (by rw [I.lab_size]; exact ha'),
          get_push _ _ ha']
        obtain ⟨p1, p2, p3⟩ := I.par a ha' h0
        refine ⟨p1, p2, ?_⟩
        rw [get_push _ _ (by omega)]
        exact p3
      · have e : a = s.2.1.size := by omega
        subst e
        rw [← I.par_size, get_push_eq, I.par_size, ← I.lab_size, get_push_eq, I.lab_size,
          get_push_eq, get_push _ _ hc, hx]
        exact ⟨hc, hj, rfl⟩
    · intro a ha
      rw [hsz] at ha
      rw [hpts a ha]
      split
      · exact I.reach a ‹_›
      · rw [hy, ← hx]
        exact Reach.step j hj (I.reach c hc)
    · intro a ha j' hj'
      rw [get_push _ _ (by have := I.c_le; omega)]
      exact hmem _ (I.closed a ha j' hj')
    · rw [hsz]
      have := I.c_le
      omega
    · rw [hsz]
      omega
    · rw [get_push _ _ hc, hx]
    · intro j' hj' hj's
      by_cases e : j' = j
      · subst e
        exact ⟨s.2.1.size, by rw [hsz]; omega, by rw [get_push_eq]⟩
      · exact hmem _ (hd j' (by omega) hj's)
  · rw [if_neg hnew]
    refine ⟨_, rfl, ⟨I, hc, hx, ?_⟩⟩
    intro j' hj' hj's
    by_cases e : j' = j
    · subst e
      by_contra hm
      exact hnew (beq_iff_eq.mpr ((I.pos_n hyn).mpr hm))
    · exact hd j' (by omega) hj's

theorem inner_loop (hs : ∀ j < steps.size, ∀ x < n, (steps[j]!)[x]! < n) {c x : Nat} :
    ∀ (r j : Nat) (s : St), j + r = steps.size → InvJ n root steps c x j s →
      InvJ n root steps c x steps.size (forIn (m := Id) (List.range' j r) s (innerF n steps c x))
  | 0, j, s, hr, I => by
    rw [List.range'_zero, List.forIn_nil]
    rw [Nat.add_zero] at hr
    rw [← hr]
    exact I
  | r + 1, j, s, hr, I => by
    obtain ⟨s', e, I'⟩ := innerF_spec hs I (by omega)
    rw [List.range'_succ, List.forIn_cons, e]
    exact inner_loop hs r (j + 1) s' (by omega) I'

theorem outerF_spec (hs : ∀ j < steps.size, ∀ x < n, (steps[j]!)[x]! < n) {c : Nat} {s : St}
    (I : Inv n root steps c s) :
    (c < s.2.1.size ∧ ∃ s', outerF n steps c s = ForInStep.yield s' ∧ Inv n root steps (c + 1) s') ∨
      (s.2.1.size ≤ c ∧ outerF n steps c s = ForInStep.done s) := by
  unfold outerF
  simp only [Prod.mk.eta]
  by_cases hc : c < s.2.1.size
  · left
    rw [if_pos hc]
    refine ⟨hc, _, rfl, ?_⟩
    have J := inner_loop (root := root) hs (c := c) (x := s.2.1[c]!) steps.size 0 s (by omega)
      ⟨I, hc, rfl, fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩
    obtain ⟨I', hc', hx', hd'⟩ := J
    refine ⟨I'.pos_size, I'.par_size, I'.lab_size, I'.pos0, I'.size_le, I'.pts_lt, I'.pos_mem, I'.par,
      I'.reach, fun a ha j hj => ?_, by omega⟩
    by_cases e : a = c
    · subst e
      rw [hx']
      exact hd' j hj hj
    · exact I'.closed a (by omega) j hj
  · right
    rw [if_neg hc]
    exact ⟨by omega, rfl⟩

theorem outer_loop (hs : ∀ j < steps.size, ∀ x < n, (steps[j]!)[x]! < n) :
    ∀ (r c : Nat) (s : St), c + r = n → Inv n root steps c s →
      ∃ s', forIn (m := Id) (List.range' c r) s (outerF n steps) = s' ∧
        Inv n root steps s'.2.1.size s'
  | 0, c, s, hr, I => by
    refine ⟨s, by rw [List.range'_zero, List.forIn_nil]; rfl, ?_⟩
    have h1 := I.c_le
    have h2 := I.size_le
    have e : s.2.1.size = c := by omega
    rw [e]
    exact I
  | r + 1, c, s, hr, I => by
    rw [List.range'_succ, List.forIn_cons]
    rcases outerF_spec hs I with ⟨-, s', e, I'⟩ | ⟨hle, e⟩
    · rw [e]
      exact outer_loop hs r (c + 1) s' (by omega) I'
    · rw [e]
      refine ⟨s, rfl, ?_⟩
      have e' : s.2.1.size = c := by have := I.c_le; omega
      rw [e']
      exact I

theorem orbitSearch_spec (hr : root < n) (hs : ∀ j < steps.size, ∀ x < n, (steps[j]!)[x]! < n) :
    orbitOK n root steps (orbitSearch n root steps) = true ∧
      (∀ a < (orbitSearch n root steps).pts.size, ∀ b < (orbitSearch n root steps).pts.size,
        (orbitSearch n root steps).pts[a]! = (orbitSearch n root steps).pts[b]! → a = b) ∧
      ∀ y, Mem (orbitSearch n root steps).pts y ↔ Reach steps root y := by
  obtain ⟨s, e, I⟩ := outer_loop (root := root) hs n 0 (init n root) (by omega) (inv_init hr)
  rw [orbitSearch_eq, e]
  dsimp only
  refine ⟨?_, ?_, fun y => ⟨?_, ?_⟩⟩
  · unfold orbitOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, CFSG.Monster.B.Co2.allLt_iff,
      Bool.or_eq_true]
    refine ⟨⟨⟨I.pos0.1, I.pos0.2⟩, fun a ha => ⟨(I.pts_lt a ha).1, (I.pts_lt a ha).2⟩⟩, ?_⟩
    intro a ha
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · exact Or.inl h0
    · obtain ⟨p1, p2, p3⟩ := I.par a ha h0
      exact Or.inr ⟨⟨p1, p2⟩, p3⟩
  · intro a ha b hb e
    rw [← (I.pts_lt a ha).2, ← (I.pts_lt b hb).2, e]
  · rintro ⟨a, ha, rfl⟩
    exact I.reach a ha
  · intro hR
    induction hR with
    | root => exact ⟨0, I.pos0.1, I.pos0.2⟩
    | step j hj _ ih =>
      obtain ⟨a, ha, rfl⟩ := ih
      exact I.closed a ha j hj

end CFSG.KC.YModel.Bfs

end
