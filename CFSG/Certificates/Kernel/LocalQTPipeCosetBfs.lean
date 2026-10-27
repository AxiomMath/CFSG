module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Coset
public import Certificates.Data.Kernel.LocalQT.Pipe
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
import Mathlib.Data.Fintype.Pigeonhole

public section

namespace CFSG.KC.LQT.PPC

open CFSG.QuasithinUnique.Setup.X1 CFSG.KC.LQT.PP

theorem getD_set!_true_iff {vis : Array Bool} {y i : Nat} :
    (vis.set! y true).getD i false = true ↔ (i = y ∧ y < vis.size) ∨ vis.getD i false = true := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
    Array.getD_eq_getD_getElem?]
  by_cases h : y = i
  · subst h
    by_cases hy : y < vis.size <;> simp [hy]
  · have h' : ¬ i = y := fun e => h e.symm
    simp [h, h']

theorem getD_true_eq {vis : Array Bool} {y : Nat} (h : y < vis.size) :
    vis.getD y true = vis.getD y false := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

def unvis (N : Nat) (vis : Array Bool) : Nat :=
  ((Finset.range N).filter fun i => vis.getD i false = false).card

theorem unvis_set {N : Nat} {vis : Array Bool} {y : Nat} (hy : y < N)
    (hv : vis.getD y false = false) (hs : vis.size = N) :
    unvis N (vis.set! y true) + 1 = unvis N vis := by
  unfold unvis
  have hget : ∀ i, (vis.set! y true).getD i false = (decide (i = y) || vis.getD i false) := by
    intro i
    apply Bool.eq_iff_iff.2
    rw [getD_set!_true_iff]
    by_cases h : i = y
    · simp [h, hs, hy]
    · simp [h]
  have e : (Finset.range N).filter (fun i => (vis.set! y true).getD i false = false) =
      ((Finset.range N).filter fun i => vis.getD i false = false).erase y := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, hget]
    by_cases h : i = y <;> by_cases h2 : vis.getD i false = true <;> simp [h, h2]
  rw [e, Finset.card_erase_of_mem]
  · have : 0 < ((Finset.range N).filter fun i => vis.getD i false = false).card :=
      Finset.card_pos.2 ⟨y, by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hy, hv⟩⟩
    omega
  · simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hy, hv⟩

theorem unvis_le (N : Nat) (vis : Array Bool) : unvis N vis ≤ N := by
  unfold unvis
  calc _ ≤ (Finset.range N).card := Finset.card_filter_le _ _
    _ = N := Finset.card_range N

def Inv (N : Nat) (ts : List (Array Nat)) (vis : Array Bool) (q : List Nat) : Prop :=
  vis.size = N ∧ (∀ y ∈ q, y < N ∧ vis.getD y false = true) ∧
    ∀ i < N, vis.getD i false = true →
      i ∈ q ∨ ∀ t ∈ ts, vis.getD (arrImg t i) false = true

def stepF (x : Nat) (acc : Array Bool × List Nat) (t : Array Nat) : Array Bool × List Nat :=
  if acc.1.getD (arrImg t x) true then acc
  else (acc.1.set! (arrImg t x) true, arrImg t x :: acc.2)

def Post (N x : Nat) (l : List (Array Nat)) (vis : Array Bool) (q : List Nat)
    (st : Array Bool × List Nat) : Prop :=
  st.1.size = N ∧ (∀ i, vis.getD i false = true → st.1.getD i false = true) ∧
    (∀ y ∈ q, y ∈ st.2) ∧ (∀ y ∈ st.2, y < N ∧ st.1.getD y false = true) ∧
    (∀ t ∈ l, st.1.getD (arrImg t x) false = true) ∧
    (∀ i, st.1.getD i false = true → vis.getD i false = true ∨ i ∈ st.2) ∧
    st.2.length + unvis N st.1 = q.length + unvis N vis

theorem expand_fold (N : Nat) (ts : List (Array Nat))
    (htab : ∀ t ∈ ts, ∀ i < N, arrImg t i < N) (x : Nat) (hx : x < N) :
    ∀ (l : List (Array Nat)), (∀ t ∈ l, t ∈ ts) → ∀ (vis : Array Bool) (q : List Nat),
      vis.size = N → (∀ y ∈ q, y < N ∧ vis.getD y false = true) →
      Post N x l vis q (l.foldl (stepF x) (vis, q)) := by
  intro l
  induction l with
  | nil =>
    intro _ vis q hs hq
    simp only [List.foldl_nil]
    refine ⟨hs, fun i h => h, fun y h => h, hq, by simp, fun i h => Or.inl h, rfl⟩
  | cons t l ih =>
    intro hl vis q hs hq
    have htl : t ∈ ts := hl t List.mem_cons_self
    have hl' : ∀ t' ∈ l, t' ∈ ts := fun t' ht' => hl t' (List.mem_cons_of_mem t ht')
    have hy : arrImg t x < N := htab t htl x hx
    simp only [List.foldl_cons]
    by_cases hv : vis.getD (arrImg t x) true = true
    · have e : stepF x (vis, q) t = (vis, q) := by simp [stepF, hv]
      rw [e]
      have hv' : vis.getD (arrImg t x) false = true := by
        rwa [getD_true_eq (by omega)] at hv
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ih hl' vis q hs hq
      refine ⟨a1, a2, a3, a4, ?_, a6, a7⟩
      intro t' ht'
      rcases List.mem_cons.1 ht' with rfl | ht'
      · exact a2 _ hv'
      · exact a5 t' ht'
    · have e : stepF x (vis, q) t = (vis.set! (arrImg t x) true, arrImg t x :: q) := by
        simp [stepF, hv]
      rw [e]
      have hv' : vis.getD (arrImg t x) false = false := by
        rw [getD_true_eq (by omega)] at hv
        simpa using hv
      have hs1 : (vis.set! (arrImg t x) true).size = N := by simpa using hs
      have hq1 : ∀ y ∈ arrImg t x :: q,
          y < N ∧ (vis.set! (arrImg t x) true).getD y false = true := by
        intro y hy'
        rcases List.mem_cons.1 hy' with rfl | hy'
        · exact ⟨hy, getD_set!_true_iff.2 (Or.inl ⟨rfl, by omega⟩)⟩
        · exact ⟨(hq y hy').1, getD_set!_true_iff.2 (Or.inr (hq y hy').2)⟩
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ih hl' _ _ hs1 hq1
      have hm : ∀ i, vis.getD i false = true →
          (vis.set! (arrImg t x) true).getD i false = true :=
        fun i h => getD_set!_true_iff.2 (Or.inr h)
      refine ⟨a1, fun i h => a2 i (hm i h), fun y h => a3 y (List.mem_cons_of_mem _ h), a4, ?_, ?_, ?_⟩
      · intro t' ht'
        rcases List.mem_cons.1 ht' with rfl | ht'
        · exact a2 _ (getD_set!_true_iff.2 (Or.inl ⟨rfl, by omega⟩))
        · exact a5 t' ht'
      · intro i h
        rcases a6 i h with h1 | h1
        · rcases getD_set!_true_iff.1 h1 with ⟨rfl, _⟩ | h1
          · exact Or.inr (a3 _ List.mem_cons_self)
          · exact Or.inl h1
        · exact Or.inr h1
      · have := unvis_set hy hv' hs
        rw [a7, List.length_cons]
        omega

theorem bfsAux_closed (N : Nat) (ts : List (Array Nat))
    (htab : ∀ t ∈ ts, ∀ i < N, arrImg t i < N) :
    ∀ (f : Nat) (vis : Array Bool) (q : List Nat), Inv N ts vis q → q.length + unvis N vis ≤ f →
      (∀ i, vis.getD i false = true → (bfsAux ts f vis q).getD i false = true) ∧
      (bfsAux ts f vis q).size = N ∧
      ∀ i < N, (bfsAux ts f vis q).getD i false = true →
        ∀ t ∈ ts, (bfsAux ts f vis q).getD (arrImg t i) false = true := by
  intro f
  induction f with
  | zero =>
    intro vis q hI hf
    have hq : q = [] := List.length_eq_zero_iff.1 (by omega)
    subst hq
    simp only [bfsAux]
    refine ⟨fun i h => h, hI.1, fun i hi h t ht => ?_⟩
    rcases hI.2.2 i hi h with h1 | h1
    · simp at h1
    · exact h1 t ht
  | succ f ih =>
    intro vis q hI hf
    cases q with
    | nil =>
      simp only [bfsAux]
      refine ⟨fun i h => h, hI.1, fun i hi h t ht => ?_⟩
      rcases hI.2.2 i hi h with h1 | h1
      · simp at h1
      · exact h1 t ht
    | cons x q =>
      obtain ⟨hs, hq, hB⟩ := hI
      have hxN : x < N := (hq x List.mem_cons_self).1
      have hq' : ∀ y ∈ q, y < N ∧ vis.getD y false = true :=
        fun y hy => hq y (List.mem_cons_of_mem _ hy)
      have key := expand_fold N ts htab x hxN ts (fun t ht => ht) vis q hs hq'
      have hbf : bfsAux ts (f + 1) vis (x :: q) =
          bfsAux ts f (ts.foldl (stepF x) (vis, q)).1 (ts.foldl (stepF x) (vis, q)).2 := rfl
      rw [hbf]
      generalize ts.foldl (stepF x) (vis, q) = st at key ⊢
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := key
      have hI' : Inv N ts st.1 st.2 := by
        refine ⟨a1, a4, fun i hi h => ?_⟩
        rcases a6 i h with h1 | h1
        · rcases hB i hi h1 with h2 | h2
          · rcases List.mem_cons.1 h2 with rfl | h2
            · exact Or.inr (fun t ht => a5 t ht)
            · exact Or.inl (a3 i h2)
          · exact Or.inr (fun t ht => a2 _ (h2 t ht))
        · exact Or.inl h1
      have hf' : st.2.length + unvis N st.1 ≤ f := by
        rw [a7]; simp only [List.length_cons] at hf; omega
      obtain ⟨b1, b2, b3⟩ := ih st.1 st.2 hI' hf'
      exact ⟨fun i h => b1 i (a2 i h), b2, b3⟩

theorem bfsVis_closed (N : Nat) (ts : List (Array Nat))
    (htab : ∀ t ∈ ts, ∀ i < N, arrImg t i < N) {s : Nat} (hs : s < N) :
    ClosedOK N ts s (bfsVis N ts s) := by
  have hI : Inv N ts ((Array.replicate N false).set! s true) [s] := by
    have hsz : ((Array.replicate N false).set! s true).size = N := by simp
    have hs1 : ((Array.replicate N false).set! s true).getD s false = true :=
      getD_set!_true_iff.2 (Or.inl ⟨rfl, by rw [Array.size_replicate]; exact hs⟩)
    refine ⟨hsz, ?_, ?_⟩
    · intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact ⟨hs, hs1⟩
    · intro i hi h
      rcases getD_set!_true_iff.1 h with ⟨rfl, _⟩ | h
      · exact Or.inl List.mem_cons_self
      · simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h
        by_cases hiN : i < N <;> simp [hiN] at h
  have hf : ([s] : List Nat).length + unvis N ((Array.replicate N false).set! s true) ≤ N + 1 := by
    have := unvis_le N ((Array.replicate N false).set! s true)
    simp only [List.length_singleton]; omega
  obtain ⟨b1, b2, b3⟩ := bfsAux_closed N ts htab (N + 1) _ _ hI hf
  exact ⟨b1 s (getD_set!_true_iff.2 (Or.inl ⟨rfl, by rw [Array.size_replicate]; exact hs⟩)), b3⟩

theorem bfsVis_size (N : Nat) (ts : List (Array Nat))
    (htab : ∀ t ∈ ts, ∀ i < N, arrImg t i < N) {s : Nat} (hs : s < N) :
    (bfsVis N ts s).size = N := by
  have hI : Inv N ts ((Array.replicate N false).set! s true) [s] := by
    have hsz : ((Array.replicate N false).set! s true).size = N := by simp
    have hs1 : ((Array.replicate N false).set! s true).getD s false = true :=
      getD_set!_true_iff.2 (Or.inl ⟨rfl, by rw [Array.size_replicate]; exact hs⟩)
    refine ⟨hsz, ?_, ?_⟩
    · intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact ⟨hs, hs1⟩
    · intro i hi h
      rcases getD_set!_true_iff.1 h with ⟨rfl, _⟩ | h
      · exact Or.inl List.mem_cons_self
      · simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h
        by_cases hiN : i < N <;> simp [hiN] at h
  have hf : ([s] : List Nat).length + unvis N ((Array.replicate N false).set! s true) ≤ N + 1 := by
    have := unvis_le N ((Array.replicate N false).set! s true)
    simp only [List.length_singleton]; omega
  exact (bfsAux_closed N ts htab (N + 1) _ _ hI hf).2.1

theorem bfsVis_getD_iff (N : Nat) (ts : List (Array Nat))
    (htab : ∀ t ∈ ts, ∀ i < N, arrImg t i < N) {s : Nat} (hs : s < N) {i : Nat} (hi : i < N) :
    (bfsVis N ts s).getD i false = true ↔ Reach ts s i := by
  rw [← bfsVis_iff ts s N (bfsVis_closed N ts htab hs) htab hs i]
  exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩

theorem bfsVis_eq_of_reach_iff (N : Nat) (ts us : List (Array Nat))
    (htab : ∀ t ∈ ts, ∀ i < N, arrImg t i < N) (htab' : ∀ t ∈ us, ∀ i < N, arrImg t i < N)
    {s : Nat} (hs : s < N) (h : ∀ i < N, Reach ts s i ↔ Reach us s i) :
    bfsVis N ts s = bfsVis N us s := by
  apply Array.ext
  · rw [bfsVis_size N ts htab hs, bfsVis_size N us htab' hs]
  · intro i hi1 hi2
    have hi : i < N := by rw [bfsVis_size N ts htab hs] at hi1; exact hi1
    have e1 := bfsVis_getD_iff N ts htab hs hi
    have e2 := bfsVis_getD_iff N us htab' hs hi
    have g1 : (bfsVis N ts s).getD i false = (bfsVis N ts s)[i] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi1]; rfl
    have g2 : (bfsVis N us s).getD i false = (bfsVis N us s)[i] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi2]; rfl
    rw [g1] at e1
    rw [g2] at e2
    apply Bool.eq_iff_iff.2
    rw [e1, e2]
    exact h i hi

theorem reach_trans {ts : List (Array Nat)} {s a b : Nat} (h1 : Reach ts s a) (h2 : Reach ts a b) :
    Reach ts s b := by
  induction h2 with
  | base => exact h1
  | step t ht _ ih => exact Reach.step t ht ih

theorem reach_iter {ts : List (Array Nat)} {t : Array Nat} (ht : t ∈ ts) (k a : Nat) :
    Reach ts a ((arrImg t)^[k] a) := by
  induction k with
  | zero => exact Reach.base
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact Reach.step t ht ih

theorem reach_back {N : Nat} {ts : List (Array Nat)} {t : Array Nat} (ht : t ∈ ts)
    (htab : ∀ i < N, arrImg t i < N)
    (hinj : ∀ i < N, ∀ j < N, arrImg t i = arrImg t j → i = j) {i : Nat} (hi : i < N) :
    Reach ts (arrImg t i) i := by
  have hlt : ∀ k x, x < N → (arrImg t)^[k] x < N := by
    intro k
    induction k with
    | zero => intro x hx; exact hx
    | succ k ih => intro x hx; rw [Function.iterate_succ_apply]; exact ih _ (htab x hx)
  have hinjk : ∀ k, ∀ x y, x < N → y < N → (arrImg t)^[k] x = (arrImg t)^[k] y → x = y := by
    intro k
    induction k with
    | zero => intro x y _ _ h; exact h
    | succ k ih =>
      intro x y hx hy h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
      exact hinj x hx y hy (ih _ _ (htab x hx) (htab y hy) h)
  have hN : 0 < N := by omega
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : Nat => (⟨(arrImg t)^[k] i, hlt k i hi⟩ : Fin N))
  have hfab' : (arrImg t)^[a] i = (arrImg t)^[b] i := by simpa using hfab
  have key : ∀ a b : Nat, a < b → (arrImg t)^[a] i = (arrImg t)^[b] i →
      Reach ts (arrImg t i) i := by
    intro a b hlt' h
    obtain ⟨m, rfl⟩ : ∃ m, b = a + (m + 1) := ⟨b - a - 1, by omega⟩
    rw [Function.iterate_add_apply] at h
    have h2 := hinjk a i _ hi (hlt _ i hi) h
    have h3 : (arrImg t)^[m + 1] i = (arrImg t)^[m] (arrImg t i) :=
      Function.iterate_succ_apply _ _ _
    rw [h3] at h2
    have h4 := reach_iter ht m (arrImg t i)
    rwa [← h2] at h4
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact key a b h hfab'
  · exact key b a h hfab'.symm

theorem reach_symm {N : Nat} {ts : List (Array Nat)}
    (htab : ∀ t ∈ ts, ∀ i < N, arrImg t i < N)
    (hinj : ∀ t ∈ ts, ∀ i < N, ∀ j < N, arrImg t i = arrImg t j → i = j) {s i : Nat}
    (hs : s < N) (h : Reach ts s i) : Reach ts i s := by
  have : i < N ∧ Reach ts i s := by
    induction h with
    | base => exact ⟨hs, Reach.base⟩
    | step t ht _ ih =>
      exact ⟨htab t ht _ ih.1, reach_trans (reach_back ht (htab t ht) (hinj t ht) ih.1) ih.2⟩
  exact this.2

theorem reach_mono {ts us : List (Array Nat)} (h : ∀ t ∈ ts, t ∈ us) {s i : Nat}
    (hr : Reach ts s i) : Reach us s i := by
  induction hr with
  | base => exact Reach.base
  | step t ht _ ih => exact Reach.step t (h t ht) ih

theorem shiftLeft_one (i : Nat) : Nat.shiftLeft 1 i = 2 ^ i := by
  change 1 <<< i = 2 ^ i
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem bitK_eq (m i : Nat) : bitK m i = m.testBit i := by
  unfold bitK
  rw [shiftLeft_one]
  change Nat.blt 0 (m &&& 2 ^ i) = _
  apply Bool.eq_iff_iff.2
  rw [Nat.blt_eq]
  constructor
  · intro hp
    by_contra hn
    have hn' : m.testBit i = false := by simpa using hn
    have : m &&& 2 ^ i = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases h : i = j
      · subst h; simp [hn']
      · simp [h]
    omega
  · intro h
    have : (m &&& 2 ^ i).testBit i = true := by
      rw [Nat.testBit_and, Nat.testBit_two_pow]; simp [h]
    rcases Nat.eq_zero_or_pos (m &&& 2 ^ i) with e | e
    · rw [e] at this; simp at this
    · exact e

theorem maskL_testBit (l : List Nat) (i : Nat) : (maskL l).testBit i = true ↔ i ∈ l := by
  induction l with
  | nil => simp [maskL]
  | cons x t ih =>
    have e : maskL (x :: t) = Nat.shiftLeft 1 x ||| maskL t := rfl
    rw [e, Nat.testBit_or, shiftLeft_one, Nat.testBit_two_pow, Bool.or_eq_true, ih]
    simp [eq_comm]

theorem sumL_eq (l : List Nat) : sumL l = l.sum := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have e : sumL (x :: t) = Nat.add x (sumL t) := rfl
    rw [e, ih, List.sum_cons]
    rfl

theorem foldl_count (l : List Nat) (p : Nat → Bool) (c : Nat) :
    l.foldl (fun c i => if p i then c + 1 else c) c = c + (l.filter p).length := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.filter_cons]
    by_cases h : p x = true
    · simp only [h, ite_true, ih, List.length_cons]
      omega
    · simp only [h, ih]
      simp

theorem blkSize_eq' (N : Nat) (b : Array Bool) :
    blkSize N b = ((List.range N).filter fun i => b.getD i false).length := by
  unfold blkSize
  rw [foldl_count]
  simp

theorem popK_eq (N m : Nat) :
    popK N m = ((List.range N).filter fun i => m.testBit i).length := by
  induction N with
  | zero => rfl
  | succ n ih =>
    have e : popK (n + 1) m = Nat.add (popK n m)
        (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 n)))) := rfl
    have e2 : Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 n)) = m.testBit n := bitK_eq m n
    rw [e, e2, ih, List.range_succ, List.filter_append]
    cases h : m.testBit n <;> simp [h]

theorem add_eq_or_add_and (a b : Nat) : a + b = (a ||| b) + (a &&& b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have ih' := ih (a / 2) (by omega) (b / 2)
      have h1 : (a ||| b) / 2 = a / 2 ||| b / 2 := Nat.or_div_two
      have h2 : (a &&& b) / 2 = a / 2 &&& b / 2 := Nat.and_div_two
      have h3 : (a ||| b) % 2 = 1 ↔ a % 2 = 1 ∨ b % 2 = 1 := Nat.or_mod_two_eq_one
      have h4 : (a &&& b) % 2 = 1 ↔ a % 2 = 1 ∧ b % 2 = 1 := Nat.and_mod_two_eq_one
      have e1 := Nat.div_add_mod (a ||| b) 2
      have e2 := Nat.div_add_mod (a &&& b) 2
      have e3 := Nat.div_add_mod a 2
      have e4 := Nat.div_add_mod b 2
      have p1 := Nat.mod_lt (a ||| b) (by decide : 2 > 0)
      have p2 := Nat.mod_lt (a &&& b) (by decide : 2 > 0)
      have p3 := Nat.mod_lt a (by decide : 2 > 0)
      have p4 := Nat.mod_lt b (by decide : 2 > 0)
      by_cases ha2 : a % 2 = 1 <;> by_cases hb2 : b % 2 = 1
      · have x1 := h3.2 (Or.inl ha2)
        have x2 := h4.2 ⟨ha2, hb2⟩
        omega
      · have x1 := h3.2 (Or.inl ha2)
        have x2 : (a &&& b) % 2 ≠ 1 := fun h => hb2 (h4.1 h).2
        omega
      · have x1 := h3.2 (Or.inr hb2)
        have x2 : (a &&& b) % 2 ≠ 1 := fun h => ha2 (h4.1 h).1
        omega
      · have x1 : (a ||| b) % 2 ≠ 1 := fun h => by rcases h3.1 h with h | h <;> contradiction
        have x2 : (a &&& b) % 2 ≠ 1 := fun h => ha2 (h4.1 h).1
        omega

def orL (ms : List Nat) : Nat := ms.foldr (· ||| ·) 0

theorem orL_testBit (ms : List Nat) (i : Nat) :
    (orL ms).testBit i = true ↔ ∃ m ∈ ms, m.testBit i = true := by
  induction ms with
  | nil => simp [orL]
  | cons x t ih =>
    have e : orL (x :: t) = x ||| orL t := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true, ih]
    simp

theorem orL_le_sum (ms : List Nat) : orL ms ≤ ms.sum := by
  induction ms with
  | nil => simp [orL]
  | cons x t ih =>
    have e : orL (x :: t) = x ||| orL t := rfl
    rw [e, List.sum_cons]
    have := add_eq_or_add_and x (orL t)
    omega

theorem pairwise_of_sum_eq_or (ms : List Nat) (h : ms.sum = orL ms) :
    ms.Pairwise (fun a b => a &&& b = 0) := by
  induction ms with
  | nil => exact List.Pairwise.nil
  | cons x t ih =>
    have e : orL (x :: t) = x ||| orL t := rfl
    rw [e, List.sum_cons] at h
    have h1 := add_eq_or_add_and x (orL t)
    have h2 := orL_le_sum t
    have h3 : t.sum = orL t := by omega
    have h4 : x &&& orL t = 0 := by omega
    refine List.Pairwise.cons (fun y hy => ?_) (ih h3)
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hx : x.testBit j = true
    · have hy' : y.testBit j = false := by
        by_contra hc
        have hc' : y.testBit j = true := by simpa using hc
        have : (orL t).testBit j = true := (orL_testBit t j).2 ⟨y, hy, hc'⟩
        have h5 := congrArg (fun z => z.testBit j) h4
        simp only [Nat.testBit_and, Nat.zero_testBit, hx, this] at h5
        simp at h5
      simp [hy']
    · simp [show x.testBit j = false by simpa using hx]

theorem mask_disjoint (N : Nat) (ms : List Nat)
    (hcover : ∀ i < N, ∃ m ∈ ms, m.testBit i = true) (hsum : ms.sum = 2 ^ N - 1) :
    ms.Pairwise (fun a b => a &&& b = 0) := by
  apply pairwise_of_sum_eq_or
  have h1 := orL_le_sum ms
  have h2 : 2 ^ N - 1 ≤ orL ms := by
    have : (2 ^ N - 1) = orL ms &&& (2 ^ N - 1) := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
      by_cases hj : j < N
      · have := (orL_testBit ms j).2 (hcover j hj)
        simp [hj, this]
      · simp [hj]
    calc 2 ^ N - 1 = orL ms &&& (2 ^ N - 1) := this
      _ ≤ orL ms := Nat.and_le_left
  omega

end CFSG.KC.LQT.PPC
