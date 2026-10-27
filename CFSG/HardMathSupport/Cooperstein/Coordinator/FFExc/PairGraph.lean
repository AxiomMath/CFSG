module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.BranchBound
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

@[expose] def dotL (a b : List ℤ) : ℤ := (List.zipWith (· * ·) a b).sum

@[expose] def adjP (R W : List (List ℤ)) (u v : ℕ) : Bool :=
  if u < W.length then
    if v < W.length then false
    else decide (v - W.length < R.length) &&
      decide (dotL (W.getD u []) (R.getD (v - W.length) []) = -1)
  else
    if v < W.length then
      decide (u - W.length < R.length) &&
        decide (dotL (W.getD v []) (R.getD (u - W.length) []) = -1)
    else
      decide (u - W.length < R.length) && decide (v - W.length < R.length) &&
        decide (List.zipWith (· + ·) (R.getD (u - W.length) []) (R.getD (v - W.length) []) ∈ R)

@[expose] def bitsOf (n : ℕ) (p : ℕ → Bool) : ℕ :=
  (List.range n).foldl (fun acc j => if p j then acc ||| 2 ^ j else acc) 0

theorem testBit_bitsOf (n : ℕ) (p : ℕ → Bool) (j : ℕ) :
    (bitsOf n p).testBit j = (decide (j < n) && p j) := by
  have key : ∀ (l : List ℕ) (acc : ℕ), (l.foldl (fun acc j => if p j then acc ||| 2 ^ j else acc)
      acc).testBit j = (acc.testBit j || (decide (j ∈ l) && p j)) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a l ih =>
      intro acc
      rw [List.foldl_cons, ih]
      by_cases hpa : p a = true
      · simp only [hpa, ite_true, Nat.testBit_or, Nat.testBit_two_pow, List.mem_cons]
        by_cases hja : a = j
        · subst hja; simp [hpa]
        · have : ¬ j = a := fun h => hja h.symm
          simp [hja, this]
      · have hpa' : p a = false := by simpa using hpa
        simp only [hpa', Bool.false_eq_true, ite_false, List.mem_cons]
        by_cases hja : j = a
        · subst hja; simp [hpa']
        · simp [hja]
  rw [bitsOf, key, Nat.zero_testBit, Bool.false_or]
  simp [List.mem_range]

@[expose] def pairGraph (nW : ℕ) (nbL : List ℕ) (wR wW : ℕ) : WGraph where
  nb v := nbL.getD v 0
  wt v := if v < nW then wW else wR

@[expose] def rootMask (nW N : ℕ) (nbL : List ℕ) (i : ℕ) : ℕ :=
  bitsOf N fun j => (decide (j < nW) || decide (nW + i < j)) && !(nbL.getD (nW + i) 0).testBit j

theorem nb_testBit (R W : List (List ℤ)) (nbL : List ℕ)
    (hnb : nbL = (List.range (W.length + R.length)).map fun v =>
      bitsOf (W.length + R.length) (adjP R W v)) (u v : ℕ) :
    (nbL.getD u 0).testBit v =
      (decide (u < W.length + R.length) && decide (v < W.length + R.length) && adjP R W u v) := by
  subst hnb
  by_cases hu : u < W.length + R.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu]
    simp only [Option.map_some, Option.getD_some, testBit_bitsOf, hu, decide_true, Bool.true_and]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by simpa using hu)]
    simp [hu]

theorem adjP_weights (R W : List (List ℤ)) {u v : ℕ} (hu : u < W.length) (hv : v < W.length) :
    adjP R W u v = false := by
  simp [adjP, hu, hv]

variable (R W : List (List ℤ)) (nbL order : List ℕ) (wR wW budget : ℕ)

theorem pair_bound
    (hnb : nbL = (List.range (W.length + R.length)).map fun v =>
      bitsOf (W.length + R.length) (adjP R W v))
    (hchk : ∀ i < R.length,
      (pairGraph W.length nbL wR wW).bnb order 200
        (rootMask W.length (W.length + R.length) nbL i) budget = true)
    (X Y : Finset ℕ) (hX : X.Nonempty) (hXR : ∀ i ∈ X, i < R.length)
    (hYW : ∀ a ∈ Y, a < W.length)
    (hXX : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → adjP R W (W.length + i) (W.length + j) = false)
    (hXY : ∀ i ∈ X, ∀ a ∈ Y,
      adjP R W (W.length + i) a = false ∧ adjP R W a (W.length + i) = false) :
    wR * X.card + wW * Y.card ≤ wR + budget := by
  classical
  set nW := W.length with hnW
  set N := nW + R.length with hN
  set g := pairGraph nW nbL wR wW with hg
  set i0 := X.min' hX with hi0
  have hi0X : i0 ∈ X := Finset.min'_mem X hX
  have hi0R : i0 < R.length := hXR i0 hi0X
  set X' := X.erase i0 with hX'
  set I : Finset ℕ := Y ∪ X'.image (fun j => nW + j) with hI
  have hdisj : Disjoint Y (X'.image (fun j => nW + j)) := by
    rw [Finset.disjoint_left]
    intro a haY haX
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 haX
    have := hYW _ haY
    omega
  have hnbv : ∀ u v, (g.nb u).testBit v =
      (decide (u < N) && decide (v < N) && adjP R W u v) := fun u v => nb_testBit R W nbL hnb u v
  have hmask : ∀ v ∈ I, (rootMask nW N nbL i0).testBit v = true := by
    intro v hv
    rw [rootMask, testBit_bitsOf]
    have hnbi : ∀ v, adjP R W (nW + i0) v = false → (nbL.getD (nW + i0) 0).testBit v = false := by
      intro v hv
      rw [nb_testBit R W nbL hnb, hv]; simp
    rcases Finset.mem_union.1 hv with hvY | hvX
    · have hlt := hYW v hvY
      have h1 := hnbi v (hXY i0 hi0X v hvY).1
      simp only [h1, Bool.not_false, Bool.and_true, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq]
      exact ⟨by omega, Or.inl hlt⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hvX
      obtain ⟨hji, hjX⟩ := Finset.mem_erase.1 hj
      have hgt : i0 < j := lt_of_le_of_ne (Finset.min'_le X j hjX) (Ne.symm hji)
      have h1 := hnbi (nW + j) (hXX i0 hi0X j hjX hji.symm)
      have hjR := hXR j hjX
      simp only [h1, Bool.not_false, Bool.and_true, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq]
      exact ⟨by omega, Or.inr (by omega)⟩
  have hind : g.Indep I := by
    intro u hu v hv huv
    rw [hnbv]
    have hN' : ∀ w ∈ I, w < N := by
      intro w hw
      rcases Finset.mem_union.1 hw with hwY | hwX
      · have := hYW w hwY; omega
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hwX
        have := hXR j (Finset.mem_of_mem_erase hj); omega
    have hadj : adjP R W u v = false := by
      rcases Finset.mem_union.1 hu with huY | huX <;> rcases Finset.mem_union.1 hv with hvY | hvX
      · exact adjP_weights R W (hYW u huY) (hYW v hvY)
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hvX
        exact (hXY j (Finset.mem_of_mem_erase hj) u huY).2
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 huX
        exact (hXY j (Finset.mem_of_mem_erase hj) v hvY).1
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 huX
        obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hvX
        refine hXX j (Finset.mem_of_mem_erase hj) j' (Finset.mem_of_mem_erase hj') ?_
        intro h; apply huv; rw [h]
    rw [hadj]; simp
  have hsound := WGraph.bnb_sound g order 200 _ budget (hchk i0 hi0R) I hmask hind
  have hwt : ∑ v ∈ I, g.wt v = wW * Y.card + wR * X'.card := by
    rw [hI, Finset.sum_union hdisj, Finset.sum_image (by intro a _ b _ h; simpa using h)]
    have h1 : ∀ v ∈ Y, g.wt v = wW := fun v hv => by
      simp [hg, pairGraph, hYW v hv]
    have h2 : ∀ j ∈ X', g.wt (nW + j) = wR := fun j _ => by
      simp [hg, pairGraph]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
    simp [mul_comm]
  have hcard : X.card = X'.card + 1 := (Finset.card_erase_add_one hi0X).symm
  rw [hwt] at hsound
  rw [hcard]
  nlinarith

theorem abelian_bound
    (hnb : nbL = (List.range R.length).map fun v => bitsOf R.length (adjP R [] v))
    (hchk : (pairGraph 0 nbL 1 1).bnb order 200 (bitsOf R.length fun _ => true) budget = true)
    (X : Finset ℕ) (hXR : ∀ i ∈ X, i < R.length)
    (hXX : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → adjP R [] i j = false) :
    X.card ≤ budget := by
  classical
  have hnb' : nbL = (List.range (([] : List (List ℤ)).length + R.length)).map fun v =>
      bitsOf (([] : List (List ℤ)).length + R.length) (adjP R [] v) := by
    simpa using hnb
  have hind : (pairGraph 0 nbL 1 1).Indep X := by
    intro u hu v hv huv
    rw [pairGraph]
    simp only
    rw [nb_testBit R [] nbL hnb' u v, hXX u hu v hv huv]
    simp
  have hmask : ∀ v ∈ X, (bitsOf R.length fun _ => true).testBit v = true := by
    intro v hv
    rw [testBit_bitsOf]
    simp [hXR v hv]
  have := WGraph.bnb_sound (pairGraph 0 nbL 1 1) order 200 _ budget hchk X hmask hind
  simpa [pairGraph] using this

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
