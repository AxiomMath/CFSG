module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.PairTransfer
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

@[expose] def adjQ (R W : List (List ℤ)) (z : List ℤ) (u v : ℕ) : Bool :=
  if u < W.length then
    if v < W.length then false
    else decide (v - W.length < R.length) &&
      (decide (List.zipWith (· + ·) (W.getD u []) (R.getD (v - W.length) []) ∈ W) ||
        decide (List.zipWith (· + ·) (W.getD u []) (R.getD (v - W.length) []) = z))
  else
    if v < W.length then
      decide (u - W.length < R.length) &&
        (decide (List.zipWith (· + ·) (W.getD v []) (R.getD (u - W.length) []) ∈ W) ||
          decide (List.zipWith (· + ·) (W.getD v []) (R.getD (u - W.length) []) = z))
    else
      decide (u - W.length < R.length) && decide (v - W.length < R.length) &&
        decide (List.zipWith (· + ·) (R.getD (u - W.length) []) (R.getD (v - W.length) []) ∈ R)

theorem nb_testBit' (R W : List (List ℤ)) (z : List ℤ) (nbL : List ℕ)
    (hnb : nbL = (List.range (W.length + R.length)).map fun v =>
      bitsOf (W.length + R.length) (adjQ R W z v)) (u v : ℕ) :
    (nbL.getD u 0).testBit v =
      (decide (u < W.length + R.length) && decide (v < W.length + R.length) && adjQ R W z u v) := by
  subst hnb
  by_cases hu : u < W.length + R.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu]
    simp only [Option.map_some, Option.getD_some, testBit_bitsOf, hu, decide_true, Bool.true_and]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by simpa using hu)]
    simp [hu]

theorem adjQ_weights (R W : List (List ℤ)) (z : List ℤ) {u v : ℕ} (hu : u < W.length)
    (hv : v < W.length) : adjQ R W z u v = false := by
  simp [adjQ, hu, hv]

variable (R W : List (List ℤ)) (z : List ℤ) (nbL order : List ℕ) (wR wW budget : ℕ)

theorem pair_bound'
    (hnb : nbL = (List.range (W.length + R.length)).map fun v =>
      bitsOf (W.length + R.length) (adjQ R W z v))
    (hchk : ∀ i < R.length,
      (pairGraph W.length nbL wR wW).bnb order 200
        (rootMask W.length (W.length + R.length) nbL i) budget = true)
    (X Y : Finset ℕ) (hX : X.Nonempty) (hXR : ∀ i ∈ X, i < R.length)
    (hYW : ∀ a ∈ Y, a < W.length)
    (hXX : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → adjQ R W z (W.length + i) (W.length + j) = false)
    (hXY : ∀ i ∈ X, ∀ a ∈ Y,
      adjQ R W z (W.length + i) a = false ∧ adjQ R W z a (W.length + i) = false) :
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
      (decide (u < N) && decide (v < N) && adjQ R W z u v) := fun u v =>
    nb_testBit' R W z nbL hnb u v
  have hmask : ∀ v ∈ I, (rootMask nW N nbL i0).testBit v = true := by
    intro v hv
    rw [rootMask, testBit_bitsOf]
    have hnbi : ∀ v, adjQ R W z (nW + i0) v = false →
        (nbL.getD (nW + i0) 0).testBit v = false := by
      intro v hv
      rw [nb_testBit' R W z nbL hnb, hv]; simp
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
    have hadj : adjQ R W z u v = false := by
      rcases Finset.mem_union.1 hu with huY | huX <;> rcases Finset.mem_union.1 hv with hvY | hvX
      · exact adjQ_weights R W z (hYW u huY) (hYW v hvY)
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

open Matrix

variable {n : ℕ} (Pos IsW : (Fin n → ℤ) → Prop)

theorem pair_transfer'
    (hnb : nbL = (List.range (W.length + R.length)).map fun v =>
      bitsOf (W.length + R.length) (adjQ R W z v))
    (hchk : ∀ i < R.length,
      (pairGraph W.length nbL wR wW).bnb order 200
        (rootMask W.length (W.length + R.length) nbL i) budget = true)
    (hR : ∀ γ : Fin n → ℤ, Pos γ ↔ List.ofFn γ ∈ R)
    (hW : ∀ μ : Fin n → ℤ, IsW μ ↔ List.ofFn μ ∈ W) (hz : z = List.ofFn (0 : Fin n → ℤ))
    (X Y : Finset (Fin n → ℤ)) (hX : X.Nonempty) (hXP : ∀ γ ∈ X, Pos γ)
    (hXX : ∀ γ ∈ X, ∀ δ ∈ X, ¬ Pos (γ + δ)) (hYW : ∀ μ ∈ Y, IsW μ)
    (hXY : ∀ γ ∈ X, ∀ μ ∈ Y, ¬ IsW (γ + μ) ∧ γ + μ ≠ 0) :
    wR * X.card + wW * Y.card ≤ wR + budget := by
  classical
  let idx : (Fin n → ℤ) → ℕ := fun γ => R.idxOf (List.ofFn γ)
  let idy : (Fin n → ℤ) → ℕ := fun μ => W.idxOf (List.ofFn μ)
  have hidxlt : ∀ γ ∈ X, idx γ < R.length := fun γ hγ =>
    List.idxOf_lt_length_iff.2 ((hR γ).1 (hXP γ hγ))
  have hidylt : ∀ μ ∈ Y, idy μ < W.length := fun μ hμ =>
    List.idxOf_lt_length_iff.2 ((hW μ).1 (hYW μ hμ))
  have hget : ∀ γ ∈ X, R.getD (idx γ) [] = List.ofFn γ := fun γ hγ =>
    getD_idxOf R ((hR γ).1 (hXP γ hγ))
  have hgetY : ∀ μ ∈ Y, W.getD (idy μ) [] = List.ofFn μ := fun μ hμ =>
    getD_idxOf W ((hW μ).1 (hYW μ hμ))
  have hinj : Set.InjOn idx X := by
    intro γ hγ δ hδ h
    have := (List.idxOf_inj ((hR γ).1 (hXP γ hγ))).1 h
    exact List.ofFn_injective this
  have hinjY : Set.InjOn idy Y := by
    intro γ hγ δ hδ h
    have := (List.idxOf_inj ((hW γ).1 (hYW γ hγ))).1 h
    exact List.ofFn_injective this
  have hXc : (X.image idx).card = X.card := Finset.card_image_of_injOn hinj
  have hYc : (Y.image idy).card = Y.card := Finset.card_image_of_injOn hinjY
  have key := pair_bound' R W z nbL order wR wW budget hnb hchk (X.image idx) (Y.image idy)
    (hX.image idx) ?_ ?_ ?_ ?_
  · rw [hXc, hYc] at key; exact key
  · intro i hi
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hi
    exact hidxlt γ hγ
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
    exact hidylt b hb
  · intro i hi j hj hij
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hi
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hj
    have h1 := hidxlt γ hγ
    have h2 := hidxlt δ hδ
    simp only [adjQ, Nat.not_lt.2 (Nat.le_add_right _ _), ite_false, Nat.add_sub_cancel_left,
      decide_eq_true h1, decide_eq_true h2, Bool.true_and, decide_eq_false_iff_not]
    rw [hget γ hγ, hget δ hδ, zipWith_add_ofFn, ← hR]
    exact hXX γ hγ δ hδ
  · intro i hi a ha
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
    have h1 := hidxlt γ hγ
    have hbW := hidylt b hb
    obtain ⟨hn1, hn2⟩ := hXY γ hγ b hb
    have hnot1 : List.zipWith (· + ·) (W.getD (idy b) []) (R.getD (idx γ) []) ∉ W := by
      rw [hgetY b hb, hget γ hγ, zipWith_add_ofFn, ← hW, add_comm]
      exact hn1
    have hnot2 : List.zipWith (· + ·) (W.getD (idy b) []) (R.getD (idx γ) []) ≠ z := by
      rw [hgetY b hb, hget γ hγ, zipWith_add_ofFn, hz, add_comm]
      intro h
      exact hn2 (List.ofFn_injective h)
    constructor
    · simp only [adjQ, Nat.not_lt.2 (Nat.le_add_right _ _), ite_false, hbW, ite_true,
        Nat.add_sub_cancel_left, decide_eq_true h1, Bool.true_and, Bool.or_eq_false_iff,
        decide_eq_false_iff_not]
      exact ⟨hnot1, hnot2⟩
    · simp only [adjQ, hbW, ite_true, Nat.not_lt.2 (Nat.le_add_right _ _), ite_false,
        Nat.add_sub_cancel_left, decide_eq_true h1, Bool.true_and, Bool.or_eq_false_iff,
        decide_eq_false_iff_not]
      exact ⟨hnot1, hnot2⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
