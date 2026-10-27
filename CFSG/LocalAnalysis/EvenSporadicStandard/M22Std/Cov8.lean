module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov3

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.QuasithinUnique.Ch1.M22Cover CFSG.QuasithinUnique.Ch1.TitsCover
open CFSG.Monster.B.Co2.Native

@[expose] def rootsV : List ℕ :=
  [7, 9, 24, 28, 79, 80, 88, 89, 94, 95, 101, 104, 105, 107, 109, 110, 115, 117, 118, 120]

@[expose] def aV : List ℕ := [79, 80, 89, 95, 101, 104, 105, 107, 109, 110, 115, 117]

@[expose] def twInv (d : CovData) : Bool :=
  allLt 3 fun i => eqA 22 (compA 22 (d.xa (fo i)) (d.xa (fo i))) (idA 22)

@[expose] def twCenter (d : CovData) : Bool :=
  allLt d.nV fun v =>
    !(allLt 3 fun i => eqA 22 (compA 22 d.elaTab[v]! (d.xa (fo i)))
      (compA 22 (d.xa (fo i)) d.elaTab[v]!)) ||
      eqA 22 d.elaTab[v]! (idA 22) ||
      eqA 22 d.elaTab[v]! (compA 22 d.elaTab[79]! d.elaTab[79]!)

@[expose] def twRoots (d : CovData) : Bool :=
  allLt d.nV fun v =>
    eqA 22 (compA 22 d.elaTab[v]! d.elaTab[v]!) (compA 22 d.elaTab[79]! d.elaTab[79]!) ==
      rootsV.contains v

@[expose] def twWalks (d : CovData) : Bool :=
  let piv := gePivots (d.M + 5) d.M (forms0 d)
  aV.all fun v => decide (v < d.nV) && (d.tab.walkEnd 0 (sqWalk d v 79) == 0) &&
    (reduceF piv (d.M + 5) (formOf (d.tab.walkEdges 0 (sqWalk d v 79))) == 0)

@[expose] def twZ (d : CovData) : Bool :=
  decide (79 < d.nV) &&
    eqA 22 (compA 22 (compA 22 d.elaTab[79]! d.elaTab[79]!)
      (compA 22 d.elaTab[79]! d.elaTab[79]!)) (idA 22) &&
    !eqA 22 (compA 22 d.elaTab[79]! d.elaTab[79]!) (idA 22) &&
    allLt d.nV fun v => eqA 22 (compA 22 (compA 22 d.elaTab[79]! d.elaTab[79]!) d.elaTab[v]!)
      (compA 22 d.elaTab[v]! (compA 22 d.elaTab[79]! d.elaTab[79]!))

@[expose] def twCheck (d : CovData) : Bool :=
  twInv d && twCenter d && twRoots d && twWalks d && twZ d

section Sound

open CFSG.Monster.B.Co2 (allLt_iff rep_compA rep_idA eqA_iff eq_of_eqA)

variable {d : CovData}

theorem twInv_sound (hx : ∀ i, CFSG.Monster.B.Co2.Rep 22 (d.xa i) (d.x i))
    (h : twInv d = true) : ∀ i : Fin 3, d.x i * d.x i = 1 := by
  intro i
  have h1 := allLt_iff.1 h i.1 i.2
  rw [fo_val] at h1
  exact eq_of_eqA (rep_compA (hx i) (hx i)) rep_idA h1

theorem twZ_sound (hx : ∀ i, CFSG.Monster.B.Co2.Rep 22 (d.xa i) (d.x i)) (h : twZ d = true) :
    79 < d.nV ∧ (d.tab.el d.x 79 * d.tab.el d.x 79) * (d.tab.el d.x 79 * d.tab.el d.x 79) = 1 ∧
      d.tab.el d.x 79 * d.tab.el d.x 79 ≠ 1 ∧
      ∀ v < d.nV, (d.tab.el d.x 79 * d.tab.el d.x 79) * d.tab.el d.x v =
        d.tab.el d.x v * (d.tab.el d.x 79 * d.tab.el d.x 79) := by
  simp only [twZ, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h79, hsq⟩, hne⟩, hcomm⟩ := h
  have hel := d.rep_el hx h79
  have hz := rep_compA hel hel
  refine ⟨h79, eq_of_eqA (rep_compA hz hz) rep_idA hsq, fun h' => ?_, fun v hv => ?_⟩
  · have h2 := (eqA_iff hz rep_idA).2 h'
    rw [h2] at hne
    exact absurd hne (by decide)
  · have hv' := d.rep_el hx hv
    exact eq_of_eqA (rep_compA hz hv') (rep_compA hv' hz) (allLt_iff.1 hcomm v hv)

theorem twCenter_sound (hx : ∀ i, CFSG.Monster.B.Co2.Rep 22 (d.xa i) (d.x i))
    (h79 : 79 < d.nV) (h : twCenter d = true) :
    ∀ v < d.nV, (∀ i, d.tab.el d.x v * d.x i = d.x i * d.tab.el d.x v) →
      d.tab.el d.x v = 1 ∨ d.tab.el d.x v = d.tab.el d.x 79 * d.tab.el d.x 79 := by
  intro v hv hcomm
  have hrep : ∀ {u : ℕ}, u < d.nV → CFSG.Monster.B.Co2.Rep 22 (d.elaTab[u]!) (d.tab.el d.x u) :=
    fun hu => d.rep_el hx hu
  have h1 := allLt_iff.1 h v hv
  have hc : (allLt 3 fun i => eqA 22 (compA 22 d.elaTab[v]! (d.xa (fo i)))
      (compA 22 (d.xa (fo i)) d.elaTab[v]!)) = true := by
    refine allLt_iff.2 fun i hi => ?_
    rw [show fo i = ⟨i, hi⟩ from fo_val ⟨i, hi⟩]
    refine (eqA_iff (rep_compA (hrep hv) (hx ⟨i, hi⟩)) (rep_compA (hx ⟨i, hi⟩) (hrep hv))).2 ?_
    exact hcomm ⟨i, hi⟩
  simp only [hc, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · left
    exact eq_of_eqA (hrep hv) rep_idA h1
  · right
    exact eq_of_eqA (hrep hv) (rep_compA (hrep h79) (hrep h79)) h1

theorem twRoots_sound (hx : ∀ i, CFSG.Monster.B.Co2.Rep 22 (d.xa i) (d.x i))
    (h79 : 79 < d.nV) (h : twRoots d = true) :
    ∀ v < d.nV, d.tab.el d.x v * d.tab.el d.x v = d.tab.el d.x 79 * d.tab.el d.x 79 ↔
      v ∈ rootsV := by
  intro v hv
  have hrep : ∀ {u : ℕ}, u < d.nV → CFSG.Monster.B.Co2.Rep 22 (d.elaTab[u]!) (d.tab.el d.x u) :=
    fun hu => d.rep_el hx hu
  have h1 := allLt_iff.1 h v hv
  rw [beq_iff_eq] at h1
  have e := eqA_iff (rep_compA (hrep hv) (hrep hv)) (rep_compA (hrep h79) (hrep h79))
  rw [← e, h1]
  simp

end Sound

end CFSG.EvenSporadicStandard.M22Std
