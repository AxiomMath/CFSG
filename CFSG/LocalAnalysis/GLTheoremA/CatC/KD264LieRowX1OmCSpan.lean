module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open
open scoped commutatorElement

section Plane

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V)

@[expose] def planeSpan (p : V × V) : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {p.1, p.2}

@[expose] def perpPlane (p : V × V) : Submodule (ZMod 2) V :=
  LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (planeSpan p)

variable {Q}

theorem left_mem_planeSpan (p : V × V) : p.1 ∈ planeSpan p :=
  Submodule.subset_span (Set.mem_insert _ _)

theorem right_mem_planeSpan (p : V × V) : p.2 ∈ planeSpan p :=
  Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem mem_planeSpan_iff (p : V × V) (x : V) :
    x ∈ planeSpan p ↔ ∃ c d : ZMod 2, c • p.1 + d • p.2 = x := by
  rw [planeSpan, Submodule.mem_span_pair]

theorem mem_perpPlane_iff (p : V × V) (x : V) :
    x ∈ perpPlane Q p ↔ polar Q p.1 x = 0 ∧ polar Q p.2 x = 0 := by
  rw [perpPlane, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨h _ (left_mem_planeSpan p), h _ (right_mem_planeSpan p)⟩
  · rintro ⟨h1, h2⟩ n hn
    obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p n).1 hn
    rw [QuadraticMap.polarBilin_apply_apply, polar_add_left, polar_smul_left, polar_smul_left,
      h1, h2]
    simp

theorem mem_perpPlane_iff' (p : V × V) (x : V) :
    x ∈ perpPlane Q p ↔ polar Q x p.1 = 0 ∧ polar Q x p.2 = 0 := by
  rw [mem_perpPlane_iff, polar_comm Q p.1 x, polar_comm Q p.2 x]

@[expose] def projPlane (Q : QuadraticForm (ZMod 2) V) (p : V × V) (x : V) : V :=
  polar Q x p.2 • p.1 + polar Q x p.1 • p.2

theorem projPlane_mem (Q : QuadraticForm (ZMod 2) V) (p : V × V) (x : V) :
    projPlane Q p x ∈ planeSpan p :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ (left_mem_planeSpan p))
    (Submodule.smul_mem _ _ (right_mem_planeSpan p))

theorem sub_projPlane_mem {p : V × V} (h : MinusPair Q p.1 p.2) (x : V) :
    x - projPlane Q p x ∈ perpPlane Q p := by
  rw [mem_perpPlane_iff']
  unfold projPlane
  constructor
  · rw [polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, h.aa, h.ba]
    simp
  · rw [polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, h.ab, h.bb]
    simp

theorem MinusPair.exists_decomp {p : V × V} (h : MinusPair Q p.1 p.2) (x : V) :
    ∃ w ∈ planeSpan p, x - w ∈ perpPlane Q p :=
  ⟨projPlane Q p x, projPlane_mem Q p x, sub_projPlane_mem h x⟩

theorem MinusPair.eq_zero_of_mem_planeSpan_of_mem_perp {p : V × V} (h : MinusPair Q p.1 p.2)
    {x : V} (hx : x ∈ planeSpan p) (hx' : x ∈ perpPlane Q p) : x = 0 := by
  obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p x).1 hx
  obtain ⟨h1, h2⟩ := (mem_perpPlane_iff' p _).1 hx'
  rw [polar_add_left, polar_smul_left, polar_smul_left, h.aa, h.ba] at h1
  rw [polar_add_left, polar_smul_left, polar_smul_left, h.ab, h.bb] at h2
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, add_zero] at h1 h2
  rw [h1, h2]
  simp

theorem MinusPair.finrank_planeSpan {p : V × V} (h : MinusPair Q p.1 p.2) :
    finrank (ZMod 2) (planeSpan p) = 2 := by
  have hli : LinearIndependent (ZMod 2) ![p.1, p.2] := by
    rw [LinearIndependent.pair_iff]
    intro c d hcd
    have h1 := congrArg (fun z => polar Q z p.2) hcd
    have h2 := congrArg (fun z => polar Q z p.1) hcd
    simp only [polar_add_left, polar_smul_left, h.ab, h.bb, h.aa, h.ba, polar_zero_left,
      smul_eq_mul, mul_zero, mul_one, zero_add, add_zero] at h1 h2
    exact ⟨h1, h2⟩
  have hrange : Set.range ![p.1, p.2] = ({p.1, p.2} : Set V) := by
    ext x
    simp [Fin.exists_fin_two, eq_comm]
    tauto
  have := finrank_span_eq_card hli
  rwa [hrange, Fintype.card_fin] at this

end Plane

section Wspan

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V)

@[expose] def Wspan : List (V × V) → Submodule (ZMod 2) V
  | [] => ⊥
  | p :: l => planeSpan p ⊔ Wspan l

@[expose] def perpL (l : List (V × V)) : Submodule (ZMod 2) V :=
  LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (Wspan l)

variable {Q}

theorem Wspan_nil : Wspan ([] : List (V × V)) = ⊥ := rfl

theorem Wspan_cons (p : V × V) (l : List (V × V)) : Wspan (p :: l) = planeSpan p ⊔ Wspan l := rfl

theorem planeSpan_le_Wspan {l : List (V × V)} {p : V × V} (hp : p ∈ l) : planeSpan p ≤ Wspan l := by
  induction l with
  | nil => exact absurd hp List.not_mem_nil
  | cons q l ih =>
    rcases List.mem_cons.1 hp with rfl | hp
    · exact le_sup_left
    · exact (ih hp).trans le_sup_right

theorem mem_perpL_iff (l : List (V × V)) (x : V) :
    x ∈ perpL Q l ↔ ∀ p ∈ l, polar Q p.1 x = 0 ∧ polar Q p.2 x = 0 := by
  induction l with
  | nil =>
    simp only [perpL, Wspan_nil, LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_bot,
      forall_eq, List.not_mem_nil, false_imp_iff, implies_true, iff_true]
    rw [QuadraticMap.polarBilin_apply_apply, polar_zero_left]
  | cons q l ih =>
    rw [List.forall_mem_cons, ← ih, ← mem_perpPlane_iff]
    simp only [perpL, Wspan_cons, perpPlane, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact ⟨fun n hn => h n (Submodule.mem_sup_left hn), fun n hn => h n (Submodule.mem_sup_right hn)⟩
    · rintro ⟨h1, h2⟩ n hn
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hn
      rw [map_add, LinearMap.add_apply, h1 u hu, h2 w hw, add_zero]

theorem polar_Wspan_eq_zero {l : List (V × V)} {p : V × V} (hp : ∀ q ∈ l, PairPerp Q p q)
    {w : V} (hw : w ∈ Wspan l) : polar Q p.1 w = 0 ∧ polar Q p.2 w = 0 := by
  induction l generalizing w with
  | nil =>
    rw [Wspan_nil, Submodule.mem_bot] at hw
    subst hw
    simp [polar_zero_right]
  | cons q l ih =>
    obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff q u).1 hu
    obtain ⟨h1, h2, h3, h4⟩ := hp q (List.mem_cons_self)
    obtain ⟨e1, e2⟩ := ih (fun r hr => hp r (List.mem_cons_of_mem _ hr)) hw'
    refine ⟨?_, ?_⟩
    · rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right, h1, h2, e1]
      simp
    · rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right, h3, h4, e2]
      simp

theorem IsFrame.exists_decomp {l : List (V × V)} (hl : IsFrame Q l) (x : V) :
    ∃ w ∈ Wspan l, x - w ∈ perpL Q l := by
  induction l generalizing x with
  | nil => exact ⟨0, Submodule.zero_mem _, (mem_perpL_iff _ _).2 (fun p hp => absurd hp List.not_mem_nil)⟩
  | cons p l ih =>
    obtain ⟨hp, hperp, hl'⟩ := isFrame_cons.1 hl
    obtain ⟨w', hw', hy⟩ := ih hl' (x - projPlane Q p x)
    refine ⟨projPlane Q p x + w', Submodule.add_mem_sup (projPlane_mem Q p x) hw', ?_⟩
    rw [mem_perpL_iff] at hy ⊢
    intro q hq
    rw [sub_add_eq_sub_sub]
    rcases List.mem_cons.1 hq with hqp | hq
    · rw [hqp]
      obtain ⟨h1, h2⟩ := (mem_perpPlane_iff p _).1 (sub_projPlane_mem hp x)
      obtain ⟨e1, e2⟩ := polar_Wspan_eq_zero hperp hw'
      refine ⟨?_, ?_⟩
      · rw [polar_sub_right, h1, e1]
        simp
      · rw [polar_sub_right, h2, e2]
        simp
    · exact hy q hq

theorem IsFrame.eq_zero_of_mem_Wspan_of_mem_perpL {l : List (V × V)} (hl : IsFrame Q l) {x : V}
    (hx : x ∈ Wspan l) (hx' : x ∈ perpL Q l) : x = 0 := by
  induction l generalizing x with
  | nil => rwa [Wspan_nil, Submodule.mem_bot] at hx
  | cons p l ih =>
    obtain ⟨hp, hperp, hl'⟩ := isFrame_cons.1 hl
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
    rw [mem_perpL_iff] at hx'
    obtain ⟨e1, e2⟩ := polar_Wspan_eq_zero hperp hw
    obtain ⟨f1, f2⟩ := hx' p (List.mem_cons_self)
    rw [polar_add_right, e1] at f1
    rw [polar_add_right, e2] at f2
    simp only [add_zero] at f1 f2
    have hu0 : u = 0 := hp.eq_zero_of_mem_planeSpan_of_mem_perp hu
      ((mem_perpPlane_iff p u).2 ⟨f1, f2⟩)
    subst hu0
    rw [zero_add] at hx' ⊢
    refine ih hl' hw ?_
    rw [mem_perpL_iff]
    intro q hq
    exact hx' q (List.mem_cons_of_mem _ hq)

theorem IsFrame.isCompl {l : List (V × V)} (hl : IsFrame Q l) : IsCompl (Wspan l) (perpL Q l) := by
  refine ⟨disjoint_iff.2 ?_, codisjoint_iff.2 ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    exact (Submodule.mem_bot _).2 (hl.eq_zero_of_mem_Wspan_of_mem_perpL hx.1 hx.2)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨w, hw, hx⟩ := hl.exists_decomp x
    exact Submodule.mem_sup.2 ⟨w, hw, x - w, hx, by abel⟩

theorem IsFrame.disjoint_planeSpan_Wspan {p : V × V} {l : List (V × V)} (hp : MinusPair Q p.1 p.2)
    (hperp : ∀ q ∈ l, PairPerp Q p q) : Disjoint (planeSpan p) (Wspan l) := by
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  obtain ⟨e1, e2⟩ := polar_Wspan_eq_zero hperp hx.2
  have := hp.eq_zero_of_mem_planeSpan_of_mem_perp hx.1 ((mem_perpPlane_iff p x).2 ⟨e1, e2⟩)
  exact (Submodule.mem_bot _).2 this

theorem IsFrame.finrank_Wspan [FiniteDimensional (ZMod 2) V] {l : List (V × V)}
    (hl : IsFrame Q l) : finrank (ZMod 2) (Wspan l) = 2 * l.length := by
  induction l with
  | nil => rw [Wspan_nil, finrank_bot]; simp
  | cons p l ih =>
    obtain ⟨hp, hperp, hl'⟩ := isFrame_cons.1 hl
    have hd := IsFrame.disjoint_planeSpan_Wspan hp hperp
    have h := Submodule.finrank_sup_add_finrank_inf_eq (planeSpan p) (Wspan l)
    rw [hd.eq_bot, finrank_bot, hp.finrank_planeSpan, ih hl'] at h
    rw [Wspan_cons, List.length_cons]
    omega

end Wspan

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

end
