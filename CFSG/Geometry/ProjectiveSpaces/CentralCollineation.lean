module

public import CFSG.Geometry.ProjectiveSpaces.Affine
public import Mathlib.Tactic.Set

public section

namespace CFSG.Geometry.ProjectiveSpaces

namespace ProjectiveSpace

universe u

variable {P : Type u} {G : ProjectiveSpace P} {H : Set P}

open Classical in
@[expose] noncomputable def meet (G : ProjectiveSpace P) (x y z w : P) : P :=
  if h : (G.line x y ∩ G.line z w).Nonempty then h.some else x

theorem meet_mem {x y z w : P} (h : (G.line x y ∩ G.line z w).Nonempty) :
    G.meet x y z w ∈ G.line x y ∩ G.line z w := by
  rw [meet, dite_eq_left h]
  exact h.some_mem

@[expose] noncomputable def centralImage (G : ProjectiveSpace P) (H : Set P) (c u u' x : P) : P :=
  G.meet c x u' (G.inf H u x)

structure IsBase (G : ProjectiveSpace P) (H : Set P) (c u u' : P) : Prop where
  not_mem : u ∉ H
  not_mem' : u' ∉ H
  ne_center : u ≠ c
  ne_center' : u' ≠ c
  ne : u ≠ u'
  mem_line : u' ∈ G.line c u

variable (hH : G.IsHyperplane H)
include hH

omit hH in
theorem not_mem_line_of_base {c u u' x : P} (hb : G.IsBase H c u u')
    (hx : x ∉ G.line c u) : u' ∉ G.line c x := by
  intro h
  have hxc : x ≠ c := fun e => hx (e ▸ G.left_mem_line c u)
  have h1 : G.line c u' = G.line c u := G.line_eq_of_mem hb.mem_line hb.ne_center'
  have h2 : G.line c u' = G.line c x := G.line_eq_of_mem h hb.ne_center'
  exact hx (h1 ▸ h2 ▸ G.right_mem_line c x)

theorem centralImage_spec {c u u' x : P} (hb : G.IsBase H c u u') (hxH : x ∉ H)
    (hx : x ∉ G.line c u) :
    G.centralImage H c u u' x ∈ G.line c x ∧
      G.centralImage H c u u' x ∈ G.line u' (G.inf H u x) ∧
      G.centralImage H c u u' x ∉ H ∧ G.centralImage H c u u' x ≠ c ∧
      G.centralImage H c u u' x ≠ x ∧ G.centralImage H c u u' x ≠ u' ∧
      ∀ y, y ∈ G.line c x → y ∈ G.line u' (G.inf H u x) → y = G.centralImage H c u u' x := by
  have hcu : c ≠ u := Ne.symm hb.ne_center
  have hxc : x ≠ c := fun e => hx (e ▸ G.left_mem_line c u)
  have hux : u ≠ x := fun e => hx (e ▸ G.right_mem_line c u)
  set d := G.inf H u x with hd
  have hdl : d ∈ G.line u x := hH.inf_mem_line hux
  have hdH : d ∈ H := hH.inf_mem hux
  have hdu : d ≠ u := hH.inf_ne hb.not_mem hux
  have hdx : d ≠ x := fun e => hxH (e ▸ hdH)
  have hu'd : u' ≠ d := fun e => hb.not_mem' (e ▸ hdH)
  have hσ : ¬ G.Collinear c u x := fun h => hx ((G.collinear_iff_of_ne hcu).1 h)
  have hσS := G.isSubspace_plane hσ
  have hu'σ : u' ∈ G.plane c u x := G.line_subset_plane c u x hb.mem_line
  have hdσ : d ∈ G.plane c u x :=
    hσS.line_subset (G.middle_mem_plane c u x) (G.right_mem_plane c u x) hdl
  have hu'x := G.not_mem_line_of_base hb hx
  have hne : G.line c x ≠ G.line u' d := fun e => hu'x (e ▸ G.left_mem_line u' d)
  have hmeet := G.inter_nonempty_of_mem_plane hσ (G.left_mem_plane c u x)
    (G.right_mem_plane c u x) hu'σ hdσ (Ne.symm hxc) hu'd
  have hx' := meet_mem hmeet
  set x' := G.centralImage H c u u' x with hx'def
  have huniq : ∀ y, y ∈ G.line c x → y ∈ G.line u' d → y = x' := fun y hy1 hy2 =>
    G.eq_of_mem_of_mem (G.line_mem_lines (Ne.symm hxc)) (G.line_mem_lines hu'd) hne hy1 hy2
      hx'.1 hx'.2
  have hdcx : d ∉ G.line c x := by
    intro h
    have h1 : G.line x d = G.line x c := by
      rw [G.line_comm x c]
      exact G.line_eq_of_mem (G.line_comm c x ▸ h) hdx |>.trans (G.line_comm x c)
    have h2 : G.line x d = G.line x u :=
      G.line_eq_of_mem (G.line_comm u x ▸ hdl) hdx
    have hul : u ∈ G.line c x := by
      rw [G.line_comm, ← h1, h2]
      exact G.right_mem_line x u
    exact hx (G.line_eq_of_mem hul hb.ne_center ▸ G.right_mem_line c x)
  refine ⟨hx'.1, hx'.2, fun hx'H => ?_, fun hx'c => ?_, fun hx'x => ?_,
    fun hx'u => hu'x (hx'u ▸ hx'.1), huniq⟩
  · have : x' = d := hH.eq_of_mem_line hb.not_mem' hx'.2 (G.right_mem_line u' d) hx'H hdH
    exact hdcx (this ▸ hx'.1)
  · have hcl : c ∈ G.line u' d := hx'c ▸ hx'.2
    have h1 : G.line u' c = G.line u' d := G.line_eq_of_mem hcl (Ne.symm hb.ne_center')
    have h2 : G.line u' c = G.line c u := by
      rw [G.line_comm]
      exact G.line_eq_of_mem hb.mem_line hb.ne_center'
    have hdcu : d ∈ G.line c u := h2 ▸ h1 ▸ G.right_mem_line u' d
    have h3 : G.line u d = G.line u c := by
      rw [G.line_comm u c]
      exact (G.line_eq_of_mem (G.line_comm c u ▸ hdcu) hdu).trans (G.line_comm u c)
    have h4 : G.line u d = G.line u x := G.line_eq_of_mem hdl hdu
    exact hx (by rw [G.line_comm, ← h3, h4]; exact G.right_mem_line u x)
  · have hxl : x ∈ G.line u' d := hx'x ▸ hx'.2
    have h1 : G.line x d = G.line u' d := G.line_eq_line hdx.symm hxl (G.right_mem_line u' d)
    have h2 : G.line x d = G.line x u := G.line_eq_of_mem (G.line_comm u x ▸ hdl) hdx
    have hu'ux : u' ∈ G.line u x := by
      rw [G.line_comm, ← h2, h1]
      exact G.left_mem_line u' d
    have hne2 : G.line u x ≠ G.line c u := fun e => hx (e ▸ G.right_mem_line u x)
    exact hb.ne (G.eq_of_mem_of_mem (G.line_mem_lines hux) (G.line_mem_lines hcu) hne2
      (G.left_mem_line u x) (G.right_mem_line c u) hu'ux hb.mem_line)

theorem inf_ne_inf {u x y : P} (huH : u ∉ H) (hu : u ∉ G.line x y) (hxy : x ≠ y) :
    G.inf H u x ≠ G.inf H u y := by
  intro e
  have hux : u ≠ x := fun e' => hu (e' ▸ G.left_mem_line x y)
  have huy : u ≠ y := fun e' => hu (e' ▸ G.right_mem_line x y)
  have h1 := hH.line_inf huH hux
  have h2 := hH.line_inf huH huy
  have hyl : y ∈ G.line u x := by
    rw [← h1, e, h2]
    exact G.right_mem_line u y
  apply hu
  rw [G.line_eq_line hxy (G.right_mem_line u x) hyl]
  exact G.left_mem_line u x

theorem line_ne_line_of_inf {v d₁ d₂ : P} (hv : v ∉ H) (hd₁ : d₁ ∈ H) (hd₂ : d₂ ∈ H)
    (hd : d₁ ≠ d₂) : G.line v d₁ ≠ G.line v d₂ := by
  intro e
  have hd₂l : d₂ ∈ G.line v d₁ := e ▸ G.right_mem_line v d₂
  have h := G.line_eq_line hd (G.right_mem_line v d₁) hd₂l
  exact hv (hH.isSubspace.line_subset hd₁ hd₂ (h ▸ G.left_mem_line v d₁))

omit hH in
theorem line_eq_of_center_mem {c x y : P} (hc : c ∈ G.line x y) (hcx : c ≠ x) :
    G.line c x = G.line x y := by
  rw [G.line_comm]
  exact G.line_eq_of_mem hc hcx

theorem centralImage_pair (hdim : ∀ x y z : P, ¬ G.Collinear x y z → ∃ w, w ∉ G.plane x y z)
    {c u u' x y : P} (hb : G.IsBase H c u u') (hxH : x ∉ H) (hyH : y ∉ H)
    (hx : x ∉ G.line c u) (hy : y ∉ G.line c u) (hxy : x ≠ y) :
    G.centralImage H c u u' x ≠ G.centralImage H c u u' y ∧
      G.inf H x y ∈ G.line (G.centralImage H c u u' x) (G.centralImage H c u u' y) := by
  obtain ⟨hx1, hx2, hx3, hx4, hx5, hx6, -⟩ := G.centralImage_spec hH hb hxH hx
  obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6, -⟩ := G.centralImage_spec hH hb hyH hy
  set x' := G.centralImage H c u u' x
  set y' := G.centralImage H c u u' y
  have hcu : c ≠ u := Ne.symm hb.ne_center
  have hxc : x ≠ c := fun e => hx (e ▸ G.left_mem_line c u)
  have hyc : y ≠ c := fun e => hy (e ▸ G.left_mem_line c u)
  have hux : u ≠ x := fun e => hx (e ▸ G.right_mem_line c u)
  have huy : u ≠ y := fun e => hy (e ▸ G.right_mem_line c u)
  have hdx := hH.inf_mem hux
  have hdy := hH.inf_mem huy
  have hlx : G.line u' x' = G.line u' (G.inf H u x) := G.line_eq_of_mem hx2 hx6
  have hly : G.line u' y' = G.line u' (G.inf H u y) := G.line_eq_of_mem hy2 hy6
  by_cases hc : c ∈ G.line x y
  · have h1 : G.line c x = G.line x y := G.line_eq_of_center_mem hc (Ne.symm hxc)
    have h2 : G.line c y = G.line x y := by
      rw [G.line_comm x y]
      exact G.line_eq_of_center_mem (G.line_comm x y ▸ hc) (Ne.symm hyc)
    have hx'l : x' ∈ G.line x y := h1 ▸ hx1
    have hy'l : y' ∈ G.line x y := h2 ▸ hy1
    have hne : x' ≠ y' := by
      intro e
      by_cases hd : G.inf H u x = G.inf H u y
      · have h3 := hH.line_inf hb.not_mem hux
        have h4 := hH.line_inf hb.not_mem huy
        have hyl : y ∈ G.line u x := by
          rw [← h3, hd, h4]
          exact G.right_mem_line u y
        have h5 : G.line x y = G.line u x :=
          G.line_eq_line hxy (G.right_mem_line u x) hyl
        have hcl : c ∈ G.line u x := h5 ▸ hc
        have h6 : G.line u c = G.line u x := G.line_eq_of_mem hcl hcu
        exact hx (by rw [G.line_comm, h6]; exact G.right_mem_line u x)
      · have hne' := G.line_ne_line_of_inf hH hb.not_mem' hdx hdy hd
        have hu'dx : u' ≠ G.inf H u x := fun e' => hb.not_mem' (by rw [e']; exact hdx)
        have hu'dy : u' ≠ G.inf H u y := fun e' => hb.not_mem' (by rw [e']; exact hdy)
        exact hx6 (G.eq_of_mem_of_mem (G.line_mem_lines hu'dx)
          (G.line_mem_lines hu'dy) hne' hx2 (e ▸ hy2)
          (G.left_mem_line _ _) (G.left_mem_line _ _))
    refine ⟨hne, ?_⟩
    rw [G.line_eq_line hne hx'l hy'l]
    exact hH.inf_mem_line hxy
  have hcxy : y ∉ G.line c x := fun h => hc (by
    rw [← G.line_eq_of_center_mem (by
      rw [G.line_eq_line hxy (G.right_mem_line c x) h]
      exact G.left_mem_line c x) (Ne.symm hxc)]
    exact G.left_mem_line c x)
  have hne : x' ≠ y' := by
    intro e
    have hne' : G.line c x ≠ G.line c y := fun e' => hcxy (e' ▸ G.right_mem_line c y)
    exact hx4 (G.eq_of_mem_of_mem (G.line_mem_lines (Ne.symm hxc)) (G.line_mem_lines
      (Ne.symm hyc)) hne' hx1 (e ▸ hy1) (G.left_mem_line c x) (G.left_mem_line c y))
  refine ⟨hne, ?_⟩
  by_cases hu : u ∈ G.line x y
  · have h1 : G.inf H u x = G.inf H x y := by
      rw [hH.inf_comm hb.not_mem hux]
      exact hH.inf_eq_of_mem hxH hxy hu hux
    have h2 : G.inf H u y = G.inf H x y := by
      rw [hH.inf_comm hb.not_mem huy, hH.inf_comm hxH hxy]
      exact hH.inf_eq_of_mem hyH (Ne.symm hxy) (G.line_comm x y ▸ hu) huy
    rw [h1] at hx2
    rw [h2] at hy2
    rw [G.line_eq_line hne hx2 hy2]
    exact G.right_mem_line _ _
  have hdne := G.inf_ne_inf hH hb.not_mem hu hxy
  have ha : ¬ G.Collinear u x y := fun h => hu ((G.collinear_iff_of_ne hxy).1 h.rotate)
  have hb' : ¬ G.Collinear u' x' y' := by
    intro h
    have hy'l : y' ∈ G.line u' x' := (G.collinear_iff_of_ne (Ne.symm hx6)).1 h
    have h1 : G.line u' y' = G.line u' x' := G.line_eq_of_mem hy'l hy6
    exact G.line_ne_line_of_inf hH hb.not_mem' hdx hdy hdne (hlx ▸ hly ▸ h1.symm)
  have h₁₂ : ¬ G.Collinear c u x := fun h => hx ((G.collinear_iff_of_ne hcu).1 h)
  have h₁₃ : ¬ G.Collinear c u y := fun h => hy ((G.collinear_iff_of_ne hcu).1 h)
  have h₂₃ : ¬ G.Collinear c x y := fun h => hcxy ((G.collinear_iff_of_ne (Ne.symm hxc)).1 h)
  have hσ := G.isSubspace_plane h₂₃
  have hmeet := G.inter_nonempty_of_mem_plane h₂₃ (G.middle_mem_plane c x y)
    (G.right_mem_plane c x y) (G.line_subset_plane c x y hx1) (G.line_subset_plane₁₃ h₂₃ hy1)
    hxy hne
  have hp := meet_mem hmeet
  have hcol := G.desargues hdim ha hb' h₁₂ h₁₃ h₂₃ hb.mem_line hx1 hy1 (Ne.symm hb.ne_center')
    (Ne.symm hx4) (Ne.symm hy4) hb.ne (Ne.symm hx5) (Ne.symm hy5)
    ⟨hH.inf_mem_line hux, hlx ▸ G.right_mem_line _ _⟩
    ⟨hH.inf_mem_line huy, hly ▸ G.right_mem_line _ _⟩ hp
  have hpH : G.meet x y x' y' ∈ H :=
    hH.isSubspace.line_subset hdx hdy ((G.collinear_iff_of_ne hdne).1 hcol)
  have := hH.eq_inf hxH hxy hp.1 hpH
  rw [← this]
  exact hp.2

theorem isBase_centralImage {c u u' w : P} (hb : G.IsBase H c u u') (hwH : w ∉ H)
    (hw : w ∉ G.line c u) : G.IsBase H c w (G.centralImage H c u u' w) := by
  obtain ⟨h1, -, h3, h4, h5, -, -⟩ := G.centralImage_spec hH hb hwH hw
  exact ⟨hwH, h3, fun e => hw (e ▸ G.left_mem_line c u), h4, Ne.symm h5, h1⟩

theorem centralImage_eq_of_base (hdim : ∀ x y z : P, ¬ G.Collinear x y z → ∃ w, w ∉ G.plane x y z)
    {c u u' w x : P} (hb : G.IsBase H c u u') (hwH : w ∉ H) (hw : w ∉ G.line c u) (hxH : x ∉ H)
    (hx : x ∉ G.line c u) (hxw : x ∉ G.line c w) :
    G.centralImage H c w (G.centralImage H c u u' w) x = G.centralImage H c u u' x := by
  have hb' := G.isBase_centralImage hH hb hwH hw
  have hwx : w ≠ x := fun e => hxw (e ▸ G.right_mem_line c w)
  obtain ⟨hne, hinf⟩ := G.centralImage_pair hH hdim hb hwH hxH hw hx hwx
  obtain ⟨hx1, -, -, -, -, -, -⟩ := G.centralImage_spec hH hb hxH hx
  obtain ⟨-, -, -, -, -, -, huniq⟩ := G.centralImage_spec hH hb' hxH hxw
  refine (huniq _ hx1 ?_).symm
  have hd : G.inf H w x ≠ G.centralImage H c u u' w :=
    fun e => hb'.not_mem' (e ▸ hH.inf_mem hwx)
  rw [G.line_eq_of_mem hinf hd]
  exact G.right_mem_line _ _

omit hH in
open Classical in
@[expose] noncomputable def centralCollineation (G : ProjectiveSpace P) (H : Set P)
    (c a b a₀ x : P) : P :=
  if x ∈ H then x else if x = c then c else if x ∈ G.line c a then
    G.centralImage H c a₀ (G.centralImage H c a b a₀) x else G.centralImage H c a b x

omit hH in
theorem centralCollineation_of_mem {c a b a₀ x : P} (hx : x ∈ H) :
    G.centralCollineation H c a b a₀ x = x := by
  simp [centralCollineation, hx]

omit hH in
theorem centralCollineation_center {c a b a₀ : P} (hc : c ∉ H) :
    G.centralCollineation H c a b a₀ c = c := by
  simp [centralCollineation, hc]

omit hH in
theorem centralCollineation_of_not_mem_line {c a b a₀ x : P} (hxH : x ∉ H)
    (hx : x ∉ G.line c a) :
    G.centralCollineation H c a b a₀ x = G.centralImage H c a b x := by
  have hxc : x ≠ c := fun e => hx (e ▸ G.left_mem_line c a)
  simp [centralCollineation, hxH, hxc, hx]

omit hH in
theorem centralCollineation_of_mem_line {c a b a₀ x : P} (hxH : x ∉ H) (hxc : x ≠ c)
    (hx : x ∈ G.line c a) :
    G.centralCollineation H c a b a₀ x =
      G.centralImage H c a₀ (G.centralImage H c a b a₀) x := by
  simp [centralCollineation, hxH, hxc, hx]

variable (hdim : ∀ x y z : P, ¬ G.Collinear x y z → ∃ w, w ∉ G.plane x y z)
  (htri : ∃ x y z : P, ¬ G.Collinear x y z)
include hdim

omit hH hdim in
theorem not_mem_line_of_mem_line {c a x : P} (hx : x ∈ G.line c a) (hxc : x ≠ c)
    {y : P} (hy : y ∉ G.line c a) : x ∉ G.line c y := by
  intro h
  have h1 : G.line c x = G.line c a := G.line_eq_of_mem hx hxc
  have h2 : G.line c x = G.line c y := G.line_eq_of_mem h hxc
  exact hy (h1 ▸ h2 ▸ G.right_mem_line c y)

theorem centralCollineation_eq_of_not_mem {c a b a₀ w x : P} (hb : G.IsBase H c a b)
    (ha₀H : a₀ ∉ H) (ha₀ : a₀ ∉ G.line c a) (hwH : w ∉ H) (hw : w ∉ G.line c a) (hxH : x ∉ H)
    (hxc : x ≠ c) (hxw : x ∉ G.line c w) :
    G.centralCollineation H c a b a₀ x =
      G.centralImage H c w (G.centralCollineation H c a b a₀ w) x := by
  rw [G.centralCollineation_of_not_mem_line hwH hw]
  have hca : c ≠ a := Ne.symm hb.ne_center
  by_cases hx : x ∉ G.line c a
  · rw [G.centralCollineation_of_not_mem_line hxH hx,
      G.centralImage_eq_of_base hH hdim hb hwH hw hxH hx hxw]
  push Not at hx
  rw [G.centralCollineation_of_mem_line hxH hxc hx]
  have hb₀ := G.isBase_centralImage hH hb ha₀H ha₀
  have hxa₀ : x ∉ G.line c a₀ := G.not_mem_line_of_mem_line hx hxc ha₀
  have key : ∀ v, v ∉ H → v ∉ G.line c a → v ∉ G.line c a₀ → x ∉ G.line c v →
      G.centralImage H c a₀ (G.centralImage H c a b a₀) x =
        G.centralImage H c v (G.centralImage H c a b v) x := by
    intro v hvH hv hva₀ hxv
    rw [← G.centralImage_eq_of_base hH hdim hb ha₀H ha₀ hvH hv hva₀,
      G.centralImage_eq_of_base hH hdim hb₀ hvH hva₀ hxH hxa₀ hxv]
  by_cases hwa₀ : w ∉ G.line c a₀
  · exact key w hwH hw hwa₀ hxw
  push Not at hwa₀
  have hσ : ¬ G.Collinear c a a₀ := fun h => ha₀ ((G.collinear_iff_of_ne hca).1 h)
  obtain ⟨v, hvH, hvσ⟩ := hH.exists_not_mem_plane_not_mem hdim hσ
  have hσS := G.isSubspace_plane hσ
  have hv : v ∉ G.line c a := fun h => hvσ (G.line_subset_plane c a a₀ h)
  have hva₀ : v ∉ G.line c a₀ := fun h => hvσ (G.line_subset_plane₁₃ hσ h)
  have hvc : v ≠ c := fun e => hv (e ▸ G.left_mem_line c a)
  have hxv : x ∉ G.line c v := G.not_mem_line_of_mem_line hx hxc hv
  have hwc : w ≠ c := fun e => hw (e ▸ G.left_mem_line c a)
  have hwv : w ∉ G.line c v := G.not_mem_line_of_mem_line hwa₀ hwc hva₀
  rw [key v hvH hv hva₀ hxv, ← G.centralImage_eq_of_base hH hdim hb hvH hv hwH hw hwv,
    G.centralImage_eq_of_base hH hdim (G.isBase_centralImage hH hb hvH hv) hwH hwv hxH hxv hxw]

include htri

omit htri in
theorem centralCollineation_eq {c a b a₀ w x : P} (hb : G.IsBase H c a b) (ha₀H : a₀ ∉ H)
    (ha₀ : a₀ ∉ G.line c a) (hwH : w ∉ H) (hwc : w ≠ c) (hxH : x ∉ H) (hxc : x ≠ c)
    (hxw : x ∉ G.line c w) :
    G.centralCollineation H c a b a₀ x =
      G.centralImage H c w (G.centralCollineation H c a b a₀ w) x := by
  by_cases hw : w ∉ G.line c a
  · exact G.centralCollineation_eq_of_not_mem hH hdim hb ha₀H ha₀ hwH hw hxH hxc hxw
  push Not at hw
  have hca : c ≠ a := Ne.symm hb.ne_center
  have hlw : G.line c w = G.line c a := G.line_eq_of_mem hw hwc
  have hxa : x ∉ G.line c a := hlw ▸ hxw
  have hσ : ¬ G.Collinear c a x := fun h => hxa ((G.collinear_iff_of_ne hca).1 h)
  obtain ⟨v, hvH, hvσ⟩ := hH.exists_not_mem_plane_not_mem hdim hσ
  have hv : v ∉ G.line c a := fun h => hvσ (G.line_subset_plane c a x h)
  have hvx : v ∉ G.line c x := fun h => hvσ (G.line_subset_plane₁₃ hσ h)
  have hxv : x ∉ G.line c v := fun h => hvx (by
    rw [G.line_eq_of_mem h hxc]
    exact G.right_mem_line c v)
  have hwv : w ∉ G.line c v := G.not_mem_line_of_mem_line hw hwc hv
  have h1 := G.centralCollineation_eq_of_not_mem hH hdim hb ha₀H ha₀ hvH hv hxH hxc hxv
  have h2 := G.centralCollineation_eq_of_not_mem hH hdim hb ha₀H ha₀ hvH hv hwH hwc hwv
  have hbv := G.isBase_centralImage hH hb hvH hv
  rw [← G.centralCollineation_of_not_mem_line (a₀ := a₀) hvH hv] at hbv
  rw [h1, h2, G.centralImage_eq_of_base hH hdim hbv hwH hwv hxH hxv hxw]

omit hdim htri in
theorem isBase_centralCollineation {c a b a₀ w : P} (hb : G.IsBase H c a b) (ha₀H : a₀ ∉ H)
    (ha₀ : a₀ ∉ G.line c a) (hwH : w ∉ H) (hwc : w ≠ c) :
    G.IsBase H c w (G.centralCollineation H c a b a₀ w) := by
  by_cases hw : w ∉ G.line c a
  · rw [G.centralCollineation_of_not_mem_line hwH hw]
    exact G.isBase_centralImage hH hb hwH hw
  push Not at hw
  rw [G.centralCollineation_of_mem_line hwH hwc hw]
  exact G.isBase_centralImage hH (G.isBase_centralImage hH hb ha₀H ha₀) hwH
    (G.not_mem_line_of_mem_line hw hwc ha₀)

theorem centralCollineation_spec {c a b a₀ x : P} (hb : G.IsBase H c a b) (ha₀H : a₀ ∉ H)
    (ha₀ : a₀ ∉ G.line c a) (hxH : x ∉ H) (hxc : x ≠ c) :
    G.centralCollineation H c a b a₀ x ∈ G.line c x ∧ G.centralCollineation H c a b a₀ x ∉ H ∧
      G.centralCollineation H c a b a₀ x ≠ c ∧ G.centralCollineation H c a b a₀ x ≠ x := by
  obtain ⟨w, hwH, hwl⟩ := hH.exists_not_mem_line_not_mem hdim htri c x
  have hwc : w ≠ c := fun e => hwl (e ▸ G.left_mem_line c x)
  have hxw : x ∉ G.line c w := fun h => hwl (by
    rw [G.line_eq_of_mem h hxc]
    exact G.right_mem_line c w)
  rw [G.centralCollineation_eq hH hdim hb ha₀H ha₀ hwH hwc hxH hxc hxw]
  obtain ⟨h1, -, h3, h4, h5, -, -⟩ :=
    G.centralImage_spec hH (G.isBase_centralCollineation hH hb ha₀H ha₀ hwH hwc) hxH hxw
  exact ⟨h1, h3, h4, h5⟩

theorem exists_not_mem_line_center {c x y : P} (hxc : x ≠ c) (hyc : y ≠ c)
    (hxy : x ≠ y) : ∃ w, w ∉ H ∧ w ≠ c ∧ x ∉ G.line c w ∧ y ∉ G.line c w := by
  have key : ∀ w, w ∉ G.line c x → w ∉ G.line c y → x ∉ G.line c w ∧ y ∉ G.line c w :=
    fun w hwx hwy => ⟨fun h => hwx (by rw [G.line_eq_of_mem h hxc]; exact G.right_mem_line c w),
      fun h => hwy (by rw [G.line_eq_of_mem h hyc]; exact G.right_mem_line c w)⟩
  by_cases hc : c ∈ G.line x y
  · obtain ⟨w, hwH, hwl⟩ := hH.exists_not_mem_line_not_mem hdim htri x y
    have hwc : w ≠ c := fun e => hwl (e ▸ hc)
    have h1 : G.line c x = G.line x y := G.line_eq_of_center_mem hc (Ne.symm hxc)
    have h2 : G.line c y = G.line x y := by
      rw [G.line_comm x y]
      exact G.line_eq_of_center_mem (G.line_comm x y ▸ hc) (Ne.symm hyc)
    exact ⟨w, hwH, hwc, key w (h1 ▸ hwl) (h2 ▸ hwl)⟩
  have hσ : ¬ G.Collinear c x y := fun h => hc (by
    rcases h.rotate with e | h
    · exact absurd e hxy
    · exact h)
  obtain ⟨w, hwH, hwσ⟩ := hH.exists_not_mem_plane_not_mem hdim hσ
  have hwc : w ≠ c := fun e => hwσ (e ▸ G.left_mem_plane c x y)
  exact ⟨w, hwH, hwc, key w (fun h => hwσ (G.line_subset_plane c x y h))
    (fun h => hwσ (G.line_subset_plane₁₃ hσ h))⟩

theorem isDilatation_centralCollineation {c a b a₀ : P} (hb : G.IsBase H c a b)
    (ha₀H : a₀ ∉ H) (ha₀ : a₀ ∉ G.line c a) :
    G.IsDilatation H (G.centralCollineation H c a b a₀) := by
  have spec := fun {x : P} (hxH : x ∉ H) (hxc : x ≠ c) =>
    G.centralCollineation_spec hH hdim htri hb ha₀H ha₀ hxH hxc
  have main : ∀ x y : P, x ∉ H → y ∉ H → x ≠ y →
      G.centralCollineation H c a b a₀ x ≠ G.centralCollineation H c a b a₀ y ∧
        G.inf H x y ∈ G.line (G.centralCollineation H c a b a₀ x)
          (G.centralCollineation H c a b a₀ y) := by
    intro x y hxH hyH hxy
    by_cases hxc : x = c
    · subst hxc
      rw [G.centralCollineation_center hxH]
      obtain ⟨h1, -, h3, -⟩ := spec hyH (Ne.symm hxy)
      refine ⟨Ne.symm h3, ?_⟩
      rw [G.line_eq_of_mem h1 h3]
      exact hH.inf_mem_line hxy
    by_cases hyc : y = c
    · subst hyc
      rw [G.centralCollineation_center hyH]
      obtain ⟨h1, -, h3, -⟩ := spec hxH hxc
      refine ⟨h3, ?_⟩
      rw [G.line_comm, G.line_eq_of_mem h1 h3, G.line_comm]
      exact hH.inf_mem_line hxy
    obtain ⟨w, hwH, hwc, hxw, hyw⟩ := G.exists_not_mem_line_center hH hdim htri hxc hyc hxy
    rw [G.centralCollineation_eq hH hdim hb ha₀H ha₀ hwH hwc hxH hxc hxw,
      G.centralCollineation_eq hH hdim hb ha₀H ha₀ hwH hwc hyH hyc hyw]
    exact G.centralImage_pair hH hdim (G.isBase_centralCollineation hH hb ha₀H ha₀ hwH
      hwc) hxH hyH hxw hyw hxy
  refine ⟨fun h hh => G.centralCollineation_of_mem hh, fun x hxH => ?_,
    fun x y hxH hyH hxy => (main x y hxH hyH hxy).1,
    fun x y hxH hyH hxy => (main x y hxH hyH hxy).2⟩
  by_cases hxc : x = c
  · subst hxc
    rw [G.centralCollineation_center hxH]
    exact hxH
  · exact (spec hxH hxc).2.1

omit hdim htri in
theorem centralCollineation_apply {c a b a₀ : P} (hb : G.IsBase H c a b) (ha₀H : a₀ ∉ H)
    (ha₀ : a₀ ∉ G.line c a) : G.centralCollineation H c a b a₀ a = b := by
  rw [G.centralCollineation_of_mem_line hb.not_mem hb.ne_center (G.right_mem_line c a)]
  have hb₀ := G.isBase_centralImage hH hb ha₀H ha₀
  have hca : c ≠ a := Ne.symm hb.ne_center
  have haa₀ : a ∉ G.line c a₀ := G.not_mem_line_of_mem_line (G.right_mem_line c a)
    hb.ne_center ha₀
  obtain ⟨-, -, -, -, -, -, huniq⟩ := G.centralImage_spec hH hb₀ hb.not_mem haa₀
  obtain ⟨-, h2, h3, -, -, h6, -⟩ := G.centralImage_spec hH hb ha₀H ha₀
  have haa₀' : a ≠ a₀ := fun e => ha₀ (e ▸ G.right_mem_line c a)
  refine (huniq b hb.mem_line ?_).symm
  rw [← hH.inf_comm hb.not_mem haa₀']
  have hd : G.inf H a a₀ ≠ G.centralImage H c a b a₀ := fun e => h3 (e ▸ hH.inf_mem haa₀')
  rw [G.line_eq_line (Ne.symm hd) h2 (G.right_mem_line b _)]
  exact G.left_mem_line b _

theorem eq_of_isDilatation_center {f : P → P} (hf : G.IsDilatation H f) {c a : P}
    (haH : a ∉ H) (hac : a ≠ c) (hfa : f a = a)
    (hcen : ∀ x, x ∉ H → x ≠ c → f x ∈ G.line c x) (x : P) : f x = x := by
  obtain ⟨z, hzH, hzl⟩ := hH.exists_not_mem_line_not_mem hdim htri c a
  have hza : z ≠ a := fun e => hzl (e ▸ G.right_mem_line c a)
  have hzc : z ≠ c := fun e => hzl (e ▸ G.left_mem_line c a)
  have h1 : f z ∈ G.line c z := hcen z hzH hzc
  have h2 : f z ∈ G.line a z := by
    have := hf.mem_line hH haH hzH (Ne.symm hza)
    rwa [hfa, hH.line_inf haH (Ne.symm hza)] at this
  have hne : G.line c z ≠ G.line a z := fun e => hzl (by
    have hal : a ∈ G.line c z := e ▸ G.left_mem_line a z
    rw [G.line_eq_of_mem hal hac]
    exact G.right_mem_line c z)
  have hfz : f z = z := G.eq_of_mem_of_mem (G.line_mem_lines (Ne.symm hzc))
    (G.line_mem_lines (Ne.symm hza)) hne h1 h2 (G.right_mem_line c z) (G.right_mem_line a z)
  exact hf.eq_of_fixed hH hdim htri haH hzH (Ne.symm hza) hfa hfz x

theorem exists_centralCollineation {c a b : P} (hb : G.IsBase H c a b) :
    ∃ f : Equiv.Perm P, G.IsDilatation H f ∧ f a = b ∧
      (∀ x, x ∉ H → x ≠ c → f x ∈ G.line c x ∧ f x ≠ x) ∧ (c ∉ H → f c = c) := by
  obtain ⟨a₀, ha₀H, ha₀⟩ := hH.exists_not_mem_line_not_mem hdim htri c a
  have hlb : G.line c b = G.line c a := G.line_eq_of_mem hb.mem_line hb.ne_center'
  have hb' : G.IsBase H c b a := ⟨hb.not_mem', hb.not_mem, hb.ne_center', hb.ne_center,
    Ne.symm hb.ne, hlb ▸ G.right_mem_line c a⟩
  have ha₀' : a₀ ∉ G.line c b := hlb ▸ ha₀
  set f := G.centralCollineation H c a b a₀
  set g := G.centralCollineation H c b a a₀
  have hf := G.isDilatation_centralCollineation hH hdim htri hb ha₀H ha₀
  have hg := G.isDilatation_centralCollineation hH hdim htri hb' ha₀H ha₀'
  have hfa : f a = b := G.centralCollineation_apply hH hb ha₀H ha₀
  have hgb : g b = a := G.centralCollineation_apply hH hb' ha₀H ha₀'
  have hfs := fun {x : P} (hxH : x ∉ H) (hxc : x ≠ c) =>
    G.centralCollineation_spec hH hdim htri hb ha₀H ha₀ hxH hxc
  have hgs := fun {x : P} (hxH : x ∉ H) (hxc : x ≠ c) =>
    G.centralCollineation_spec hH hdim htri hb' ha₀H ha₀' hxH hxc
  have hcen : ∀ (φ ψ : P → P), (∀ {x : P}, x ∉ H → x ≠ c → φ x ∈ G.line c x ∧ φ x ∉ H ∧
      φ x ≠ c ∧ φ x ≠ x) → (∀ {x : P}, x ∉ H → x ≠ c → ψ x ∈ G.line c x ∧ ψ x ∉ H ∧
      ψ x ≠ c ∧ ψ x ≠ x) → ∀ x, x ∉ H → x ≠ c → (ψ ∘ φ) x ∈ G.line c x := by
    intro φ ψ hφ hψ x hxH hxc
    obtain ⟨h1, h2, h3, -⟩ := hφ hxH hxc
    obtain ⟨h1', -, -, -⟩ := hψ h2 h3
    change ψ (φ x) ∈ G.line c x
    rw [← G.line_eq_of_mem h1 h3]
    exact h1'
  have hgf : ∀ x, (g ∘ f) x = x := G.eq_of_isDilatation_center hH hdim htri (hg.comp hH hf)
    hb.not_mem hb.ne_center (by simp [hfa, hgb]) (hcen f g hfs hgs)
  have hfg : ∀ x, (f ∘ g) x = x := G.eq_of_isDilatation_center hH hdim htri (hf.comp hH hg)
    hb.not_mem' hb.ne_center' (by simp [hfa, hgb]) (hcen g f hgs hfs)
  refine ⟨⟨f, g, hgf, hfg⟩, hf, hfa, fun x hxH hxc => ⟨(hfs hxH hxc).1, (hfs hxH hxc).2.2.2⟩,
    fun hc => G.centralCollineation_center hc⟩

end ProjectiveSpace

end CFSG.Geometry.ProjectiveSpaces
