module

public import CFSG.Geometry.ProjectiveSpaces.Desargues
public import Mathlib.Tactic.Attr.Core

public section

namespace CFSG.Geometry.ProjectiveSpaces

namespace ProjectiveSpace

universe u

variable {P : Type u} (G : ProjectiveSpace P)

structure IsHyperplane (H : Set P) : Prop where
  isSubspace : G.IsSubspace H
  exists_not_mem : ∃ x, x ∉ H
  inter_nonempty : ∀ p q : P, p ≠ q → (G.line p q ∩ H).Nonempty

variable {G} {H : Set P}

open Classical in
@[expose] noncomputable def inf (G : ProjectiveSpace P) (H : Set P) (x y : P) : P :=
  if h : (G.line x y ∩ H).Nonempty then h.some else x

theorem IsHyperplane.inf_mem_inter (hH : G.IsHyperplane H) {x y : P} (hxy : x ≠ y) :
    G.inf H x y ∈ G.line x y ∩ H := by
  have h := hH.inter_nonempty x y hxy
  rw [inf, dite_eq_left h]
  exact h.some_mem

theorem IsHyperplane.inf_mem_line (hH : G.IsHyperplane H) {x y : P} (hxy : x ≠ y) :
    G.inf H x y ∈ G.line x y := (hH.inf_mem_inter hxy).1

theorem IsHyperplane.inf_mem (hH : G.IsHyperplane H) {x y : P} (hxy : x ≠ y) :
    G.inf H x y ∈ H := (hH.inf_mem_inter hxy).2

theorem IsHyperplane.eq_of_mem_line (hH : G.IsHyperplane H) {x y z w : P} (hx : x ∉ H)
    (hz : z ∈ G.line x y) (hw : w ∈ G.line x y) (hzH : z ∈ H) (hwH : w ∈ H) : z = w :=
  G.eq_of_mem_line_of_not_mem hH.isSubspace hx hz hw hzH hwH

theorem IsHyperplane.eq_inf (hH : G.IsHyperplane H) {x y z : P} (hx : x ∉ H) (hxy : x ≠ y)
    (hz : z ∈ G.line x y) (hzH : z ∈ H) : z = G.inf H x y :=
  hH.eq_of_mem_line hx hz (hH.inf_mem_line hxy) hzH (hH.inf_mem hxy)

theorem IsHyperplane.inf_ne (hH : G.IsHyperplane H) {x y : P} (hx : x ∉ H) (hxy : x ≠ y) :
    G.inf H x y ≠ x := fun e => hx (e ▸ hH.inf_mem hxy)

theorem IsHyperplane.line_inf (hH : G.IsHyperplane H) {x y : P} (hx : x ∉ H) (hxy : x ≠ y) :
    G.line x (G.inf H x y) = G.line x y :=
  G.line_eq_of_mem (hH.inf_mem_line hxy) (hH.inf_ne hx hxy)

theorem IsHyperplane.inf_comm (hH : G.IsHyperplane H) {x y : P} (hx : x ∉ H)
    (hxy : x ≠ y) : G.inf H x y = G.inf H y x :=
  hH.eq_inf hx hxy (G.line_comm y x ▸ hH.inf_mem_line (Ne.symm hxy)) (hH.inf_mem (Ne.symm hxy))
    |>.symm

theorem IsHyperplane.inf_eq_of_mem (hH : G.IsHyperplane H) {x y z : P} (hx : x ∉ H)
    (hxy : x ≠ y) (hz : z ∈ G.line x y) (hzx : z ≠ x) : G.inf H x z = G.inf H x y :=
  hH.eq_inf hx hxy (G.line_eq_of_mem hz hzx ▸ hH.inf_mem_line (Ne.symm hzx)) (hH.inf_mem
    (Ne.symm hzx))

theorem IsHyperplane.inf_eq_of_mem_line (hH : G.IsHyperplane H) {x y x' y' : P} (hx' : x' ∉ H)
    (hxy : x ≠ y) (hxy' : x' ≠ y') (h : G.inf H x y ∈ G.line x' y') :
    G.inf H x' y' = G.inf H x y :=
  (hH.eq_inf hx' hxy' h (hH.inf_mem hxy)).symm

theorem IsHyperplane.exists_not_mem_plane_not_mem (hH : G.IsHyperplane H)
    (hdim : ∀ x y z : P, ¬ G.Collinear x y z → ∃ w, w ∉ G.plane x y z) {x y z : P}
    (h : ¬ G.Collinear x y z) : ∃ w, w ∉ H ∧ w ∉ G.plane x y z := by
  by_contra hall
  push Not at hall
  have hπ := G.isSubspace_plane h
  obtain ⟨x₀, hx₀⟩ := hH.exists_not_mem
  have hx₀π : x₀ ∈ G.plane x y z := hall x₀ hx₀
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ ∈ H, h₀ ∉ G.plane x y z := by
    obtain ⟨w, hw⟩ := hdim x y z h
    by_cases hwH : w ∈ H
    · exact ⟨w, hwH, hw⟩
    · exact absurd (hall w hwH) hw
  have hne : x₀ ≠ h₀ := fun e => hx₀ (e ▸ hh₀.1)
  obtain ⟨w, hw, hwx, hwh⟩ := G.exists_mem_line_ne hne
  have hwH : w ∉ H := fun hwH => hwh (hH.eq_of_mem_line hx₀ hw (G.right_mem_line x₀ h₀) hwH hh₀.1)
  have hwπ := hall w hwH
  exact hh₀.2 (hπ.line_subset hx₀π hwπ (G.line_eq_line (Ne.symm hwx) (G.left_mem_line x₀ h₀) hw
    ▸ G.right_mem_line x₀ h₀))

structure IsDilatation (G : ProjectiveSpace P) (H : Set P) (f : P → P) : Prop where
  map_of_mem : ∀ h ∈ H, f h = h
  map_not_mem : ∀ x ∉ H, f x ∉ H
  map_ne : ∀ x y, x ∉ H → y ∉ H → x ≠ y → f x ≠ f y
  inf_mem_line : ∀ x y, x ∉ H → y ∉ H → x ≠ y → G.inf H x y ∈ G.line (f x) (f y)

theorem IsHyperplane.isDilatation_id (hH : G.IsHyperplane H) : G.IsDilatation H id :=
  ⟨fun _ _ => rfl, fun _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => hH.inf_mem_line h⟩

variable (hH : G.IsHyperplane H)
include hH

theorem IsDilatation.inf_eq {f : P → P} (hf : G.IsDilatation H f) {x y : P} (hx : x ∉ H)
    (hy : y ∉ H) (hxy : x ≠ y) : G.inf H (f x) (f y) = G.inf H x y :=
  hH.inf_eq_of_mem_line (hf.map_not_mem x hx) hxy (hf.map_ne x y hx hy hxy)
    (hf.inf_mem_line x y hx hy hxy)

theorem IsDilatation.mem_line {f : P → P} (hf : G.IsDilatation H f) {x y : P} (hx : x ∉ H)
    (hy : y ∉ H) (hxy : x ≠ y) : f y ∈ G.line (f x) (G.inf H x y) := by
  have hfx := hf.map_not_mem x hx
  have hne := hf.map_ne x y hx hy hxy
  rw [← hf.inf_eq hH hx hy hxy, hH.line_inf hfx hne]
  exact G.right_mem_line _ _

theorem IsDilatation.comp {f g : P → P} (hf : G.IsDilatation H f) (hg : G.IsDilatation H g) :
    G.IsDilatation H (f ∘ g) := by
  refine ⟨fun h hh => ?_, fun x hx => hf.map_not_mem _ (hg.map_not_mem x hx),
    fun x y hx hy hxy => hf.map_ne _ _ (hg.map_not_mem x hx) (hg.map_not_mem y hy)
      (hg.map_ne x y hx hy hxy), fun x y hx hy hxy => ?_⟩
  · change f (g h) = h
    rw [hg.map_of_mem h hh, hf.map_of_mem h hh]
  · rw [← hg.inf_eq hH hx hy hxy]
    exact hf.inf_mem_line _ _ (hg.map_not_mem x hx) (hg.map_not_mem y hy) (hg.map_ne x y hx hy hxy)

theorem IsDilatation.eq_of_fixed_of_not_mem {f : P → P} (hf : G.IsDilatation H f) {x y z : P}
    (hx : x ∉ H) (hy : y ∉ H) (hxy : x ≠ y) (hfx : f x = x) (hfy : f y = y) (hz : z ∉ H)
    (hzl : z ∉ G.line x y) : f z = z := by
  have hzx : z ≠ x := fun e => hzl (e ▸ G.left_mem_line x y)
  have hzy : z ≠ y := fun e => hzl (e ▸ G.right_mem_line x y)
  have h1 : f z ∈ G.line x z := by
    have := hf.mem_line hH hx hz (Ne.symm hzx)
    rwa [hfx, hH.line_inf hx (Ne.symm hzx)] at this
  have h2 : f z ∈ G.line y z := by
    have := hf.mem_line hH hy hz (Ne.symm hzy)
    rwa [hfy, hH.line_inf hy (Ne.symm hzy)] at this
  have hne : G.line x z ≠ G.line y z := by
    intro e
    have hyl : y ∈ G.line x z := e ▸ G.left_mem_line y z
    apply hzl
    rw [G.line_eq_of_mem hyl (Ne.symm hxy)]
    exact G.right_mem_line x z
  exact G.eq_of_mem_of_mem (G.line_mem_lines (Ne.symm hzx)) (G.line_mem_lines (Ne.symm hzy)) hne
    h1 h2 (G.right_mem_line x z) (G.right_mem_line y z)

omit hH in
theorem IsHyperplane.exists_ne_not_mem (hH : G.IsHyperplane H) {p q : P} (hpq : p ≠ q)
    {x : P} (hx : x ∉ H) : ∃ y, y ∉ H ∧ y ≠ x := by
  obtain ⟨z, hzx⟩ : ∃ z, z ≠ x := by
    by_cases hp : p = x
    · exact ⟨q, fun e => hpq (hp.trans e.symm)⟩
    · exact ⟨p, hp⟩
  have hh := hH.inf_mem_inter (Ne.symm hzx)
  have hxh : x ≠ G.inf H x z := Ne.symm (hH.inf_ne hx (Ne.symm hzx))
  obtain ⟨y, hy, hyx, hyh⟩ := G.exists_mem_line_ne hxh
  refine ⟨y, fun hyH => hyh ?_, hyx⟩
  exact hH.eq_of_mem_line hx hy (G.right_mem_line x _) hyH hh.2

omit hH in
theorem IsHyperplane.exists_not_mem_line_not_mem (hH : G.IsHyperplane H)
    (hdim : ∀ x y z : P, ¬ G.Collinear x y z → ∃ w, w ∉ G.plane x y z)
    (htri : ∃ x y z : P, ¬ G.Collinear x y z) (p q : P) :
    ∃ w, w ∉ H ∧ w ∉ G.line p q := by
  obtain ⟨a, b, c, habc⟩ := htri
  obtain ⟨hab, -, -⟩ := G.ne_of_not_collinear habc
  by_cases hpq : p = q
  · subst hpq
    rw [line_self]
    by_cases hpH : p ∈ H
    · obtain ⟨x, hx⟩ := hH.exists_not_mem
      exact ⟨x, hx, fun e => hx (e ▸ hpH)⟩
    · obtain ⟨y, hy, hyp⟩ := hH.exists_ne_not_mem hab hpH
      exact ⟨y, hy, hyp⟩
  obtain ⟨z, hz⟩ : ∃ z, z ∉ G.line p q := by
    by_contra hall
    push Not at hall
    exact habc (G.collinear_of_mem_line (hall a) (hall b) (hall c))
  have hpqz : ¬ G.Collinear p q z := fun h => hz ((G.collinear_iff_of_ne hpq).1 h)
  obtain ⟨w, hw, hwπ⟩ := hH.exists_not_mem_plane_not_mem hdim hpqz
  exact ⟨w, hw, fun hwl => hwπ (G.line_subset_plane p q z hwl)⟩

theorem IsDilatation.eq_of_fixed {f : P → P} (hf : G.IsDilatation H f)
    (hdim : ∀ x y z : P, ¬ G.Collinear x y z → ∃ w, w ∉ G.plane x y z)
    (htri : ∃ x y z : P, ¬ G.Collinear x y z) {x y : P} (hx : x ∉ H) (hy : y ∉ H)
    (hxy : x ≠ y) (hfx : f x = x) (hfy : f y = y) (z : P) : f z = z := by
  by_cases hzH : z ∈ H
  · exact hf.map_of_mem z hzH
  by_cases hzl : z ∉ G.line x y
  · exact hf.eq_of_fixed_of_not_mem hH hx hy hxy hfx hfy hzH hzl
  push Not at hzl
  by_cases hzx : z = x
  · rw [hzx, hfx]
  obtain ⟨w, hw, hwl⟩ := hH.exists_not_mem_line_not_mem hdim htri x y
  have hxw : x ≠ w := fun e => hwl (e ▸ G.left_mem_line x y)
  have hfw := hf.eq_of_fixed_of_not_mem hH hx hy hxy hfx hfy hw hwl
  refine hf.eq_of_fixed_of_not_mem hH hx hw hxw hfx hfw hzH fun hzw => hwl ?_
  rw [← G.line_eq_of_mem hzl hzx, G.line_eq_of_mem hzw hzx]
  exact G.right_mem_line x w

end ProjectiveSpace

end CFSG.Geometry.ProjectiveSpaces
