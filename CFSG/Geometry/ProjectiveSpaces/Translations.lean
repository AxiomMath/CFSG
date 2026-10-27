module

public import CFSG.Geometry.ProjectiveSpaces.CentralCollineation
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.Geometry.ProjectiveSpaces

namespace ProjectiveSpace

universe u

variable {P : Type u} {G : ProjectiveSpace P} {H : Set P}

structure AffineData (G : ProjectiveSpace P) (H : Set P) : Prop where
  hyperplane : G.IsHyperplane H
  not_mem_plane : ∀ x y z : P, ¬ G.Collinear x y z → ∃ w, w ∉ G.plane x y z
  triangle : ∃ x y z : P, ¬ G.Collinear x y z

@[expose] def IsTranslation (G : ProjectiveSpace P) (H : Set P) (f : P → P) : Prop :=
  G.IsDilatation H f ∧ ((∀ x, f x = x) ∨ ∀ x, x ∉ H → f x ≠ x)

section Hyperplane

variable (hH : G.IsHyperplane H)
include hH

theorem IsDilatation.mem_trace {f : P → P} (hf : G.IsDilatation H f) {x z : P} (hxH : x ∉ H)
    (hzH : z ∉ H) (hfx : f x ≠ x) (hz : z ∈ G.line x (f x)) : f z ∈ G.line x (f x) := by
  by_cases hzx : z = x
  · rw [hzx]
    exact G.right_mem_line x (f x)
  have h1 := hf.mem_line hH hxH hzH (Ne.symm hzx)
  rw [hH.inf_eq_of_mem hxH (Ne.symm hfx) hz hzx] at h1
  have hd : G.inf H x (f x) ≠ f x := fun e => hf.map_not_mem x hxH (e ▸ hH.inf_mem (Ne.symm hfx))
  rwa [G.line_eq_line (Ne.symm hd) (G.right_mem_line x (f x))
    (hH.inf_mem_line (Ne.symm hfx))] at h1

theorem trace_dir_eq {f : P → P} (hf : G.IsDilatation H f) (hfix : ∀ x, x ∉ H → f x ≠ x)
    {x y : P} (hxH : x ∉ H) (hyH : y ∉ H) : G.inf H x (f x) = G.inf H y (f y) := by
  have hfx := hfix x hxH
  have hfy := hfix y hyH
  by_cases hyl : y ∈ G.line x (f x)
  · have h1 := hf.mem_trace hH hxH hyH hfx hyl
    have h2 : G.line y (f y) = G.line x (f x) := G.line_eq_line (Ne.symm hfy) hyl h1
    exact (hH.eq_inf hyH (Ne.symm hfy) (h2 ▸ hH.inf_mem_line (Ne.symm hfx))
      (hH.inf_mem (Ne.symm hfx)))
  have hσ : ¬ G.Collinear x (f x) y := fun h => hyl ((G.collinear_iff_of_ne (Ne.symm hfx)).1 h)
  have hσS := G.isSubspace_plane hσ
  have hxy : x ≠ y := fun e => hyl (e ▸ G.left_mem_line x (f x))
  have hfyσ : f y ∈ G.plane x (f x) y := by
    have h1 := hf.mem_line hH hxH hyH hxy
    exact hσS.line_subset (G.middle_mem_plane _ _ _)
      (hσS.line_subset (G.left_mem_plane _ _ _) (G.right_mem_plane _ _ _)
        (hH.inf_mem_line hxy)) h1
  obtain ⟨z, hz1, hz2⟩ := G.inter_nonempty_of_mem_plane hσ (G.left_mem_plane _ _ _)
    (G.middle_mem_plane _ _ _) (G.right_mem_plane _ _ _) hfyσ (Ne.symm hfx) (Ne.symm hfy)
  by_contra hne
  have hlne : G.line x (f x) ≠ G.line y (f y) := fun e => hne (hH.eq_inf hyH (Ne.symm hfy)
    (e ▸ hH.inf_mem_line (Ne.symm hfx)) (hH.inf_mem (Ne.symm hfx)))
  by_cases hzH : z ∈ H
  · exact hne ((hH.eq_inf hxH (Ne.symm hfx) hz1 hzH).symm.trans
      (hH.eq_inf hyH (Ne.symm hfy) hz2 hzH))
  have h1 := hf.mem_trace hH hxH hzH hfx hz1
  have h2 := hf.mem_trace hH hyH hzH hfy hz2
  exact hfix z hzH (G.eq_of_mem_of_mem (G.line_mem_lines (Ne.symm hfx))
    (G.line_mem_lines (Ne.symm hfy)) hlne h1 h2 hz1 hz2)

omit hH in
theorem IsTranslation.comp (hA : G.AffineData H) {σ τ : P → P} (hσ : G.IsTranslation H σ)
    (hτ : G.IsTranslation H τ) : G.IsTranslation H (σ ∘ τ) := by
  have hH := hA.hyperplane
  refine ⟨hσ.1.comp hH hτ.1, ?_⟩
  by_cases hfix : ∀ x, x ∉ H → (σ ∘ τ) x ≠ x
  · exact Or.inr hfix
  push Not at hfix
  obtain ⟨p, hpH, hp⟩ := hfix
  left
  rcases hτ.2 with hτid | hτfix
  · rcases hσ.2 with hσid | hσfix
    · intro x
      simp [hσid, hτid]
    · exact absurd (by simpa [hτid] using hp) (hσfix p hpH)
  rcases hσ.2 with hσid | hσfix
  · exact absurd (by simpa [hσid] using hp) (hτfix p hpH)
  have hτp := hτfix p hpH
  have hτpH := hτ.1.map_not_mem p hpH
  set d := G.inf H p (τ p) with hd
  have hdσ : ∀ q, q ∉ H → G.inf H q (σ q) = d := fun q hq => by
    rw [trace_dir_eq hH hσ.1 hσfix hq hτpH]
    have hp' : σ (τ p) = p := hp
    rw [hp', hH.inf_comm hτpH hτp]
  have hdτ : ∀ q, q ∉ H → G.inf H q (τ q) = d := fun q hq =>
    trace_dir_eq hH hτ.1 hτfix hq hpH
  obtain ⟨q, hqH, hql⟩ := hH.exists_not_mem_line_not_mem hA.not_mem_plane hA.triangle p (τ p)
  have hpq : p ≠ q := fun e => hql (e ▸ G.left_mem_line p (τ p))
  have hf := hσ.1.comp hH hτ.1
  have h1 : (σ ∘ τ) q ∈ G.line p q := by
    have := hf.mem_line hH hpH hqH hpq
    rwa [hp, hH.line_inf hpH hpq] at this
  have hτq := hτfix q hqH
  have hτqH := hτ.1.map_not_mem q hqH
  have hτql : τ q ∈ G.line q d := by
    rw [← hdτ q hqH, hH.line_inf hqH (Ne.symm hτq)]
    exact G.right_mem_line q (τ q)
  have hdq : d ≠ q := fun e => hqH (e ▸ hH.inf_mem (Ne.symm hτp))
  have h2 : (σ ∘ τ) q ∈ G.line q d := by
    have hστ := hσfix (τ q) hτqH
    have h3 : σ (τ q) ∈ G.line (τ q) d := by
      rw [← hdσ (τ q) hτqH, hH.line_inf hτqH (Ne.symm hστ)]
      exact G.right_mem_line (τ q) (σ (τ q))
    have hτqd : τ q ≠ d := fun e => hτqH (e ▸ hH.inf_mem (Ne.symm hτp))
    rwa [G.line_eq_line hτqd hτql (G.right_mem_line q d)] at h3
  have hne : G.line p q ≠ G.line q d := by
    intro e
    have hdl : d ∈ G.line p q := e ▸ G.right_mem_line q d
    have hdp : d ≠ p := hH.inf_ne hpH (Ne.symm hτp)
    apply hql
    rw [← hH.line_inf hpH (Ne.symm hτp), ← hd, G.line_eq_of_mem hdl hdp]
    exact G.right_mem_line p q
  have hfq : (σ ∘ τ) q = q := G.eq_of_mem_of_mem (G.line_mem_lines hpq)
    (G.line_mem_lines (Ne.symm hdq)) hne h1 h2 (G.right_mem_line p q) (G.left_mem_line q d)
  exact hf.eq_of_fixed hH hA.not_mem_plane hA.triangle hpH hqH hpq hp hfq

theorem IsDilatation.inv {f : Equiv.Perm P} (hf : G.IsDilatation H f) :
    G.IsDilatation H ⇑f⁻¹ := by
  have hfix : ∀ h ∈ H, f⁻¹ h = h := fun h hh => by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hf.map_of_mem h hh).symm
  have hnot : ∀ x, x ∉ H → f⁻¹ x ∉ H := fun x hx hxH => hx (by
    have := hf.map_of_mem _ hxH
    rw [show f (f⁻¹ x) = x from f.apply_symm_apply x] at this
    rw [this]
    exact hxH)
  refine ⟨hfix, hnot, fun x y _ _ hxy e => hxy (f⁻¹.injective e), fun x y hx hy hxy => ?_⟩
  have hne : f⁻¹ x ≠ f⁻¹ y := fun e => hxy (f⁻¹.injective e)
  have h := hf.inf_eq hH (hnot x hx) (hnot y hy) hne
  rw [show f (f⁻¹ x) = x from f.apply_symm_apply x,
    show f (f⁻¹ y) = y from f.apply_symm_apply y] at h
  rw [h]
  exact hH.inf_mem_line hne

theorem IsTranslation.inv {τ : Equiv.Perm P} (hτ : G.IsTranslation H τ) :
    G.IsTranslation H ⇑τ⁻¹ := by
  refine ⟨hτ.1.inv hH, ?_⟩
  rcases hτ.2 with hid | hfx
  · left
    intro x
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hid x).symm
  · right
    intro x hx e
    apply hfx x hx
    rw [Equiv.Perm.inv_eq_iff_eq] at e
    exact e.symm

end Hyperplane

@[expose] def translationGroup (hA : G.AffineData H) : Subgroup (Equiv.Perm P) where
  carrier := {τ | G.IsTranslation H τ}
  mul_mem' := fun {σ τ} hσ hτ => by
    change G.IsTranslation H ⇑(σ * τ)
    rw [Equiv.Perm.coe_mul]
    exact IsTranslation.comp hA hσ hτ
  one_mem' := ⟨hA.hyperplane.isDilatation_id, Or.inl fun _ => rfl⟩
  inv_mem' := fun {τ} hτ => IsTranslation.inv hA.hyperplane hτ

variable {hA : G.AffineData H}

theorem eq_one_of_apply_eq {τ : Equiv.Perm P} (hτ : τ ∈ G.translationGroup hA) {a : P}
    (ha : a ∉ H) (h : τ a = a) : τ = 1 := by
  rcases hτ.2 with hid | hfix
  · exact Equiv.ext hid
  · exact absurd h (hfix a ha)

theorem eq_of_apply_eq {σ τ : Equiv.Perm P} (hσ : σ ∈ G.translationGroup hA)
    (hτ : τ ∈ G.translationGroup hA) {a : P} (ha : a ∉ H) (h : σ a = τ a) : σ = τ := by
  have hρ : σ⁻¹ * τ ∈ G.translationGroup hA := mul_mem (inv_mem hσ) hτ
  have h1 : (σ⁻¹ * τ) a = a := by
    rw [Equiv.Perm.mul_apply, ← h]
    exact σ.symm_apply_apply a
  have := eq_one_of_apply_eq hρ ha h1
  rw [inv_mul_eq_one] at this
  exact this

theorem apply_ne_of_ne_one {τ : Equiv.Perm P} (hτ : τ ∈ G.translationGroup hA) (h1 : τ ≠ 1)
    {x : P} (hx : x ∉ H) : τ x ≠ x := fun h => h1 (eq_one_of_apply_eq hτ hx h)

theorem exists_translation (hA : G.AffineData H) {a b : P} (ha : a ∉ H) (hb : b ∉ H) :
    ∃ τ ∈ G.translationGroup hA, τ a = b := by
  have hH := hA.hyperplane
  by_cases hab : a = b
  · exact ⟨1, one_mem _, hab⟩
  set c := G.inf H a b
  have hcH : c ∈ H := hH.inf_mem hab
  have hbase : G.IsBase H c a b := ⟨ha, hb, Ne.symm (hH.inf_ne ha hab), fun e => hb (e ▸ hcH),
    hab, by rw [G.line_comm, hH.line_inf ha hab]; exact G.right_mem_line a b⟩
  obtain ⟨f, hf, hfa, hcen, -⟩ := G.exists_centralCollineation hH hA.not_mem_plane hA.triangle
    hbase
  refine ⟨f, ⟨hf, Or.inr fun x hx => (hcen x hx fun e => hx (e ▸ hcH)).2⟩, hfa⟩

open Classical in
@[expose] noncomputable def dir (hA : G.AffineData H) (τ : Equiv.Perm P) : P :=
  G.inf H hA.hyperplane.exists_not_mem.choose (τ hA.hyperplane.exists_not_mem.choose)

theorem inf_apply_eq_dir {τ : Equiv.Perm P} (hτ : τ ∈ G.translationGroup hA) (h1 : τ ≠ 1)
    {x : P} (hx : x ∉ H) : G.inf H x (τ x) = G.dir hA τ := by
  have hfix : ∀ y, y ∉ H → τ y ≠ y := fun y hy => apply_ne_of_ne_one hτ h1 hy
  exact trace_dir_eq hA.hyperplane hτ.1 hfix hx hA.hyperplane.exists_not_mem.choose_spec

theorem dir_mem {τ : Equiv.Perm P} (hτ : τ ∈ G.translationGroup hA) (h1 : τ ≠ 1) :
    G.dir hA τ ∈ H := by
  obtain ⟨x, hx⟩ := hA.hyperplane.exists_not_mem
  rw [← inf_apply_eq_dir hτ h1 hx]
  exact hA.hyperplane.inf_mem (Ne.symm (apply_ne_of_ne_one hτ h1 hx))

theorem apply_mem_line_dir {τ : Equiv.Perm P} (hτ : τ ∈ G.translationGroup hA) (h1 : τ ≠ 1)
    {x : P} (hx : x ∉ H) : τ x ∈ G.line x (G.dir hA τ) := by
  rw [← inf_apply_eq_dir hτ h1 hx,
    hA.hyperplane.line_inf hx (Ne.symm (apply_ne_of_ne_one hτ h1 hx))]
  exact G.right_mem_line x (τ x)

@[expose] def HasDir (G : ProjectiveSpace P) (H : Set P) (τ : Equiv.Perm P) (d : P) : Prop :=
  ∀ x, x ∉ H → τ x ∈ G.line x d

theorem hasDir_one (d : P) : G.HasDir H 1 d := fun x _ => G.left_mem_line x d

theorem hasDir_dir {τ : Equiv.Perm P} (hτ : τ ∈ G.translationGroup hA) (h1 : τ ≠ 1) :
    G.HasDir H τ (G.dir hA τ) :=
  fun _ hx => apply_mem_line_dir hτ h1 hx

theorem hasDir_iff {τ : Equiv.Perm P} (hτ : τ ∈ G.translationGroup hA) {d p : P} (hd : d ∈ H)
    (hp : p ∉ H) : G.HasDir H τ d ↔ τ p ∈ G.line p d := by
  refine ⟨fun h => h p hp, fun h => ?_⟩
  by_cases h1 : τ = 1
  · rw [h1]
    exact hasDir_one d
  have hτp := apply_ne_of_ne_one hτ h1 hp
  have he : G.dir hA τ = d := by
    rw [← inf_apply_eq_dir hτ h1 hp]
    have hl : G.line p (τ p) = G.line p d := G.line_eq_of_mem h hτp
    refine (hA.hyperplane.eq_inf hp (Ne.symm hτp) ?_ hd).symm
    rw [hl]
    exact G.right_mem_line p d
  have := hasDir_dir hτ h1
  rwa [he] at this

theorem HasDir.dir_eq {τ : Equiv.Perm P} {d : P} (h : G.HasDir H τ d)
    (hτ : τ ∈ G.translationGroup hA) (h1 : τ ≠ 1) (hd : d ∈ H) : G.dir hA τ = d := by
  obtain ⟨x, hx⟩ := hA.hyperplane.exists_not_mem
  have hτx := apply_ne_of_ne_one hτ h1 hx
  rw [← inf_apply_eq_dir hτ h1 hx]
  have hl : G.line x (τ x) = G.line x d := G.line_eq_of_mem (h x hx) hτx
  refine (hA.hyperplane.eq_inf hx (Ne.symm hτx) ?_ hd).symm
  rw [hl]
  exact G.right_mem_line x d

theorem HasDir.eq_one {τ : Equiv.Perm P} {d e : P} (h : G.HasDir H τ d) (h' : G.HasDir H τ e)
    (hτ : τ ∈ G.translationGroup hA) (hd : d ∈ H) (he : e ∈ H) (hde : d ≠ e) : τ = 1 := by
  by_contra h1
  exact hde ((h.dir_eq hτ h1 hd).symm.trans (h'.dir_eq hτ h1 he))

theorem HasDir.mul {σ τ : Equiv.Perm P} {d : P} (hσd : G.HasDir H σ d) (hτd : G.HasDir H τ d)
    (hτ : G.IsDilatation H τ) (hd : d ∈ H) : G.HasDir H (σ * τ) d := by
  intro x hx
  have hτxH := hτ.map_not_mem x hx
  have h := hσd (τ x) hτxH
  rw [Equiv.Perm.mul_apply]
  have hne : τ x ≠ d := fun e => hτxH (e ▸ hd)
  rwa [G.line_eq_line hne (hτd x hx) (G.right_mem_line x d)] at h

theorem HasDir.inv {τ : Equiv.Perm P} {d : P} (h : G.HasDir H τ d) (hτ : G.IsDilatation H τ)
    (hd : d ∈ H) : G.HasDir H τ⁻¹ d := by
  intro x hx
  have hτx : τ (τ⁻¹ x) = x := τ.apply_symm_apply x
  have hy : τ⁻¹ x ∉ H := fun hy => hx (by
    have := hτ.map_of_mem _ hy
    rw [hτx] at this
    rw [this]
    exact hy)
  have h1 := h _ hy
  rw [hτx] at h1
  have hxd : x ≠ d := fun e => hx (e ▸ hd)
  rw [G.line_eq_line hxd h1 (G.right_mem_line _ d)]
  exact G.left_mem_line _ d

theorem exists_hasDir (hA : G.AffineData H) {d : P} (hd : d ∈ H) :
    ∃ τ ∈ G.translationGroup hA, τ ≠ 1 ∧ G.HasDir H τ d := by
  have hH := hA.hyperplane
  obtain ⟨x, hx⟩ := hH.exists_not_mem
  have hxd : x ≠ d := fun e => hx (e ▸ hd)
  obtain ⟨y, hy, hyx, hyd⟩ := G.exists_mem_line_ne hxd
  have hyH : y ∉ H := fun hyH => hyd (hH.eq_of_mem_line hx hy (G.right_mem_line x d) hyH hd)
  obtain ⟨τ, hτ, hτx⟩ := G.exists_translation hA hx hyH
  have h1 : τ ≠ 1 := fun e => hyx (by rw [← hτx, e]; rfl)
  refine ⟨τ, hτ, h1, (hasDir_iff hτ hd hx).2 ?_⟩
  rw [hτx]
  exact hy

theorem exists_dir_ne (hA : G.AffineData H) {d : P} :
    ∃ ρ ∈ G.translationGroup hA, ρ ≠ 1 ∧ G.dir hA ρ ≠ d := by
  have hH := hA.hyperplane
  obtain ⟨x, hx⟩ := hH.exists_not_mem
  obtain ⟨y, hy, hyl⟩ := hH.exists_not_mem_line_not_mem hA.not_mem_plane hA.triangle x d
  obtain ⟨ρ, hρ, hρx⟩ := G.exists_translation hA hx hy
  have hρ1 : ρ ≠ 1 := fun e => hyl (by rw [← hρx, e]; exact G.left_mem_line x d)
  refine ⟨ρ, hρ, hρ1, fun e => ?_⟩
  have := apply_mem_line_dir hρ hρ1 hx
  rw [e, hρx] at this
  exact hyl this

theorem mul_comm_of_dir_ne {σ τ : Equiv.Perm P} (hσ : σ ∈ G.translationGroup hA)
    (hτ : τ ∈ G.translationGroup hA) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1)
    (hne : G.dir hA σ ≠ G.dir hA τ) : σ * τ = τ * σ := by
  have hH := hA.hyperplane
  obtain ⟨x, hx⟩ := hH.exists_not_mem
  refine eq_of_apply_eq (mul_mem hσ hτ) (mul_mem hτ hσ) hx ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  have hσx := apply_ne_of_ne_one hσ hσ1 hx
  have hτx := apply_ne_of_ne_one hτ hτ1 hx
  have hσxH := hσ.1.map_not_mem x hx
  have hτxH := hτ.1.map_not_mem x hx
  have hdσ := dir_mem hσ hσ1
  have hdτ := dir_mem hτ hτ1
  have h1 : τ (σ x) ∈ G.line (τ x) (G.dir hA σ) := by
    have := hτ.1.mem_line hH hx hσxH (Ne.symm hσx)
    rwa [inf_apply_eq_dir hσ hσ1 hx] at this
  have h2 : τ (σ x) ∈ G.line (σ x) (G.dir hA τ) := apply_mem_line_dir hτ hτ1 hσxH
  have h3 : σ (τ x) ∈ G.line (τ x) (G.dir hA σ) := apply_mem_line_dir hσ hσ1 hτxH
  have h4 : σ (τ x) ∈ G.line (σ x) (G.dir hA τ) := by
    have := hσ.1.mem_line hH hx hτxH (Ne.symm hτx)
    rwa [inf_apply_eq_dir hτ hτ1 hx] at this
  have hl : G.line (τ x) (G.dir hA σ) ≠ G.line (σ x) (G.dir hA τ) := by
    intro e
    have : G.dir hA σ ∈ G.line (σ x) (G.dir hA τ) := by
      rw [← e]
      exact G.right_mem_line _ _
    exact hne (hH.eq_of_mem_line hσxH this (G.right_mem_line _ _) hdσ hdτ)
  have hn1 : τ x ≠ G.dir hA σ := fun e => hτxH (e ▸ hdσ)
  have hn2 : σ x ≠ G.dir hA τ := fun e => hσxH (e ▸ hdτ)
  exact G.eq_of_mem_of_mem (G.line_mem_lines hn1) (G.line_mem_lines hn2) hl h3 h4 h1 h2

theorem translation_mul_comm {σ τ : Equiv.Perm P} (hσ : σ ∈ G.translationGroup hA)
    (hτ : τ ∈ G.translationGroup hA) : σ * τ = τ * σ := by
  by_cases hσ1 : σ = 1
  · rw [hσ1, one_mul, mul_one]
  by_cases hτ1 : τ = 1
  · rw [hτ1, one_mul, mul_one]
  by_cases hne : G.dir hA σ ≠ G.dir hA τ
  · exact mul_comm_of_dir_ne hσ hτ hσ1 hτ1 hne
  have hne' : G.dir hA σ = G.dir hA τ := Classical.not_not.1 hne
  set d := G.dir hA σ with hd_def
  have hd : d ∈ H := dir_mem hσ hσ1
  obtain ⟨ρ, hρ, hρ1, hρd⟩ := G.exists_dir_ne hA (d := d)
  have hdρ := dir_mem hρ hρ1
  have hσρ := mul_mem hσ hρ
  have hσρ1 : σ * ρ ≠ 1 := by
    intro e
    have hs : σ = ρ⁻¹ := eq_inv_of_mul_eq_one_left e
    have h1 : G.HasDir H σ (G.dir hA ρ) := by
      rw [hs]
      exact (hasDir_dir hρ hρ1).inv hρ.1 hdρ
    exact hσ1 ((hasDir_dir hσ hσ1).eq_one h1 hσ hd hdρ (Ne.symm hρd))
  have hσρd : G.dir hA (σ * ρ) ≠ d := by
    intro e
    have h1 : G.HasDir H (σ * ρ) d := by
      rw [← e]
      exact hasDir_dir hσρ hσρ1
    have h2 : G.HasDir H (σ⁻¹ * (σ * ρ)) d :=
      ((hasDir_dir hσ hσ1).inv hσ.1 hd).mul h1 hσρ.1 hd
    rw [inv_mul_cancel_left] at h2
    exact hρ1 ((hasDir_dir hρ hρ1).eq_one h2 hρ hdρ hd hρd)
  have e1 : τ * (σ * ρ) = σ * ρ * τ :=
    mul_comm_of_dir_ne hτ hσρ hτ1 hσρ1 (by rw [← hne']; exact Ne.symm hσρd)
  have e2 : τ * ρ = ρ * τ := mul_comm_of_dir_ne hτ hρ hτ1 hρ1 (by rw [← hne']; exact Ne.symm hρd)
  have e3 : σ * τ * ρ = τ * σ * ρ := calc
    σ * τ * ρ = σ * (τ * ρ) := mul_assoc _ _ _
    _ = σ * (ρ * τ) := by rw [e2]
    _ = σ * ρ * τ := (mul_assoc _ _ _).symm
    _ = τ * (σ * ρ) := e1.symm
    _ = τ * σ * ρ := (mul_assoc _ _ _).symm
  exact mul_right_cancel e3

end ProjectiveSpace

end CFSG.Geometry.ProjectiveSpaces
