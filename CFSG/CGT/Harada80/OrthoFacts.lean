module

public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
public import CFSG.LargeExtraspecial.OrthoF2Basic
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizer
public import CFSG.Timmesfeld.TransvectionActions.CommonCenterFixedSpace

public section

namespace CFSG.CGT.Harada80

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LargeExtraspecial (eq_one_of_fix_orthogonal_of_map_eq_zero)
open CFSG.LargeExtraspecial.OrthoF2
open CFSG.Timmesfeld.TransvectionActions

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

@[expose] def IsRootElt (Q : QuadraticForm (ZMod 2) V) (a : V) (g : V ≃ₗ[ZMod 2] V) : Prop :=
  g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ g a = a ∧
    ∀ z, polar Q z a = 0 → g z - z ∈ (ZMod 2) ∙ a

private abbrev rootPerp (a : V) : Submodule (ZMod 2) V :=
  LinearMap.BilinForm.orthogonal (polarBilin Q) ((ZMod 2) ∙ a)

private theorem rootPerp_self {a : V} (ha : Q a = 0) : a ∈ rootPerp (Q := Q) a :=
  mem_orth_span_single_iff.mpr (polar_self_eq_zero ha)

private theorem rootPerp_mapsTo {a : V} {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hE : ∀ g ∈ E, IsRootElt Q a g) (g : E) :
    ∀ z : rootPerp (Q := Q) a, g.1 z.1 ∈ rootPerp (Q := Q) a := by
  intro z
  dsimp only [rootPerp] at z ⊢
  rw [mem_orth_span_single_iff]
  have hz : polar Q a z.1 = 0 := mem_orth_span_single_iff.mp z.2
  have hga := (hE g g.2).2.1
  calc polar Q a (g.1 z.1) = polar Q (g.1 a) (g.1 z.1) := by rw [hga]
    _ = polar Q a z.1 := polar_map_of_mem (hE g g.2).1 a z.1
    _ = 0 := hz

private noncomputable def rootAction {a : V} (E : Subgroup (V ≃ₗ[ZMod 2] V))
    (hE : ∀ g ∈ E, IsRootElt Q a g) : Representation (ZMod 2) E (rootPerp (Q := Q) a) :=
  let fP : E → Module.End (ZMod 2) (rootPerp (Q := Q) a) := fun g =>
    { toFun := fun z => ⟨g.1 z.1, rootPerp_mapsTo hE g z⟩
      map_add' := by intro z w; ext; simp
      map_smul' := by intro c z; ext; simp }
  MonoidHom.mk (OneHom.mk fP (by ext z; rfl)) (by intro g h; ext z; rfl)

private theorem rootAction_apply {a : V} {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hE : ∀ g ∈ E, IsRootElt Q a g) (g : E) (z : rootPerp (Q := Q) a) :
    (rootAction E hE g z : V) = g.1 z.1 := rfl

private theorem apply_eq_self_of_sub_mem_span_of_polar_ne_zero {a : V} (ha : Q a = 0)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {z : V}
    (hz : polar Q z a ≠ 0) (hsub : g z - z ∈ (ZMod 2) ∙ a) : g z = z := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hsub
  have hgz : g z = z + c • a := by rw [hc]; abel
  have hQ := map_of_mem hg z
  rw [hgz] at hQ
  have hQadd : Q (z + c • a) = Q z + c * polar Q z a := by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq Q c a, ha, mul_zero,
      polar_smul_right_eq Q c z a]
    ring
  rw [hQadd] at hQ
  have hcoeff : c * polar Q z a = 0 := add_eq_left.mp hQ
  have hc0 : c = 0 := (mul_eq_zero.mp hcoeff).resolve_right hz
  rw [hc0, zero_smul, add_zero] at hgz
  exact hgz

theorem eq_one_of_forall_sub_mem_span (hQ : (polarBilin Q).Nondegenerate) {a : V}
    (ha : Q a = 0) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h : ∀ x, g x - x ∈ (ZMod 2) ∙ a) : g = 1 := by
  by_cases ha0 : a = 0
  · subst a
    refine eq_one_of_fix_orthogonal_of_map_eq_zero hQ ha hg ?_
    intro x _
    simpa [sub_eq_zero] using h x
  · obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ ha0
    have hy' : polar Q y a ≠ 0 := by rwa [polar_comm] at hy
    have hy1 : polar Q y a = 1 := zmod2_eq_one_of_ne_zero hy'
    have hyfix : g y = y :=
      apply_eq_self_of_sub_mem_span_of_polar_ne_zero ha hg hy' (h y)
    refine eq_one_of_fix_orthogonal_of_map_eq_zero hQ ha hg ?_
    intro x hx
    have hx' : polar Q x a = 0 := by rwa [polar_comm] at hx
    have hxy : polar Q (x + y) a ≠ 0 := by
      rw [QuadraticMap.polar_add_left, hx', hy1]
      exact one_ne_zero
    have hxyfix : g (x + y) = x + y :=
      apply_eq_self_of_sub_mem_span_of_polar_ne_zero ha hg hxy (h (x + y))
    have h1 : g (x + y) = g x + g y := map_add g x y
    rw [hxyfix, hyfix] at h1
    exact (add_right_cancel h1).symm

theorem apply_eq_of_sub_mem_span_of_map_eq_one {b : V} (hb : Q b = 1)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {z : V}
    (hz : polar Q z b = 0) (h : g z - z ∈ (ZMod 2) ∙ b) : g z = z := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have hgz : g z = z + c • b := by rw [hc]; abel
  have hQ := map_of_mem hg z
  rw [hgz] at hQ
  have hQadd : Q (z + c • b) = Q z + c := by
    rw [QuadraticMap.map_add Q, map_smul_zmod2 Q c b, hb, mul_one,
      polar_smul_right_eq Q c z b, hz]
    ring
  rw [hQadd] at hQ
  have hc0 : c = 0 := add_eq_left.mp hQ
  rw [hc0, zero_smul, add_zero] at hgz
  exact hgz

theorem IsRootElt.eq_one_of_apply_eq (hQ : (polarBilin Q).Nondegenerate) {a : V}
    (ha : Q a = 0) {g : V ≃ₗ[ZMod 2] V} (hg : IsRootElt Q a g) {y : V}
    (hy : polar Q y a ≠ 0) (hgy : g y = y) : g = 1 := by
  refine eq_one_of_fix_orthogonal_of_map_eq_zero hQ ha hg.1 ?_
  intro z hz
  have hz' : polar Q z a = 0 := by rwa [polar_comm] at hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hg.2.2 z hz')
  have hgz : g z = z + c • a := by rw [hc]; abel
  have hmap := polar_map_of_mem hg.1 z y
  rw [hgz, hgy] at hmap
  have hmap' : polar Q z y + c * polar Q a y = polar Q z y := by
    calc polar Q z y + c * polar Q a y
        = polar Q z y + polar Q (c • a) y := by
          rw [polar_smul_left_eq Q c a y]
      _ = polar Q (z + c • a) y := by
          rw [QuadraticMap.polar_add_left]
      _ = polar Q z y := hmap
  have hcoeff : c * polar Q a y = 0 := add_eq_left.mp hmap'
  have hay : polar Q a y ≠ 0 := by rwa [polar_comm]
  have hc0 : c = 0 := (mul_eq_zero.mp hcoeff).resolve_right hay
  rw [hc0, zero_smul, add_zero] at hgz
  exact hgz

theorem IsRootElt.exists_sub_eq (hQ : (polarBilin Q).Nondegenerate) {a : V}
    (ha : Q a = 0) {g : V ≃ₗ[ZMod 2] V} (hg : IsRootElt Q a g) (hg1 : g ≠ 1) :
    ∃ z, polar Q z a = 0 ∧ g z - z = a := by
  by_contra hcon
  push Not at hcon
  have hfix : ∀ z, polar Q a z = 0 → g z = z := by
    intro z hz
    have hz' : polar Q z a = 0 := by rwa [polar_comm] at hz
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hg.2.2 z hz')
    rcases zmod2_eq_zero_or_eq_one c with h0 | h1
    · rw [h0, zero_smul] at hc
      exact sub_eq_zero.mp hc.symm
    · rw [h1, one_smul] at hc
      exact absurd hc.symm (hcon z hz')
  exact hg1 (eq_one_of_fix_orthogonal_of_map_eq_zero hQ ha hg.1 hfix)

theorem reflect_apply_eq_self_iff {b : V} (hb : Q b = 1) {x : V} :
    reflect Q b x = x ↔ polar Q x b = 0 := by
  have hb0 : b ≠ 0 := fun h0 => by rw [h0, map_zero] at hb; exact zero_ne_one hb
  constructor
  · intro h
    have h1 := h
    rw [reflect_apply_of_map_eq_one hb] at h1
    have h' : polar Q x b • b = 0 := add_eq_left.mp h1
    exact (smul_eq_zero.mp h').resolve_right hb0
  · intro h
    calc reflect Q b x = x + polar Q x b • b := reflect_apply_of_map_eq_one hb x
      _ = x := by rw [h, zero_smul, add_zero]

private theorem exists_singular_in_submodule {W : Submodule (ZMod 2) V}
    (hW : 3 ≤ Module.finrank (ZMod 2) W) : ∃ w ∈ W, w ≠ 0 ∧ Q w = 0 := by
  obtain ⟨w, hw0, hQw⟩ :=
    exists_ne_zero_map_eq_zero (V := W) (Q := Q.restrict W) hW
  exact ⟨w.1, w.2, fun h => hw0 (Subtype.ext h), by simpa using hQw⟩

private theorem finrank_span_pair_eq_two_of_singular_nonsingular {u b : V}
    (hu : Q u = 0) (hb : Q b = 1) (hu0 : u ≠ 0) (hub : u ≠ b) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({u, b} : Set V)) = 2 := by
  have hb0 : b ≠ 0 := fun h0 => by rw [h0, map_zero] at hb; exact zero_ne_one hb
  have hli : LinearIndependent (ZMod 2) ![u, b] := by
    rw [LinearIndependent.pair_iff' hu0]
    intro a ha
    rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
    · rw [zero_smul] at ha
      exact hb0 ha.symm
    · rw [one_smul] at ha
      exact hub ha
  rw [← Matrix.range_cons_cons_empty u b ![]]
  simpa using finrank_span_eq_card hli

private theorem exists_singular_ne_of_finrank_four {R : Submodule (ZMod 2) V} {u₁ : V}
    (hu₁R : u₁ ∈ R) (hu₁Q : Q u₁ = 0) (hu₁0 : u₁ ≠ 0)
    (hR : 4 ≤ Module.finrank (ZMod 2) R) :
    ∃ u₂ ∈ R, Q u₂ = 0 ∧ u₂ ≠ 0 ∧ u₂ ≠ u₁ := by
  let pR : Submodule (ZMod 2) R := Submodule.span (ZMod 2) {⟨u₁, hu₁R⟩}
  have hpRdim : Module.finrank (ZMod 2) pR = 1 := by
    refine finrank_span_singleton ?_
    intro h
    exact hu₁0 (congrArg Subtype.val h)
  obtain ⟨qR, hcompl⟩ := Submodule.exists_isCompl pR
  have hqRdim : Module.finrank (ZMod 2) qR = Module.finrank (ZMod 2) R - 1 := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  let C : Submodule (ZMod 2) V := qR.map R.subtype
  have hCdim : Module.finrank (ZMod 2) C = Module.finrank (ZMod 2) qR :=
    Submodule.finrank_map_subtype_eq R qR
  have hC3 : 3 ≤ Module.finrank (ZMod 2) C := by
    rw [hCdim, hqRdim]
    omega
  obtain ⟨u₂, hu₂C, hu₂0, hu₂Q⟩ := exists_singular_in_submodule (W := C) hC3
  have hu₂R : u₂ ∈ R := Submodule.map_subtype_le R qR hu₂C
  have hu₂q : (⟨u₂, hu₂R⟩ : R) ∈ qR := by
    obtain ⟨q, hq, hqval⟩ := Submodule.mem_map.mp hu₂C
    have hqeq : q = ⟨u₂, hu₂R⟩ := Subtype.ext hqval
    rwa [hqeq] at hq
  refine ⟨u₂, hu₂R, hu₂Q, hu₂0, ?_⟩
  intro h
  have hmemp : (⟨u₁, hu₁R⟩ : R) ∈ pR := Submodule.mem_span_singleton_self _
  have hmemq : (⟨u₁, hu₁R⟩ : R) ∈ qR := by
    have hsub : (⟨u₂, hu₂R⟩ : R) = ⟨u₁, hu₁R⟩ := Subtype.ext h
    rwa [hsub] at hu₂q
  have hzero : (⟨u₁, hu₁R⟩ : R) = 0 :=
    (Submodule.disjoint_def.mp hcompl.disjoint) _ hmemp hmemq
  exact hu₁0 (congrArg Subtype.val hzero)

theorem exists_singular_pair_perp (hQ : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ Module.finrank (ZMod 2) V) {b : V} (hb : Q b = 1) :
    ∃ u₁ u₂ : V, u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₁ ≠ u₂ ∧ Q u₁ = 0 ∧ Q u₂ = 0 ∧ polar Q u₁ u₂ = 0 ∧
      polar Q u₁ b = 0 ∧ polar Q u₂ b = 0 := by
  have hb0 : b ≠ 0 := fun h0 => by rw [h0, map_zero] at hb; exact zero_ne_one hb
  let P : Submodule (ZMod 2) V :=
    LinearMap.BilinForm.orthogonal (polarBilin Q) ((ZMod 2) ∙ b)
  have hbP : b ∈ P := mem_orth_span_single_iff.mpr (by
    rw [polar_self_eq_two_mul, hb, mul_one]
    exact CharTwo.two_eq_zero)
  have hPdim : Module.finrank (ZMod 2) P = Module.finrank (ZMod 2) V - 1 := by
    dsimp only [P]
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton hb0]
  have hP3 : 3 ≤ Module.finrank (ZMod 2) P := by rw [hPdim]; omega
  obtain ⟨u₁, hu₁P, hu₁0, hu₁Q⟩ := exists_singular_in_submodule (W := P) hP3
  have hu₁b : u₁ ≠ b := by
    intro h
    rw [h, hb] at hu₁Q
    exact zero_ne_one hu₁Q.symm
  have hspan2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({u₁, b} : Set V)) = 2 :=
    finrank_span_pair_eq_two_of_singular_nonsingular hu₁Q hb hu₁0 hu₁b
  let R : Submodule (ZMod 2) V :=
    LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span (ZMod 2) ({u₁, b} : Set V))
  have hu₁R : u₁ ∈ R := by
    dsimp only [R]
    rw [mem_orth_span_pair_iff]
    exact ⟨polar_self_eq_zero hu₁Q, mem_orth_span_single_iff.mp hu₁P⟩
  have hRdim : Module.finrank (ZMod 2) R = Module.finrank (ZMod 2) V - 2 := by
    dsimp only [R]
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, hspan2]
  have hR4 : 4 ≤ Module.finrank (ZMod 2) R := by rw [hRdim]; omega
  obtain ⟨u₂, hu₂R, hu₂Q, hu₂0, hu₂_ne_u₁⟩ :=
    exists_singular_ne_of_finrank_four hu₁R hu₁Q hu₁0 hR4
  have hu₂pair := mem_orth_span_pair_iff.mp hu₂R
  refine ⟨u₁, u₂, hu₁0, hu₂0, fun h => hu₂_ne_u₁ h.symm, hu₁Q, hu₂Q, hu₂pair.1,
    ?_, ?_⟩
  · rw [polar_comm]
    exact mem_orth_span_single_iff.mp hu₁P
  · rw [polar_comm]
    exact hu₂pair.2

private theorem exists_singular_polar_ne_zero_of_not_mem (hQ : (polarBilin Q).Nondegenerate)
    {b x : V} (hb : Q b = 1)
    (hxP : x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((ZMod 2) ∙ b))
    (hxL : x ∉ (ZMod 2) ∙ b) :
    ∃ u, u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((ZMod 2) ∙ b) ∧ Q u = 0 ∧
      polar Q x u ≠ 0 := by
  obtain ⟨z, hzP, hxz⟩ := exists_polar_ne_zero_of_not_mem hQ hxL
  by_cases hzQ : Q z = 0
  · exact ⟨z, hzP, hzQ, hxz⟩
  have hzQ1 : Q z = 1 := zmod2_eq_one_of_ne_zero hzQ
  have hbP : b ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((ZMod 2) ∙ b) :=
    mem_orth_span_single_iff.mpr (by
      rw [polar_self_eq_two_mul, hb, mul_one]
      exact CharTwo.two_eq_zero)
  have hxb0 : polar Q x b = 0 := by
    rw [polar_comm]
    exact mem_orth_span_single_iff.mp hxP
  have hbz : polar Q b z = 0 := mem_orth_span_single_iff.mp hzP
  have hzb : polar Q z b = 0 := by rwa [polar_comm] at hbz
  refine ⟨z + b, Submodule.add_mem _ hzP hbP, ?_, ?_⟩
  · rw [QuadraticMap.map_add Q, hzQ1, hb, hzb]
    decide
  · rw [polar_add_right, hxb0, add_zero]
    exact hxz

private theorem eichler_add_smul_mem_of_invariant {b x u w : V} {X : Submodule (ZMod 2) V}
    (hb : Q b = 1) (hinv : ∀ g ∈ elementaryGroup Q, g b = b → ∀ y ∈ X, g y ∈ X)
    (hxX : x ∈ X) (hxP : x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((ZMod 2) ∙ b))
    (huP : u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((ZMod 2) ∙ b))
    (huQ : Q u = 0) (hxu : polar Q x u = 1)
    (hw : w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q)
      (Submodule.span (ZMod 2) ({u, b} : Set V))) :
    w + (polar Q x w + Q w) • u ∈ X := by
  have huw : polar Q u w = 0 := (mem_orth_span_pair_iff.mp hw).1
  have hbw : polar Q b w = 0 := (mem_orth_span_pair_iff.mp hw).2
  have hbu : polar Q b u = 0 := mem_orth_span_single_iff.mp huP
  have hgb : eichler Q u w b = b := eichler_apply_of_polar_eq_zero hbu hbw
  have hmem := hinv (eichler Q u w) (eichler_mem_elementaryGroup Q u w) hgb x hxX
  have hsub := X.sub_mem hmem hxX
  have hformula : eichler Q u w x - x = w + (polar Q x w + Q w) • u := by
    rw [eichler_apply huQ huw, hxu, one_smul, mul_one, vec_sub, vec_sub]
    calc x + w + (polar Q x w + Q w) • u + x
        = w + (polar Q x w + Q w) • u + (x + x) := by abel
      _ = w + (polar Q x w + Q w) • u := by rw [vec_add_self, add_zero]
  rwa [hformula] at hsub

private theorem mem_of_three_eichler_displacements {x u w₁ w₂ : V} {X : Submodule (ZMod 2) V}
    (h1X : w₁ + (polar Q x w₁ + Q w₁) • u ∈ X)
    (h2X : w₂ + (polar Q x w₂ + Q w₂) • u ∈ X)
    (h12X : w₁ + w₂ + (polar Q x (w₁ + w₂) + Q (w₁ + w₂)) • u ∈ X)
    (h12one : polar Q w₁ w₂ = 1) : u ∈ X := by
  have hdiff := X.sub_mem (X.add_mem h1X h2X) h12X
  have hcoeff : (polar Q x w₁ + Q w₁) + (polar Q x w₂ + Q w₂) -
      (polar Q x (w₁ + w₂) + Q (w₁ + w₂)) = 1 := by
    rw [QuadraticMap.polar_add_right, QuadraticMap.map_add Q, h12one]
    ring
    decide
  have hEq : (w₁ + (polar Q x w₁ + Q w₁) • u) +
      (w₂ + (polar Q x w₂ + Q w₂) • u) -
      (w₁ + w₂ + (polar Q x (w₁ + w₂) + Q (w₁ + w₂)) • u) =
      ((polar Q x w₁ + Q w₁) + (polar Q x w₂ + Q w₂) -
        (polar Q x (w₁ + w₂) + Q (w₁ + w₂))) • u := by
    module
  rw [hEq, hcoeff, one_smul] at hdiff
  exact hdiff

theorem eq_span_or_eq_orth_of_map_eq_one (hQ : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ Module.finrank (ZMod 2) V) {b : V} (hb : Q b = 1) (X : Submodule (ZMod 2) V)
    (hbX : (ZMod 2) ∙ b ≤ X)
    (hXb : X ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) ((ZMod 2) ∙ b))
    (hinv : ∀ g ∈ elementaryGroup Q, g b = b → ∀ x ∈ X, g x ∈ X) :
    X = (ZMod 2) ∙ b ∨ X = LinearMap.BilinForm.orthogonal (polarBilin Q) ((ZMod 2) ∙ b) := by
  by_cases hX : X = (ZMod 2) ∙ b
  · exact Or.inl hX
  refine Or.inr (le_antisymm hXb ?_)
  obtain ⟨x, hxX, hxL⟩ : ∃ x ∈ X, x ∉ (ZMod 2) ∙ b := by
    by_contra hcon
    push Not at hcon
    exact hX (le_antisymm hcon hbX)
  have hxP : x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((ZMod 2) ∙ b) := hXb hxX
  obtain ⟨u, huP, huQ, hxu⟩ :=
    exists_singular_polar_ne_zero_of_not_mem hQ hb hxP hxL
  have hxu1 : polar Q x u = 1 := zmod2_eq_one_of_ne_zero hxu
  let R : Submodule (ZMod 2) V :=
    LinearMap.BilinForm.orthogonal (polarBilin Q)
      (Submodule.span (ZMod 2) ({u, b} : Set V))
  obtain ⟨w₁, hw₁, w₂, hw₂, h12⟩ :=
    exists_polar_ne_zero_of_finrank hQ (finrank_span_pair_le u b) (by omega)
  have h12one : polar Q w₁ w₂ = 1 := zmod2_eq_one_of_ne_zero h12
  have h1X : w₁ + (polar Q x w₁ + Q w₁) • u ∈ X :=
    eichler_add_smul_mem_of_invariant hb hinv hxX hxP huP huQ hxu1 hw₁
  have h2X : w₂ + (polar Q x w₂ + Q w₂) • u ∈ X :=
    eichler_add_smul_mem_of_invariant hb hinv hxX hxP huP huQ hxu1 hw₂
  have h12X : w₁ + w₂ + (polar Q x (w₁ + w₂) + Q (w₁ + w₂)) • u ∈ X :=
    eichler_add_smul_mem_of_invariant hb hinv hxX hxP huP huQ hxu1
      (Submodule.add_mem _ hw₁ hw₂)
  have huX : u ∈ X :=
    mem_of_three_eichler_displacements h1X h2X h12X h12one
  have hRleX : R ≤ X := by
    intro w hw
    have hwX : w + (polar Q x w + Q w) • u ∈ X :=
      eichler_add_smul_mem_of_invariant hb hinv hxX hxP huP huQ hxu1 hw
    have h := X.sub_mem hwX (X.smul_mem (polar Q x w + Q w) huX)
    convert h using 1
    abel
  intro z hzP
  let c : ZMod 2 := polar Q z u
  have hzR : z - c • x ∈ R := by
    dsimp only [R]
    rw [mem_orth_span_pair_iff]
    constructor
    · rw [polar_sub_right, polar_smul_right_eq, polar_comm Q u x, hxu1]
      dsimp only [c]
      rw [polar_comm Q u z]
      ring
    · have hbz : polar Q b z = 0 := mem_orth_span_single_iff.mp hzP
      have hbx : polar Q b x = 0 := mem_orth_span_single_iff.mp hxP
      rw [polar_sub_right, polar_smul_right_eq, hbz, hbx]
      ring
  have hzX : z - c • x ∈ X := hRleX hzR
  have h := X.add_mem hzX (X.smul_mem c hxX)
  convert h using 1
  abel

private theorem rootAction_commonCenter (hQ : (polarBilin Q).Nondegenerate) {a : V}
    (ha : Q a = 0) (ha0 : a ≠ 0) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hE : ∀ g ∈ E, IsRootElt Q a g) :
    CommonTransvectionCenter (rootAction E hE)
      (⟨a, rootPerp_self (Q := Q) ha⟩ : rootPerp (Q := Q) a) := by
  constructor
  · intro h0
    exact ha0 (congrArg Subtype.val h0)
  · intro g hg1
    have hgroot := hE g g.2
    have hg1' : g.1 ≠ 1 := fun h => hg1 (Subtype.ext h)
    obtain ⟨z, hzpa, hgz⟩ := IsRootElt.exists_sub_eq hQ ha hgroot hg1'
    have hzP : z ∈ rootPerp (Q := Q) a :=
      mem_orth_span_single_iff.mpr (by rwa [polar_comm] at hzpa)
    have hdisp : rootAction E hE g ⟨z, hzP⟩ - ⟨z, hzP⟩ =
        (⟨a, rootPerp_self (Q := Q) ha⟩ : rootPerp (Q := Q) a) := by
      ext
      change g.1 z - z = a
      exact hgz
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      have hzroot : polar Q a z.1 = 0 :=
        mem_orth_span_single_iff.mp (by simpa [rootPerp] using z.2)
      have hzroot2 : polar Q z.1 a = 0 := by rwa [polar_comm] at hzroot
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hgroot.2.2 z.1 hzroot2)
      have hc' : rootAction E hE g z - z =
          c • (⟨a, rootPerp_self (Q := Q) ha⟩ : rootPerp (Q := Q) a) := by
        ext
        change g.1 z.1 - z.1 = c • a
        exact hc.symm
      change rootAction E hE g z - z ∈
        (ZMod 2) ∙ (⟨a, rootPerp_self (Q := Q) ha⟩ : rootPerp (Q := Q) a)
      rw [hc']
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨⟨z, hzP⟩, hdisp⟩

private theorem rootAction_elementary (hQ : (polarBilin Q).Nondegenerate) {a : V}
    (ha : Q a = 0) (ha0 : a ≠ 0) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hE : ∀ g ∈ E, IsRootElt Q a g) : IsElementaryAbelian2 E := by
  have hroot : ∀ g : E, g.1 ∈ rootGroup Q a := fun g =>
    (mem_rootGroup_iff hQ ha ha0).mpr
      ⟨(hE g g.2).1, (hE g g.2).2.1,
        fun x hx =>
          let ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((hE g g.2).2.2 x hx)
          ⟨c, hc.symm⟩⟩
  constructor
  · intro g h
    exact Subtype.ext (rootGroup_commute (hroot g) (hroot h))
  · intro g
    exact Subtype.ext (by
      simpa [pow_two] using
        sq_eq_one_of_mem_rootGroup (by decide : (2 : ZMod 2) = 0) (hroot g))

private theorem rootAction_exists_card_eq (hQ : (polarBilin Q).Nondegenerate) {a : V}
    (ha : Q a = 0) (ha0 : a ≠ 0) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hE : ∀ g ∈ E, IsRootElt Q a g) :
    ∃ r : ℕ, Nat.card E = 2 ^ r ∧ IsElementaryAbelian2 E := by
  classical
  have helem := rootAction_elementary hQ ha ha0 hE
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Finite (V → V) := inferInstance
  haveI : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective
  haveI : Finite E := Subtype.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2group : IsPGroup 2 E := by
    rw [isPGroup_iff_exists_pow_pow_eq_one]
    exact ⟨1, fun g => by simpa using helem.2 g⟩
  obtain ⟨r, hcardE⟩ := h2group.exists_card_eq
  exact ⟨r, hcardE, helem⟩

private theorem rootAction_fixed_mem_rootPerp (hQ : (polarBilin Q).Nondegenerate) {a v : V}
    (ha : Q a = 0) (ha0 : a ≠ 0) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hE : ∀ g ∈ E, IsRootElt Q a g) (hE1 : E ≠ ⊥)
    (hv : ∀ g ∈ E, g v = v) : v ∈ rootPerp (Q := Q) a := by
  by_contra hvp
  have hne : polar Q v a ≠ 0 := by
    intro h0
    exact hvp (mem_orth_span_single_iff.mpr (by rwa [polar_comm] at h0))
  obtain ⟨g, hgne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
  have hg1 : g.1 ≠ 1 := fun h => hgne (Subtype.ext h)
  exact hg1 (IsRootElt.eq_one_of_apply_eq hQ ha (hE g g.2) hne (hv g g.2))

private theorem rootAction_card_fixed (hQ : (polarBilin Q).Nondegenerate) {a : V}
    (ha : Q a = 0) (ha0 : a ≠ 0) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hE : ∀ g ∈ E, IsRootElt Q a g) (hE1 : E ≠ ⊥) :
    Nat.card {v : V // ∀ g ∈ E, g v = v} =
      Nat.card (fixedSpace (rootAction E hE) Set.univ) := by
  have hfixP : ∀ v : V, (∀ g ∈ E, g v = v) → v ∈ rootPerp (Q := Q) a :=
    fun v hv => rootAction_fixed_mem_rootPerp hQ ha ha0 hE hE1 hv
  refine Nat.card_congr ?_
  refine
    { toFun := fun v =>
        ⟨⟨v.1, hfixP v.1 v.2⟩, by
          intro g _
          apply Subtype.ext
          change (rootAction E hE g ⟨v.1, hfixP v.1 v.2⟩ : V) = v.1
          rw [rootAction_apply]
          exact v.2 g g.2⟩
      invFun := fun z =>
        ⟨z.1.1, by
          intro g hg
          have hz := z.2 ⟨g, hg⟩ (Set.mem_univ _)
          have h := congrArg (fun w : rootPerp (Q := Q) a => (w : V)) hz
          change (rootAction E hE ⟨g, hg⟩ z.1 : V) = (z.1 : V) at h
          rwa [rootAction_apply] at h⟩
      left_inv := by intro v; ext; rfl
      right_inv := by intro z; ext; rfl }

private theorem two_pow_mul_two_pow_mul_two (d r : ℕ) (hd : 0 < d) (hr : r ≤ d - 1) :
    2 ^ r * 2 ^ (d - 1 - r) * 2 = 2 ^ d := by
  rw [← pow_add, Nat.add_sub_of_le hr, ← pow_succ]
  congr 1
  omega

theorem card_mul_card_fixed_le (hQ : (polarBilin Q).Nondegenerate) {a : V} (ha : Q a = 0)
    (ha0 : a ≠ 0) (E : Subgroup (V ≃ₗ[ZMod 2] V)) (hE : ∀ g ∈ E, IsRootElt Q a g)
    (hE1 : E ≠ ⊥) :
    Nat.card E * Nat.card {v : V // ∀ g ∈ E, g v = v} * 2 ≤ Nat.card V := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  have haP : a ∈ rootPerp (Q := Q) a := rootPerp_self (Q := Q) ha
  have hPdim : Module.finrank (ZMod 2) (rootPerp (Q := Q) a) =
      Module.finrank (ZMod 2) V - 1 := by
    dsimp only [rootPerp]
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton ha0]
  obtain ⟨r, hcardE, helem⟩ := rootAction_exists_card_eq hQ ha ha0 hE
  haveI : Module.Finite (ZMod 2) (rootPerp (Q := Q) a) := Module.Finite.of_finite
  have hcenter := rootAction_commonCenter hQ ha ha0 hE
  have hdim := finrank_fixedSpace_univ_of_commonTransvectionCenter
    (action := rootAction E hE) (center := (⟨a, haP⟩ : rootPerp (Q := Q) a))
    r hcardE helem hcenter
  have hcardV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcardFix := rootAction_card_fixed hQ ha ha0 hE hE1
  have hcardCP : Nat.card (fixedSpace (rootAction E hE) Set.univ) =
      2 ^ (Module.finrank (ZMod 2) (rootPerp (Q := Q) a) - r) := by
    haveI : Module.Finite (ZMod 2) (fixedSpace (rootAction E hE) Set.univ) :=
      Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim.2]
  have hfinVpos : 0 < Module.finrank (ZMod 2) V := by
    have hle := Submodule.finrank_mono
      (le_top : Submodule.span (ZMod 2) {a} ≤ (⊤ : Submodule (ZMod 2) V))
    rw [finrank_top, finrank_span_singleton ha0] at hle
    omega
  have hrle : r ≤ Module.finrank (ZMod 2) V - 1 := by
    have h := hdim.1
    rw [hPdim] at h
    exact h
  rw [hcardE, hcardFix, hcardCP, hcardV, hPdim]
  exact le_of_eq (two_pow_mul_two_pow_mul_two _ _ hfinVpos hrle)

end CFSG.CGT.Harada80
