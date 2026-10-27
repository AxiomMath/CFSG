module

public import CFSG.Fischer.Classification.Orthogonal2.SpModel
public import CFSG.LargeExtraspecial.OrthoF2SpRadical

import CFSG.LargeExtraspecial.S4Basic
public import CFSG.LargeExtraspecial.S2Three
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public section

namespace CFSG.Fischer.Classification.Orth2

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Module CFSG.LargeExtraspecial
open scoped commutatorElement

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}

theorem smul_add_smul_self (c : ZMod 2) (v : U) : c • v + c • v = 0 := by
  rw [← add_smul, OrthoF2.zmod2_add_self, zero_smul]

theorem isometry_apply (g : TauCeti.BilinForm.isometryGroup f) (x y : U) :
    f ((g : U ≃ₗ[ZMod 2] U) x) ((g : U ≃ₗ[ZMod 2] U) y) = f x y :=
  TauCeti.BilinForm.mem_isometryGroup_iff.mp g.2 x y

noncomputable abbrev spRadical (f : LinearMap.BilinForm (ZMod 2) U) (u : U) :
    Subgroup (TauCeti.BilinForm.isometryGroup f) :=
  (spPointRadical f u).subgroupOf (TauCeti.BilinForm.isometryGroup f)

theorem mem_spRadical_iff (hf : f.IsAlt) {u : U} {g : TauCeti.BilinForm.isometryGroup f} :
    g ∈ spRadical f u ↔ (g : U ≃ₗ[ZMod 2] U) u = u ∧
      ∀ x, f x u = 0 → (g : U ≃ₗ[ZMod 2] U) x = x ∨ (g : U ≃ₗ[ZMod 2] U) x = x + u := by
  rw [Subgroup.mem_subgroupOf, mem_spPointRadical]
  constructor
  · rintro ⟨-, hgu, h1, -⟩
    refine ⟨hgu, fun x hx => ?_⟩
    have hx' : f u x = 0 := by rw [OrthoF2.isAlt_symm hf]; exact hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h1 x hx')
    rcases OrthoF2.zmod2_eq_zero_or_eq_one c with rfl | rfl
    · left
      rw [zero_smul] at hc
      exact (sub_eq_zero.mp hc.symm)
    · right
      rw [one_smul] at hc
      rw [← sub_eq_iff_eq_add', ← hc]
  · rintro ⟨hgu, h1⟩
    refine ⟨g.2, hgu, fun x hx => ?_, fun v => ?_⟩
    · have hx' : f x u = 0 := by rw [OrthoF2.isAlt_symm hf]; exact hx
      rcases h1 x hx' with h | h
      · rw [h, sub_self]; exact zero_mem _
      · rw [h, add_sub_cancel_left]; exact Submodule.mem_span_singleton_self u
    · rw [map_sub, ← hgu, isometry_apply, hgu, sub_self]

theorem spT_mem_spRadical (hf : f.IsAlt) (u : U) : spT hf u ∈ spRadical f u :=
  spTransvection_mem_spPointRadical hf u

theorem spRadical_ext (hf : f.IsAlt) {u a' : U} (ha' : f a' u = 1)
    {g h : TauCeti.BilinForm.isometryGroup f} (hg : g ∈ spRadical f u) (hh : h ∈ spRadical f u)
    (hgh : (g : U ≃ₗ[ZMod 2] U) a' = (h : U ≃ₗ[ZMod 2] U) a') : g = h := by
  have hua : f u a' = 1 := by rw [OrthoF2.isAlt_symm hf]; exact ha'
  exact Subtype.ext (spPointRadical_ext hua hg hh hgh)

theorem apply_eq_of_commute_spT (hf : f.IsAlt) (hnd : f.Nondegenerate) {u : U} (hu : u ≠ 0)
    {g : TauCeti.BilinForm.isometryGroup f} (hg : g * spT hf u = spT hf u * g) :
    (g : U ≃ₗ[ZMod 2] U) u = u := by
  have h1 : g * spT hf u * g⁻¹ = spT hf u := by rw [hg, mul_inv_cancel_right]
  rw [spT_conj] at h1
  exact eq_of_spT_eq hf hnd (fun h0 => hu ((LinearEquiv.map_eq_zero_iff _).mp h0)) h1

theorem conj_mem_spRadical (hf : f.IsAlt) {u : U} {g k : TauCeti.BilinForm.isometryGroup f}
    (hg : (g : U ≃ₗ[ZMod 2] U) u = u) (hk : k ∈ spRadical f u) :
    g * k * g⁻¹ ∈ spRadical f u := by
  rw [mem_spRadical_iff hf] at hk ⊢
  obtain ⟨hku, hk1⟩ := hk
  have hgi : (g⁻¹ : TauCeti.BilinForm.isometryGroup f) = ⟨(g : U ≃ₗ[ZMod 2] U)⁻¹, inv_mem g.2⟩ :=
    rfl
  have hginv : ∀ x, (g : U ≃ₗ[ZMod 2] U) (((g⁻¹ : TauCeti.BilinForm.isometryGroup f) :
      U ≃ₗ[ZMod 2] U) x) = x := fun x => OrthoF2.apply_inv_apply _ x
  have hgu' : ((g⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) u = u := by
    conv_lhs => rw [← hg]
    exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' _ u
  refine ⟨?_, fun x hx => ?_⟩
  · change (g : U ≃ₗ[ZMod 2] U) ((k : U ≃ₗ[ZMod 2] U)
      (((g⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) u)) = u
    rw [hgu', hku, hg]
  · have hx' : f (((g⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) x) u = 0 := by
      rw [← hgu', isometry_apply]; exact hx
    change (g : U ≃ₗ[ZMod 2] U) ((k : U ≃ₗ[ZMod 2] U)
      (((g⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) x)) = x ∨
      (g : U ≃ₗ[ZMod 2] U) ((k : U ≃ₗ[ZMod 2] U)
      (((g⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) x)) = x + u
    rcases hk1 _ hx' with h | h
    · left; rw [h, hginv]
    · right; rw [h, map_add, hginv, hg]

theorem spT_mul_apply (hf : f.IsAlt) (a b x : U) :
    ((spT hf a * spT hf b : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) x =
      ((spT hf a : _) : U ≃ₗ[ZMod 2] U) (((spT hf b : _) : U ≃ₗ[ZMod 2] U) x) :=
  rfl

theorem spSiegel_apply (hf : f.IsAlt) {u y : U} (hy : f y u = 0) (x : U) :
    ((spT hf y * spT hf (y + u) : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) x =
      x + f x u • y + (f x y + f x u) • u := by
  have huy : f u y = 0 := by rw [OrthoF2.isAlt_symm hf]; exact hy
  rw [spT_mul_apply, spT_apply, spT_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hf.self_eq_zero, huy, mul_zero, add_zero]
  rw [smul_add, add_smul (f x y) (f x u) y]
  have h1 := smul_add_smul_self (f x y) y
  calc x + (f x y • y + f x u • y + (f x y + f x u) • u) + f x y • y
      = x + f x u • y + (f x y + f x u) • u + (f x y • y + f x y • y) := by abel
    _ = x + f x u • y + (f x y + f x u) • u := by rw [h1, add_zero]

theorem spSiegel_apply_self (hf : f.IsAlt) {u y : U} (hy : f y u = 0) :
    ((spT hf y * spT hf (y + u) : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) u = u := by
  have huy : f u y = 0 := by rw [OrthoF2.isAlt_symm hf]; exact hy
  rw [spSiegel_apply hf hy, hf.self_eq_zero, huy, zero_smul, add_zero, zero_add, zero_smul,
    add_zero]

theorem spSiegel_mem_spRadical (hf : f.IsAlt) {u y : U} (hy : f y u = 0) :
    spT hf y * spT hf (y + u) ∈ spRadical f u := by
  rw [mem_spRadical_iff hf]
  refine ⟨spSiegel_apply_self hf hy, fun x hx => ?_⟩
  rw [spSiegel_apply hf hy, hx, zero_smul, add_zero, add_zero]
  rcases OrthoF2.zmod2_eq_zero_or_eq_one (f x y) with h | h
  · left; rw [h, zero_smul, add_zero]
  · right; rw [h, one_smul]

theorem spSiegel_mul_spSiegel (hf : f.IsAlt) {u y z : U} (hy : f y u = 0) (hz : f z u = 0)
    (hyz : f y z = 0) :
    (spT hf y * spT hf (y + u)) * (spT hf z * spT hf (z + u)) =
      (spT hf (y + z) * spT hf (y + z + u)) * spT hf u := by
  have huy : f u y = 0 := by rw [OrthoF2.isAlt_symm hf]; exact hy
  have huz : f u z = 0 := by rw [OrthoF2.isAlt_symm hf]; exact hz
  have hzy : f z y = 0 := by rw [OrthoF2.isAlt_symm hf]; exact hyz
  have hyzu : f (y + z) u = 0 := by rw [map_add, LinearMap.add_apply, hy, hz, add_zero]
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change ((spT hf y * spT hf (y + u) : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U)
      (((spT hf z * spT hf (z + u) : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) x) =
    ((spT hf (y + z) * spT hf (y + z + u) : TauCeti.BilinForm.isometryGroup f) :
      U ≃ₗ[ZMod 2] U) (((spT hf u : _) : U ≃ₗ[ZMod 2] U) x)
  rw [spSiegel_apply hf hz, spSiegel_apply hf hy, spSiegel_apply hf hyzu, spT_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hf.self_eq_zero, huy, huz, hzy, hz, mul_zero, add_zero]
  module

noncomputable def spOmega (hf : f.IsAlt) (u : U) : Subgroup (TauCeti.BilinForm.isometryGroup f) :=
  Subgroup.closure {g | ∃ v w, f v u = 0 ∧ f w u = 0 ∧ v ≠ 0 ∧ v ≠ u ∧ w ≠ 0 ∧ w ≠ u ∧
    g = spT hf v * spT hf w}

theorem spT_mul_spT_mem_spOmega (hf : f.IsAlt) {u v w : U} (hv : f v u = 0) (hw : f w u = 0)
    (hv0 : v ≠ 0) (hvu : v ≠ u) (hw0 : w ≠ 0) (hwu : w ≠ u) :
    spT hf v * spT hf w ∈ spOmega hf u :=
  Subgroup.subset_closure ⟨v, w, hv, hw, hv0, hvu, hw0, hwu, rfl⟩

theorem spSiegel_mem_spOmega (hf : f.IsAlt) {u y : U} (hy : f y u = 0) (hy0 : y ≠ 0)
    (hyu : y ≠ u) : spT hf y * spT hf (y + u) ∈ spOmega hf u := by
  refine spT_mul_spT_mem_spOmega hf hy ?_ hy0 hyu ?_ ?_
  · rw [map_add, LinearMap.add_apply, hy, hf.self_eq_zero, add_zero]
  · intro h
    apply hyu
    have := congrArg (· + u) h
    simpa [add_assoc, OrthoF2.vec_add_self] using this
  · intro h
    apply hy0
    have := congrArg (· + u) h
    simpa [add_assoc, OrthoF2.vec_add_self] using this

section Exists

variable [FiniteDimensional (ZMod 2) U]

theorem finrank_ker_pi_ge {k : ℕ} (v : Fin k → U) :
    finrank (ZMod 2) U - k ≤
      finrank (ZMod 2) (LinearMap.ker (LinearMap.pi fun i => f.flip (v i))) := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun i => f.flip (v i))
  have h2 : finrank (ZMod 2) (LinearMap.range (LinearMap.pi fun i => f.flip (v i))) ≤ k := by
    calc _ ≤ finrank (ZMod 2) (Fin k → ZMod 2) := Submodule.finrank_le _
      _ = k := by simp
  omega

omit [FiniteDimensional (ZMod 2) U] in
theorem mem_ker_pi_iff {k : ℕ} {v : Fin k → U} {x : U} :
    x ∈ LinearMap.ker (LinearMap.pi fun i => f.flip (v i)) ↔ ∀ i, f x (v i) = 0 := by
  rw [LinearMap.mem_ker, funext_iff]
  rfl

omit [FiniteDimensional (ZMod 2) U] in
theorem exists_mem_ne_zero_ne {P : Submodule (ZMod 2) U} (hP : 2 ≤ finrank (ZMod 2) P) (u : U) :
    ∃ x ∈ P, x ≠ 0 ∧ x ≠ u := by
  by_contra h
  push Not at h
  have hle : P ≤ Submodule.span (ZMod 2) {u} := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    · rw [h x hx hx0]; exact Submodule.mem_span_singleton_self u
  have h1 := Submodule.finrank_mono hle
  have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({u} : Set U)) ≤ 1 :=
    (finrank_span_le_card ({u} : Set U)).trans (by simp)
  omega

theorem exists_mem_not_mem_span_pair {P : Submodule (ZMod 2) U} (hP : 3 ≤ finrank (ZMod 2) P)
    (u y : U) : ∃ x ∈ P, x ∉ Submodule.span (ZMod 2) {u, y} := by
  by_contra h
  push Not at h
  have hle : P ≤ Submodule.span (ZMod 2) {u, y} := fun x hx => h x hx
  have h1 := Submodule.finrank_mono hle
  have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({u, y} : Set U)) ≤ 2 := by
    rw [Submodule.span_insert]
    refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
    have hu : finrank (ZMod 2) (Submodule.span (ZMod 2) ({u} : Set U)) ≤ 1 :=
      (finrank_span_le_card ({u} : Set U)).trans (by simp)
    have hy : finrank (ZMod 2) (Submodule.span (ZMod 2) ({y} : Set U)) ≤ 1 :=
      (finrank_span_le_card ({y} : Set U)).trans (by simp)
    omega
  omega

theorem exists_perp_three (hn : 5 ≤ finrank (ZMod 2) U) (u v w : U) :
    ∃ x, f x u = 0 ∧ f x v = 0 ∧ f x w = 0 ∧ x ≠ 0 ∧ x ≠ u := by
  have h := finrank_ker_pi_ge (f := f) ![u, v, w]
  obtain ⟨x, hx, hx0, hxu⟩ := exists_mem_ne_zero_ne (P := LinearMap.ker
    (LinearMap.pi fun i => f.flip (![u, v, w] i))) (by omega) u
  rw [mem_ker_pi_iff] at hx
  exact ⟨x, hx 0, hx 1, hx 2, hx0, hxu⟩

theorem exists_perp_two_not_mem_span (hn : 5 ≤ finrank (ZMod 2) U) (u y : U) :
    ∃ z, f z u = 0 ∧ f z y = 0 ∧ z ∉ Submodule.span (ZMod 2) {u, y} := by
  have h := finrank_ker_pi_ge (f := f) ![u, y]
  obtain ⟨z, hz, hzs⟩ := exists_mem_not_mem_span_pair (P := LinearMap.ker
    (LinearMap.pi fun i => f.flip (![u, y] i))) (by omega) u y
  rw [mem_ker_pi_iff] at hz
  exact ⟨z, hz 0, hz 1, hzs⟩

omit [FiniteDimensional (ZMod 2) U] in
theorem exists_apply_zero_zero_one (hf : f.IsAlt) (hnd : f.Nondegenerate) {u v w : U}
    (hw : w ∉ Submodule.span (ZMod 2) {u, v}) : ∃ z, f z u = 0 ∧ f z v = 0 ∧ f z w = 1 := by
  by_contra hall
  push Not at hall
  have hker : (⨅ i, LinearMap.ker (![f u, f v] i)) ≤ LinearMap.ker (f w) := by
    intro x hx
    rw [Submodule.mem_iInf] at hx
    rw [LinearMap.mem_ker]
    have h0 : f u x = 0 := hx 0
    have h1 : f v x = 0 := hx 1
    rcases OrthoF2.zmod2_eq_zero_or_eq_one (f w x) with h | h
    · exact h
    · exfalso
      apply hall x
      · rw [OrthoF2.isAlt_symm hf]; exact h0
      · rw [OrthoF2.isAlt_symm hf]; exact h1
      · rw [OrthoF2.isAlt_symm hf]; exact h
  have hmem := mem_span_of_iInf_ker_le_ker hker
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Submodule.mem_span_pair] at hmem
  obtain ⟨c, d, hcd⟩ := hmem
  apply hw
  have h0 : w - (c • u + d • v) = 0 := by
    apply hnd.1
    intro x
    rw [map_sub, LinearMap.sub_apply, map_add, map_smul, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.smul_apply, ← hcd]
    simp
  rw [sub_eq_zero] at h0
  rw [h0, Submodule.mem_span_pair]
  exact ⟨c, d, rfl⟩

theorem exists_apply_zero_one (hf : f.IsAlt) (hnd : f.Nondegenerate) {u v : U} (hv0 : v ≠ 0)
    (hvu : v ≠ u) : ∃ y, f y u = 0 ∧ f y v = 1 := by
  have hv : v ∉ Submodule.span (ZMod 2) {u} := fun hmem => by
    rcases eq_zero_or_eq_of_mem_span_singleton hmem with h | h
    · exact hv0 h
    · exact hvu h
  have : Finite U := Module.finite_of_finite (ZMod 2)
  obtain ⟨y, hy0, hy1⟩ := exists_apply_eq_zero_eq_one hnd hv
  exact ⟨y, by rw [OrthoF2.isAlt_symm hf]; exact hy0, by rw [OrthoF2.isAlt_symm hf]; exact hy1⟩

theorem exists_apply_zero_one_one (hf : f.IsAlt) (hnd : f.Nondegenerate) {u v w : U}
    (hv0 : v ≠ 0) (hvu : v ≠ u) (hw0 : w ≠ 0) (hwu : w ≠ u) :
    ∃ y, f y u = 0 ∧ f y v = 1 ∧ f y w = 1 := by
  obtain ⟨y₁, hy₁u, hy₁v⟩ := exists_apply_zero_one hf hnd hv0 hvu
  rcases OrthoF2.zmod2_eq_zero_or_eq_one (f y₁ w) with h0 | h1
  · have hw : w ∉ Submodule.span (ZMod 2) {u, v} := by
      intro hmem
      obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hmem
      have hd : d = 0 := by
        have := congrArg (f y₁) hcd
        rw [map_add, map_smul, map_smul, hy₁u, hy₁v, h0, smul_zero, smul_eq_mul, mul_one,
          zero_add] at this
        exact this
      rw [hd, zero_smul, add_zero] at hcd
      rcases OrthoF2.zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul] at hcd; exact hw0 hcd.symm
      · rw [one_smul] at hcd; exact hwu hcd.symm
    obtain ⟨y₂, hy₂u, hy₂v, hy₂w⟩ := exists_apply_zero_zero_one hf hnd hw
    refine ⟨y₁ + y₂, ?_, ?_, ?_⟩
    · rw [map_add, LinearMap.add_apply, hy₁u, hy₂u, add_zero]
    · rw [map_add, LinearMap.add_apply, hy₁v, hy₂v, add_zero]
    · rw [map_add, LinearMap.add_apply, h0, hy₂w, zero_add]
  · exact ⟨y₁, hy₁u, hy₁v, h1⟩

end Exists

section Radical

variable [FiniteDimensional (ZMod 2) U]

omit [FiniteDimensional (ZMod 2) U] in
theorem exists_apply_eq_one_of_ne_zero (hnd : f.Nondegenerate) {u : U} (hu : u ≠ 0) :
    ∃ a', f a' u = 1 := by
  obtain ⟨a', ha'⟩ : ∃ a', f a' u ≠ 0 := by
    by_contra! h
    exact hu (hnd.2 u h)
  exact ⟨a', OrthoF2.zmod2_eq_one_of_ne_zero ha'⟩

theorem spT_mem_spOmega (hf : f.IsAlt) (hn : 5 ≤ finrank (ZMod 2) U) (u : U) :
    spT hf u ∈ spOmega hf u := by
  obtain ⟨y, hyu, -, -, hy0, hyu'⟩ := exists_perp_three (f := f) hn u u u
  obtain ⟨z, hzu, hzy, hzs⟩ := exists_perp_two_not_mem_span (f := f) hn u y
  have hyz : f y z = 0 := by rw [OrthoF2.isAlt_symm hf]; exact hzy
  have hz0 : z ≠ 0 := fun h => hzs (h ▸ zero_mem _)
  have hzu' : z ≠ u := fun h => hzs (h ▸ Submodule.subset_span (by simp))
  have hyz0 : y + z ≠ 0 := fun h => by
    apply hzs
    have : z = y := by
      have := congrArg (· + y) h
      simpa [add_comm y z, add_assoc, OrthoF2.vec_add_self] using this
    rw [this]
    exact Submodule.subset_span (by simp)
  have hyzu : y + z ≠ u := fun h => by
    apply hzs
    have : z = u + y := by
      have := congrArg (· + y) h
      simpa [add_comm y z, add_assoc, OrthoF2.vec_add_self] using this
    rw [this, Submodule.mem_span_pair]
    exact ⟨1, 1, by simp⟩
  have hyzp : f (y + z) u = 0 := by rw [map_add, LinearMap.add_apply, hyu, hzu, add_zero]
  have e := spSiegel_mul_spSiegel hf hyu hzu hyz
  have ht : spT hf u = (spT hf (y + z) * spT hf (y + z + u))⁻¹ *
      ((spT hf y * spT hf (y + u)) * (spT hf z * spT hf (z + u))) := by
    rw [e]; group
  rw [ht]
  exact mul_mem (inv_mem (spSiegel_mem_spOmega hf hyzp hyz0 hyzu))
    (mul_mem (spSiegel_mem_spOmega hf hyu hy0 hyu') (spSiegel_mem_spOmega hf hzu hz0 hzu'))

theorem exists_mem_spRadical_apply (hf : f.IsAlt) (hn : 5 ≤ finrank (ZMod 2) U) {u a' s : U}
    (ha' : f a' u = 1) (hs : f s u = 0) :
    ∃ h ∈ spRadical f u, h ∈ spOmega hf u ∧ (h : U ≃ₗ[ZMod 2] U) a' = a' + s := by
  by_cases hs0 : s = 0
  · exact ⟨1, one_mem _, one_mem _, by rw [hs0, add_zero]; rfl⟩
  by_cases hsu : s = u
  · refine ⟨spT hf u, spT_mem_spRadical hf u, spT_mem_spOmega hf hn u, ?_⟩
    rw [spT_apply, ha', one_smul, hsu]
  rcases OrthoF2.zmod2_eq_zero_or_eq_one (f a' s) with h0 | h1
  · refine ⟨(spT hf s * spT hf (s + u)) * spT hf u,
      mul_mem (spSiegel_mem_spRadical hf hs) (spT_mem_spRadical hf u),
      mul_mem (spSiegel_mem_spOmega hf hs hs0 hsu) (spT_mem_spOmega hf hn u), ?_⟩
    change ((spT hf s * spT hf (s + u) : TauCeti.BilinForm.isometryGroup f) :
      U ≃ₗ[ZMod 2] U) (((spT hf u : _) : U ≃ₗ[ZMod 2] U) a') = a' + s
    rw [spT_apply, ha', one_smul, map_add, spSiegel_apply hf hs, spSiegel_apply_self hf hs, ha',
      h0, one_smul, zero_add, one_smul, add_assoc, OrthoF2.vec_add_self, add_zero]
  · refine ⟨spT hf s * spT hf (s + u), spSiegel_mem_spRadical hf hs,
      spSiegel_mem_spOmega hf hs hs0 hsu, ?_⟩
    rw [spSiegel_apply hf hs, ha', h1, one_smul, OrthoF2.zmod2_add_self, zero_smul, add_zero]

omit [FiniteDimensional (ZMod 2) U] in
theorem apply_sub_perp_of_mem_spRadical (hf : f.IsAlt) {u : U}
    {g : TauCeti.BilinForm.isometryGroup f} (hg : g ∈ spRadical f u) (a' : U) :
    f ((g : U ≃ₗ[ZMod 2] U) a' - a') u = 0 := by
  rw [OrthoF2.isAlt_symm hf]
  exact (Subgroup.mem_subgroupOf.mp hg).2.2.2 a'

theorem spRadical_le_spOmega (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hn : 5 ≤ finrank (ZMod 2) U) {u : U} (hu : u ≠ 0) : spRadical f u ≤ spOmega hf u := by
  obtain ⟨a', ha'⟩ := exists_apply_eq_one_of_ne_zero hnd hu
  intro g hg
  obtain ⟨h, hK, hΩ, hh⟩ :=
    exists_mem_spRadical_apply hf hn ha' (apply_sub_perp_of_mem_spRadical hf hg a')
  have : g = h := spRadical_ext hf ha' hg hK (by rw [hh]; abel)
  rw [this]
  exact hΩ

theorem card_spRadical (hf : f.IsAlt) (hnd : f.Nondegenerate) {u : U} (hu : u ≠ 0) :
    Nat.card ↥(spRadical f u) = 2 ^ (finrank (ZMod 2) U - 1) := by
  have hle : spPointRadical f u ≤ TauCeti.BilinForm.isometryGroup f := fun t ht => ht.1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  exact card_spPointRadical hf hnd hu

end Radical

section Perfect

variable [FiniteDimensional (ZMod 2) U]

omit [FiniteDimensional (ZMod 2) U] in
theorem spT_mul_spT_pow_three (hf : f.IsAlt) {a b : U} (hab : f a b = 1) :
    (spT hf a * spT hf b) ^ 3 = 1 := by
  have hba : f b a = 1 := by rw [OrthoF2.isAlt_symm hf]; exact hab
  have e1 := spT_mul_spT_mul_spT hf hab
  have e2 := spT_mul_spT_mul_spT hf hba
  rw [add_comm] at e2
  calc (spT hf a * spT hf b) ^ 3 = (spT hf a * spT hf b * spT hf a) *
        (spT hf b * spT hf a * spT hf b) := by
          rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, sq]
          simp only [mul_assoc]
    _ = 1 := by rw [e1, e2, spT_mul_self]

omit [FiniteDimensional (ZMod 2) U] in
theorem orderOf_spT_mul_spT (hf : f.IsAlt) (hnd : f.Nondegenerate) {a b : U}
    (hab : f a b = 1) : orderOf (spT hf a * spT hf b) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (spT_mul_spT_pow_three hf hab) fun h1 => ?_
  have ha0 : a ≠ 0 := by
    intro h; rw [h, LinearMap.map_zero₂] at hab; exact zero_ne_one hab
  have h2 : spT hf a = spT hf b := by
    have := congrArg (· * spT hf b) h1
    simpa [mul_assoc, spT_mul_self] using this
  have hab' := eq_of_spT_eq hf hnd ha0 h2
  rw [hab', hf.self_eq_zero] at hab
  exact zero_ne_one hab

theorem commutatorElement_mul_mul_eq {G : Type*} [Group G] {a b c : G} (ha : a * a = 1)
    (hb : b * b = 1) (hca : c * a = a * c) (hcb : c * b = b * c) (h3 : (b * a) ^ 3 = 1) :
    ⁅b * c, a * c⁆ = a * b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  rw [commutatorElement_def, mul_inv_rev, mul_inv_rev, ha', hb']
  have e1 : b * c * (a * c) * (c⁻¹ * b) * (c⁻¹ * a) = b * a * b * a := by
    calc b * c * (a * c) * (c⁻¹ * b) * (c⁻¹ * a) = b * (c * a) * b * c⁻¹ * a := by group
      _ = b * (a * c) * b * c⁻¹ * a := by rw [hca]
      _ = b * a * (c * b) * c⁻¹ * a := by group
      _ = b * a * (b * c) * c⁻¹ * a := by rw [hcb]
      _ = b * a * b * a := by group
  rw [e1]
  have e2 : b * a * b * a * (b * a) = 1 := by
    rw [← h3, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, sq]
    simp only [mul_assoc]
  calc b * a * b * a = b * a * b * a * (b * a) * (b * a)⁻¹ := by group
    _ = (b * a)⁻¹ := by rw [e2, one_mul]
    _ = a * b := by rw [mul_inv_rev, ha', hb']

theorem spT_mul_spT_mem_commutator_of_eq_one (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hn : 5 ≤ finrank (ZMod 2) U) {u v w : U} (hv : f v u = 0) (hw : f w u = 0) (hv0 : v ≠ 0)
    (hvu : v ≠ u) (hw0 : w ≠ 0) (hwu : w ≠ u) (hvw : f v w = 1) :
    spT hf v * spT hf w ∈ ⁅spOmega hf u, spOmega hf u⁆ := by
  obtain ⟨x, hxu, hxv, hxw, hx0, hxu'⟩ := exists_perp_three (f := f) hn u v w
  have hmem := Subgroup.commutator_mem_commutator
    (spT_mul_spT_mem_spOmega hf hw hxu hw0 hwu hx0 hxu')
    (spT_mul_spT_mem_spOmega hf hv hxu hv0 hvu hx0 hxu')
  have hwv : f w v = 1 := by rw [OrthoF2.isAlt_symm hf]; exact hvw
  rw [commutatorElement_mul_mul_eq (spT_mul_self hf v) (spT_mul_self hf w)
    ((spT_mul_comm_iff hf hnd hx0).mpr hxv) ((spT_mul_comm_iff hf hnd hx0).mpr hxw)
    (spT_mul_spT_pow_three hf hwv)] at hmem
  exact hmem

theorem commutator_spOmega (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hn : 5 ≤ finrank (ZMod 2) U) (u : U) :
    ⁅spOmega hf u, spOmega hf u⁆ = spOmega hf u := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  · rw [spOmega, Subgroup.closure_le]
    rintro _ ⟨v, w, hv, hw, hv0, hvu, hw0, hwu, rfl⟩
    rcases OrthoF2.zmod2_eq_zero_or_eq_one (f v w) with h0 | h1
    · obtain ⟨y, hyu, hyv, hyw⟩ := exists_apply_zero_one_one hf hnd hv0 hvu hw0 hwu
      have hy0 : y ≠ 0 := by
        intro h; rw [h, LinearMap.map_zero₂] at hyv; exact zero_ne_one hyv
      have hyu' : y ≠ u := by
        intro h; rw [h, OrthoF2.isAlt_symm hf, hv] at hyv; exact zero_ne_one hyv
      have hvy : f v y = 1 := by rw [OrthoF2.isAlt_symm hf]; exact hyv
      have e : spT hf v * spT hf w = (spT hf v * spT hf y) * (spT hf y * spT hf w) := by
        rw [show (spT hf v * spT hf y) * (spT hf y * spT hf w) =
          spT hf v * (spT hf y * spT hf y) * spT hf w by group, spT_mul_self, mul_one]
      rw [e]
      exact mul_mem (spT_mul_spT_mem_commutator_of_eq_one hf hnd hn hv hyu hv0 hvu hy0 hyu' hvy)
        (spT_mul_spT_mem_commutator_of_eq_one hf hnd hn hyu hw hy0 hyu' hw0 hwu hyw)
    · exact spT_mul_spT_mem_commutator_of_eq_one hf hnd hn hv hw hv0 hvu hw0 hwu h1

omit [FiniteDimensional (ZMod 2) U] in
theorem spOmega_le_centralizer (hf : f.IsAlt) (hnd : f.Nondegenerate) {u : U} :
    spOmega hf u ≤ Subgroup.centralizer {spT hf u} := by
  rw [spOmega, Subgroup.closure_le]
  rintro _ ⟨v, w, hv, hw, hv0, -, hw0, -, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have h1 := (spT_mul_comm_iff hf hnd hv0).mpr hv
  have h2 := (spT_mul_comm_iff hf hnd hw0).mpr hw
  calc spT hf v * spT hf w * spT hf u = spT hf v * (spT hf w * spT hf u) := by group
    _ = spT hf v * (spT hf u * spT hf w) := by rw [h2]
    _ = (spT hf v * spT hf u) * spT hf w := by group
    _ = (spT hf u * spT hf v) * spT hf w := by rw [h1]
    _ = spT hf u * (spT hf v * spT hf w) := by group

end Perfect

section TwoGroups

variable [FiniteDimensional (ZMod 2) U]

omit [FiniteDimensional (ZMod 2) U] in
theorem perp_of_decomp (hf : f.IsAlt) {u a' : U} (ha' : f a' u = 1) (x : U) :
    f (x + f x a' • u + f x u • a') u = 0 ∧ f (x + f x a' • u + f x u • a') a' = 0 := by
  have hua : f u a' = 1 := by rw [OrthoF2.isAlt_symm hf]; exact ha'
  constructor
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hf.self_eq_zero, ha', mul_zero, mul_one, add_zero, OrthoF2.zmod2_add_self]
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hf.self_eq_zero, hua, mul_zero, mul_one, add_zero, OrthoF2.zmod2_add_self]

omit [FiniteDimensional (ZMod 2) U] in
theorem eq_decomp {u a' : U} (x : U) :
    x = (x + f x a' • u + f x u • a') + f x a' • u + f x u • a' := by
  have h1 := smul_add_smul_self (f x a') u
  have h2 := smul_add_smul_self (f x u) a'
  calc x = x + (f x a' • u + f x a' • u) + (f x u • a' + f x u • a') := by rw [h1, h2]; abel
    _ = _ := by abel

omit [FiniteDimensional (ZMod 2) U] in
theorem eq_zero_of_perp_plane (hf : f.IsAlt) (hnd : f.Nondegenerate) {u a' v : U}
    (ha' : f a' u = 1) (hu : f u v = 0) (ha : f a' v = 0)
    (h0 : ∀ x, f x u = 0 → f x a' = 0 → f x v = 0) : v = 0 := by
  refine hnd.1 v fun x => ?_
  rw [OrthoF2.isAlt_symm hf]
  obtain ⟨h1, h2⟩ := perp_of_decomp hf ha' x
  have hx := h0 _ h1 h2
  rw [eq_decomp (f := f) (u := u) (a' := a') x, map_add, map_add, LinearMap.add_apply,
    LinearMap.add_apply, hx, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hu,
    ha, smul_zero, smul_zero, add_zero, add_zero]

omit [FiniteDimensional (ZMod 2) U] in
theorem eq_one_of_fix_plane {u a' : U} (hf : f.IsAlt) (ha' : f a' u = 1)
    {g : TauCeti.BilinForm.isometryGroup f} (hgu : (g : U ≃ₗ[ZMod 2] U) u = u)
    (hga : (g : U ≃ₗ[ZMod 2] U) a' = a')
    (h0 : ∀ x, f x u = 0 → f x a' = 0 → (g : U ≃ₗ[ZMod 2] U) x = x) : g = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  obtain ⟨h1, h2⟩ := perp_of_decomp hf ha' x
  change (g : U ≃ₗ[ZMod 2] U) x = x
  rw [eq_decomp (f := f) (u := u) (a' := a') x, map_add, map_add, h0 _ h1 h2, map_smul,
    map_smul, hgu, hga]

omit [FiniteDimensional (ZMod 2) U] in
theorem perp_apply_of_fix {u a' : U} {g : TauCeti.BilinForm.isometryGroup f}
    (hgu : (g : U ≃ₗ[ZMod 2] U) u = u) (hga : (g : U ≃ₗ[ZMod 2] U) a' = a') {x : U}
    (hxu : f x u = 0) (hxa : f x a' = 0) :
    f ((g : U ≃ₗ[ZMod 2] U) x) u = 0 ∧ f ((g : U ≃ₗ[ZMod 2] U) x) a' = 0 := by
  constructor
  · rw [← hgu, isometry_apply, hxu]
  · rw [← hga, isometry_apply, hxa]

noncomputable def planePerp (f : LinearMap.BilinForm (ZMod 2) U) (u a' : U) :
    Submodule (ZMod 2) U :=
  LinearMap.ker (LinearMap.pi fun i => f.flip (![u, a'] i))

omit [FiniteDimensional (ZMod 2) U] in
theorem mem_planePerp {u a' x : U} : x ∈ planePerp f u a' ↔ f x u = 0 ∧ f x a' = 0 := by
  rw [planePerp, mem_ker_pi_iff]
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1

theorem exists_fix_planePerp (hn : 5 ≤ finrank (ZMod 2) U) {u a' : U}
    {R : Subgroup (TauCeti.BilinForm.isometryGroup f)} (h2 : IsPGroup 2 R) {g}
    (hgR : g ∈ R) (hgu : (g : U ≃ₗ[ZMod 2] U) u = u) (hga : (g : U ≃ₗ[ZMod 2] U) a' = a') :
    ∃ w, f w u = 0 ∧ f w a' = 0 ∧ w ≠ 0 ∧ (g : U ≃ₗ[ZMod 2] U) w = w := by
  have : Finite U := Module.finite_of_finite (ZMod 2)
  have hP : IsPGroup 2 (Subgroup.zpowers g) := h2.to_le (Subgroup.zpowers_le.mpr hgR)
  let φ : ↥(Subgroup.zpowers g) →* (U ≃ₗ[ZMod 2] U) :=
    (TauCeti.BilinForm.isometryGroup f).subtype.comp (Subgroup.zpowers g).subtype
  have hle : Subgroup.zpowers g ≤
      MulAction.stabilizer (TauCeti.BilinForm.isometryGroup f) u ⊓
        MulAction.stabilizer (TauCeti.BilinForm.isometryGroup f) a' := by
    rw [Subgroup.zpowers_le]
    refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, MulAction.mem_stabilizer_iff.mpr ?_⟩
    · rw [Subgroup.smul_def, LinearEquiv.smul_def]; exact hgu
    · rw [Subgroup.smul_def, LinearEquiv.smul_def]; exact hga
  have hinv : ∀ (x : ↥(Subgroup.zpowers g)) v, v ∈ planePerp f u a' →
      φ x v ∈ planePerp f u a' := by
    intro x v hv
    rw [mem_planePerp] at hv ⊢
    have hx := hle x.2
    have hxu : (((x : TauCeti.BilinForm.isometryGroup f)) : U ≃ₗ[ZMod 2] U) u = u := by
      have := MulAction.mem_stabilizer_iff.mp hx.1
      rwa [Subgroup.smul_def, LinearEquiv.smul_def] at this
    have hxa : (((x : TauCeti.BilinForm.isometryGroup f)) : U ≃ₗ[ZMod 2] U) a' = a' := by
      have := MulAction.mem_stabilizer_iff.mp hx.2
      rwa [Subgroup.smul_def, LinearEquiv.smul_def] at this
    exact perp_apply_of_fix hxu hxa hv.1 hv.2
  have hne : planePerp f u a' ≠ ⊥ := by
    intro h
    have hk := finrank_ker_pi_ge (f := f) ![u, a']
    have : finrank (ZMod 2) (planePerp f u a') = 0 := by rw [h]; simp
    rw [planePerp] at this
    omega
  obtain ⟨w, hw, hw0, hwfix⟩ := CFSG.LargeExtraspecial.S4.exists_fixed_ne_zero hP φ hinv hne
  rw [mem_planePerp] at hw
  exact ⟨w, hw.1, hw.2, hw0, hwfix ⟨g, Subgroup.mem_zpowers g⟩⟩

omit [FiniteDimensional (ZMod 2) U] in
theorem commutatorElement_spT (hf : f.IsAlt) {g : TauCeti.BilinForm.isometryGroup f} {y w : U}
    (hgw : (g : U ≃ₗ[ZMod 2] U) w = w) :
    g * (spT hf y * spT hf w) * g⁻¹ * (spT hf y * spT hf w)⁻¹ =
      spT hf ((g : U ≃ₗ[ZMod 2] U) y) * spT hf y := by
  have hinv : ∀ c : U, (spT hf c)⁻¹ = spT hf c := fun c =>
    inv_eq_of_mul_eq_one_left (spT_mul_self hf c)
  have e1 : g * (spT hf y * spT hf w) * g⁻¹ =
      (g * spT hf y * g⁻¹) * (g * spT hf w * g⁻¹) := by group
  rw [e1, spT_conj, spT_conj, hgw, mul_inv_rev, hinv, hinv]
  calc spT hf ((g : U ≃ₗ[ZMod 2] U) y) * spT hf w * (spT hf w * spT hf y)
      = spT hf ((g : U ≃ₗ[ZMod 2] U) y) * (spT hf w * spT hf w) * spT hf y := by group
    _ = _ := by rw [spT_mul_self, mul_one]

theorem not_mem_of_orderOf_eq_three {G : Type*} [Group G] {R : Subgroup G} (h2 : IsPGroup 2 R)
    {c : G} (hc : orderOf c = 3) : c ∉ R := by
  intro hcR
  obtain ⟨k, hk⟩ := h2 ⟨c, hcR⟩
  have hk' : c ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd := orderOf_dvd_of_pow_eq_one hk'
  rw [hc] at hdvd
  have h3 : (3 : ℕ) ∣ 2 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
  omega

theorem isPGroup_spRadical (hf : f.IsAlt) (hnd : f.Nondegenerate) {u : U} (hu : u ≠ 0) :
    IsPGroup 2 (spRadical f u) :=
  IsPGroup.of_card (card_spRadical hf hnd hu)

omit [FiniteDimensional (ZMod 2) U] in
theorem mem_normalizer_spRadical (hf : f.IsAlt) {u : U} {g : TauCeti.BilinForm.isometryGroup f}
    (hg : (g : U ≃ₗ[ZMod 2] U) u = u) :
    g ∈ Subgroup.normalizer (spRadical f u : Set (TauCeti.BilinForm.isometryGroup f)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => conj_mem_spRadical hf hg hk, fun hk => ?_⟩
  have hg' : ((g⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) u = u := by
    conv_lhs => rw [← hg]
    exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' _ u
  have := conj_mem_spRadical hf hg' hk
  rwa [show g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k by group] at this

omit [FiniteDimensional (ZMod 2) U] in
theorem apply_eq_of_mem_spOmega (hf : f.IsAlt) (hnd : f.Nondegenerate) {u : U} (hu : u ≠ 0)
    {ρ : TauCeti.BilinForm.isometryGroup f} (hρ : ρ ∈ spOmega hf u) :
    (ρ : U ≃ₗ[ZMod 2] U) u = u :=
  apply_eq_of_commute_spT hf hnd hu
    (Subgroup.mem_centralizer_singleton_iff.mp (spOmega_le_centralizer hf hnd hρ))

omit [FiniteDimensional (ZMod 2) U] in
theorem spT_mul_spT_apply_self (hf : f.IsAlt) {a y : U} (hya : f y a = 0) (x : U) :
    f (((spT hf a * spT hf y : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) x) x =
      f x y + f x a := by
  rw [spT_mul_apply, spT_apply, spT_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hya,
    mul_zero, add_zero, hf.self_eq_zero, zero_add]
  rw [OrthoF2.isAlt_symm hf y x, OrthoF2.isAlt_symm hf a x, OrthoF2.zmod2_mul_self,
    OrthoF2.zmod2_mul_self]

theorem le_spRadical_of_isPGroup (hf : f.IsAlt)
    (hnd : f.Nondegenerate) (hn : 5 ≤ finrank (ZMod 2) U) {u : U} (hu : u ≠ 0)
    {R : Subgroup (TauCeti.BilinForm.isometryGroup f)}
    (hR : ∀ g ∈ R, (g : U ≃ₗ[ZMod 2] U) u = u) (h2 : IsPGroup 2 R)
    (hN : spOmega hf u ≤ Subgroup.normalizer (R : Set (TauCeti.BilinForm.isometryGroup f))) :
    R ≤ spRadical f u := by
  obtain ⟨a', ha'⟩ := exists_apply_eq_one_of_ne_zero hnd hu
  have hua : f u a' = 1 := by rw [OrthoF2.isAlt_symm hf]; exact ha'
  have hRK : R ≤ Subgroup.normalizer
      (spRadical f u : Set (TauCeti.BilinForm.isometryGroup f)) := fun g hg =>
    mem_normalizer_spRadical hf (hR g hg)
  have hR' : IsPGroup 2 (R ⊔ spRadical f u : Subgroup _) :=
    IsPGroup.to_sup_of_normal_right' h2 (isPGroup_spRadical hf hnd hu) hRK
  have hN' : spOmega hf u ≤ Subgroup.normalizer
      ((R ⊔ spRadical f u : Subgroup _) : Set (TauCeti.BilinForm.isometryGroup f)) :=
    fun ρ hρ => Subgroup.inf_normalizer_le_normalizer_sup R (spRadical f u)
      ⟨hN hρ, mem_normalizer_spRadical hf (apply_eq_of_mem_spOmega hf hnd hu hρ)⟩
  have hcomm : ∀ g ∈ (R ⊔ spRadical f u : Subgroup _), ∀ ρ ∈ spOmega hf u,
      g * ρ * g⁻¹ * ρ⁻¹ ∈ (R ⊔ spRadical f u : Subgroup _) := by
    intro g hg ρ hρ
    have h1 : ρ * g⁻¹ * ρ⁻¹ ∈ (R ⊔ spRadical f u : Subgroup _) :=
      (Subgroup.mem_normalizer_iff.mp (hN' hρ) _).mp (inv_mem hg)
    rw [show g * ρ * g⁻¹ * ρ⁻¹ = g * (ρ * g⁻¹ * ρ⁻¹) by group]
    exact mul_mem hg h1
  have hne_u : ∀ y, f y a' = 0 → y ≠ u := fun y hy h => by
    rw [h, hua] at hy; exact one_ne_zero hy
  have hC : ∀ g ∈ (R ⊔ spRadical f u : Subgroup _), (g : U ≃ₗ[ZMod 2] U) u = u →
      (g : U ≃ₗ[ZMod 2] U) a' = a' → ∀ y, f y u = 0 → f y a' = 0 →
        spT hf ((g : U ≃ₗ[ZMod 2] U) y) * spT hf y ∈ (R ⊔ spRadical f u : Subgroup _) := by
    intro g hg hgu hga y hyu hya
    by_cases hy0 : y = 0
    · rw [hy0, map_zero, spT_zero, one_mul]; exact one_mem _
    obtain ⟨w, hwu, hwa, hw0, hgw⟩ := exists_fix_planePerp hn hR' hg hgu hga
    have hρ := spT_mul_spT_mem_spOmega hf hyu hwu hy0 (hne_u y hya) hw0 (hne_u w hwa)
    have := hcomm g hg _ hρ
    rwa [commutatorElement_spT hf hgw] at this
  have hA : ∀ g ∈ (R ⊔ spRadical f u : Subgroup _), (g : U ≃ₗ[ZMod 2] U) u = u →
      (g : U ≃ₗ[ZMod 2] U) a' = a' → ∀ y, f y u = 0 → f y a' = 0 →
        f ((g : U ≃ₗ[ZMod 2] U) y) y = 0 := by
    intro g hg hgu hga y hyu hya
    by_contra hne
    have h1 : f ((g : U ≃ₗ[ZMod 2] U) y) y = 1 := OrthoF2.zmod2_eq_one_of_ne_zero hne
    exact not_mem_of_orderOf_eq_three hR' (orderOf_spT_mul_spT hf hnd h1)
      (hC g hg hgu hga y hyu hya)
  have hB : ∀ g ∈ (R ⊔ spRadical f u : Subgroup _), (g : U ≃ₗ[ZMod 2] U) u = u →
      (g : U ≃ₗ[ZMod 2] U) a' = a' → g = 1 := by
    intro g hg hgu hga
    refine eq_one_of_fix_plane hf ha' hgu hga fun y hyu hya => ?_
    obtain ⟨hgyu, hgya⟩ := perp_apply_of_fix hgu hga hyu hya
    have huy : f u y = 0 := by rw [OrthoF2.isAlt_symm hf]; exact hyu
    have hay : f a' y = 0 := by rw [OrthoF2.isAlt_symm hf]; exact hya
    have hugy : f u ((g : U ≃ₗ[ZMod 2] U) y) = 0 := by
      rw [OrthoF2.isAlt_symm hf]; exact hgyu
    have hagy : f a' ((g : U ≃ₗ[ZMod 2] U) y) = 0 := by
      rw [OrthoF2.isAlt_symm hf]; exact hgya
    have ht := hC g hg hgu hga y hyu hya
    have htu : ((spT hf ((g : U ≃ₗ[ZMod 2] U) y) * spT hf y :
        TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) u = u := by
      rw [spT_mul_apply, spT_apply_of_eq_zero hf huy, spT_apply_of_eq_zero hf hugy]
    have hta : ((spT hf ((g : U ≃ₗ[ZMod 2] U) y) * spT hf y :
        TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) a' = a' := by
      rw [spT_mul_apply, spT_apply_of_eq_zero hf hay, spT_apply_of_eq_zero hf hagy]
    have hAt := hA _ ht htu hta
    have hyy : f y ((g : U ≃ₗ[ZMod 2] U) y) = 0 := by
      rw [OrthoF2.isAlt_symm hf]; exact hA g hg hgu hga y hyu hya
    have hperp : ∀ x, f x u = 0 → f x a' = 0 → f x (y + (g : U ≃ₗ[ZMod 2] U) y) = 0 := by
      intro x hxu hxa
      have h := hAt x hxu hxa
      rw [spT_mul_spT_apply_self hf hyy] at h
      rw [map_add, h]
    have hv := eq_zero_of_perp_plane hf hnd ha'
      (by rw [map_add, huy, hugy, add_zero]) (by rw [map_add, hay, hagy, add_zero]) hperp
    have := congrArg (· + y) hv
    simpa [add_comm y ((g : U ≃ₗ[ZMod 2] U) y), add_assoc, OrthoF2.vec_add_self] using this
  intro z hz
  have hzu := hR z hz
  have hs : f ((z : U ≃ₗ[ZMod 2] U) a' - a') u = 0 := by
    rw [map_sub, LinearMap.sub_apply]
    conv_lhs => rw [show f ((z : U ≃ₗ[ZMod 2] U) a') u =
      f ((z : U ≃ₗ[ZMod 2] U) a') ((z : U ≃ₗ[ZMod 2] U) u) by rw [hzu]]
    rw [isometry_apply, sub_self]
  obtain ⟨k, hk, -, hka⟩ := exists_mem_spRadical_apply hf hn ha' hs
  have hkz : k⁻¹ * z ∈ (R ⊔ spRadical f u : Subgroup _) :=
    mul_mem (inv_mem ((le_sup_right : spRadical f u ≤ R ⊔ spRadical f u) hk))
      ((le_sup_left : R ≤ R ⊔ spRadical f u) hz)
  have hku : (k : U ≃ₗ[ZMod 2] U) u = u := ((mem_spRadical_iff hf).mp hk).1
  have hkinv : ∀ x, ((k⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U)
      ((k : U ≃ₗ[ZMod 2] U) x) = x := fun x =>
    CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' _ x
  have hgu : ((k⁻¹ * z : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) u = u := by
    change ((k⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U)
      ((z : U ≃ₗ[ZMod 2] U) u) = u
    rw [hzu]
    conv_lhs => rw [← hku]
    exact hkinv u
  have hga : ((k⁻¹ * z : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) a' = a' := by
    change ((k⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U)
      ((z : U ≃ₗ[ZMod 2] U) a') = a'
    rw [show (z : U ≃ₗ[ZMod 2] U) a' = (k : U ≃ₗ[ZMod 2] U) a' by rw [hka]; abel]
    exact hkinv a'
  have h1 := hB _ hkz hgu hga
  have hzk : z = k := by
    calc z = k * (k⁻¹ * z) := by group
      _ = k := by rw [h1, mul_one]
  rw [hzk]
  exact hk

theorem eq_zpowers_or_eq_spRadical (hf : f.IsAlt)
    (hnd : f.Nondegenerate) (hn : 5 ≤ finrank (ZMod 2) U) {u : U} (hu : u ≠ 0)
    {E : Subgroup (TauCeti.BilinForm.isometryGroup f)} (h1 : spT hf u ∈ E)
    (h2 : E ≤ spRadical f u)
    (hN : spOmega hf u ≤ Subgroup.normalizer (E : Set (TauCeti.BilinForm.isometryGroup f))) :
    E = Subgroup.zpowers (spT hf u) ∨ E = spRadical f u := by
  obtain ⟨a', ha'⟩ := exists_apply_eq_one_of_ne_zero hnd hu
  have hua : f u a' = 1 := by rw [OrthoF2.isAlt_symm hf]; exact ha'
  have hK : ∀ k ∈ spRadical f u, ∀ x, f x u = 0 →
      (k : U ≃ₗ[ZMod 2] U) x = x + f x ((k : U ≃ₗ[ZMod 2] U) a' - a') • u := by
    intro k hk x hx
    exact spPointRadical_apply_of_orthogonal hua (Subgroup.mem_subgroupOf.mp hk)
      (by rw [OrthoF2.isAlt_symm hf]; exact hx)
  let P : U → Prop := fun s => ∃ e ∈ E, (e : U ≃ₗ[ZMod 2] U) a' = a' + s
  have hP0 : P 0 := ⟨1, one_mem _, by rw [add_zero]; rfl⟩
  have hPu : P u := ⟨spT hf u, h1, by rw [spT_apply, ha', one_smul]⟩
  have hPperp : ∀ s, P s → f s u = 0 := by
    rintro s ⟨e, he, hes⟩
    have := apply_sub_perp_of_mem_spRadical hf (h2 he) a'
    rwa [hes, add_sub_cancel_left] at this
  have hPadd' : ∀ s s', P s → P s' → P (s + s' + f s' s • u) := by
    rintro s s' ⟨e, he, hes⟩ ⟨e', he', hes'⟩
    refine ⟨e * e', mul_mem he he', ?_⟩
    have hs'u : f s' u = 0 := hPperp s' ⟨e', he', hes'⟩
    change (e : U ≃ₗ[ZMod 2] U) ((e' : U ≃ₗ[ZMod 2] U) a') = _
    rw [hes', map_add, hes, hK e (h2 he) s' hs'u, hes, add_sub_cancel_left]
    abel
  have hPu' : ∀ s, P s → P (s + u) := by
    intro s hs
    have := hPadd' s u hs hPu
    rwa [show f u s = 0 by rw [OrthoF2.isAlt_symm hf]; exact hPperp s hs, zero_smul,
      add_zero] at this
  have hPadd : ∀ s s', P s → P s' → P (s + s') := by
    intro s s' hs hs'
    rcases OrthoF2.zmod2_eq_zero_or_eq_one (f s' s) with h0 | h1'
    · have := hPadd' s s' hs hs'
      rwa [h0, zero_smul, add_zero] at this
    · have := hPu' _ (hPadd' s s' hs hs')
      rwa [h1', one_smul, add_assoc (s + s'), OrthoF2.vec_add_self, add_zero] at this
  have hPconj : ∀ ρ ∈ spOmega hf u, ∀ s, P s → P ((ρ : U ≃ₗ[ZMod 2] U) s) := by
    rintro ρ hρ s ⟨e, he, hes⟩
    have hρu := apply_eq_of_mem_spOmega hf hnd hu hρ
    have hsu : f s u = 0 := hPperp s ⟨e, he, hes⟩
    have hconj : ρ * e * ρ⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hN hρ) e).mp he
    set r := ((ρ⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) a' - a' with hr
    have hρinv : ∀ x, (ρ : U ≃ₗ[ZMod 2] U)
        (((ρ⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) x) = x := fun x =>
      OrthoF2.apply_inv_apply _ x
    have hρinvu : ((ρ⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) u = u := by
      conv_lhs => rw [← hρu]
      exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' _ u
    have hru : f r u = 0 := by
      rw [hr, map_sub, LinearMap.sub_apply, ha']
      conv_lhs => rw [show f (((ρ⁻¹ : TauCeti.BilinForm.isometryGroup f) :
        U ≃ₗ[ZMod 2] U) a') u = f (((ρ⁻¹ : TauCeti.BilinForm.isometryGroup f) :
          U ≃ₗ[ZMod 2] U) a') (((ρ⁻¹ : TauCeti.BilinForm.isometryGroup f) :
            U ≃ₗ[ZMod 2] U) u) by rw [hρinvu]]
      rw [isometry_apply, ha', sub_self]
    have key : ((ρ * e * ρ⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) a' =
        a' + ((ρ : U ≃ₗ[ZMod 2] U) s + f r s • u) := by
      change (ρ : U ≃ₗ[ZMod 2] U) ((e : U ≃ₗ[ZMod 2] U)
        (((ρ⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) a')) = _
      have hra : ((ρ⁻¹ : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) a' = a' + r := by
        rw [hr]; abel
      rw [hra, map_add, hes, hK e (h2 he) r hru, hes, add_sub_cancel_left, map_add, map_add,
        map_add, map_smul, hρu]
      have : (ρ : U ≃ₗ[ZMod 2] U) a' + (ρ : U ≃ₗ[ZMod 2] U) r = a' := by
        rw [← map_add, show a' + r = ((ρ⁻¹ : TauCeti.BilinForm.isometryGroup f) :
          U ≃ₗ[ZMod 2] U) a' by rw [hr]; abel, hρinv]
      calc (ρ : U ≃ₗ[ZMod 2] U) a' + (ρ : U ≃ₗ[ZMod 2] U) s +
            ((ρ : U ≃ₗ[ZMod 2] U) r + f r s • u)
          = ((ρ : U ≃ₗ[ZMod 2] U) a' + (ρ : U ≃ₗ[ZMod 2] U) r) +
            ((ρ : U ≃ₗ[ZMod 2] U) s + f r s • u) := by abel
        _ = _ := by rw [this]
    have hP' : P ((ρ : U ≃ₗ[ZMod 2] U) s + f r s • u) := ⟨_, hconj, key⟩
    rcases OrthoF2.zmod2_eq_zero_or_eq_one (f r s) with h0 | h1'
    · rwa [h0, zero_smul, add_zero] at hP'
    · have := hPu' _ hP'
      rwa [h1', one_smul, add_assoc, OrthoF2.vec_add_self, add_zero] at this
  have hstep : ∀ s v, P s → f v u = 0 → v ≠ 0 → v ≠ u → f s v = 1 → P v := by
    intro s v hs hvu hv0 hvu' hsv
    have hsu : f s u = 0 := hPperp s hs
    obtain ⟨w, hwu, hws, hwv, hw0, hwu'⟩ := exists_perp_three (f := f) hn u s v
    have hρ := spT_mul_spT_mem_spOmega hf hvu hwu hv0 hvu' hw0 hwu'
    have hρs : ((spT hf v * spT hf w : TauCeti.BilinForm.isometryGroup f) :
        U ≃ₗ[ZMod 2] U) s = s + v := by
      have hsw : f s w = 0 := by rw [OrthoF2.isAlt_symm hf]; exact hws
      rw [spT_mul_apply, spT_apply_of_eq_zero hf hsw, spT_apply_of_eq_one hf hsv]
    have h := hPadd _ _ (hPconj _ hρ s hs) hs
    rwa [hρs, add_comm s v, add_assoc, OrthoF2.vec_add_self, add_zero] at h
  by_cases hall : ∀ e ∈ E, e = 1 ∨ e = spT hf u
  · left
    refine le_antisymm (fun e he => ?_) ((Subgroup.zpowers_le).mpr h1)
    rcases hall e he with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
  · right
    push Not at hall
    obtain ⟨e, he, he1, heu⟩ := hall
    set s := (e : U ≃ₗ[ZMod 2] U) a' - a' with hsdef
    have hes : (e : U ≃ₗ[ZMod 2] U) a' = a' + s := by rw [hsdef]; abel
    have hs : P s := ⟨e, he, hes⟩
    have hsu : f s u = 0 := hPperp s hs
    have hs0 : s ≠ 0 := by
      intro h0
      apply he1
      refine spRadical_ext hf ha' (h2 he) (one_mem _) ?_
      rw [hes, h0, add_zero]; rfl
    have hsu' : s ≠ u := by
      intro h0
      apply heu
      refine spRadical_ext hf ha' (h2 he) (spT_mem_spRadical hf u) ?_
      rw [hes, h0, spT_apply, ha', one_smul]
    have hall' : ∀ v, f v u = 0 → P v := by
      intro v hvu
      by_cases hv0 : v = 0
      · rw [hv0]; exact hP0
      by_cases hvu' : v = u
      · rw [hvu']; exact hPu
      rcases OrthoF2.zmod2_eq_zero_or_eq_one (f s v) with h0 | h1'
      · obtain ⟨y, hyu, hys, hyv⟩ := exists_apply_zero_one_one hf hnd hs0 hsu' hv0 hvu'
        have hy0 : y ≠ 0 := by
          intro h; rw [h, LinearMap.map_zero₂] at hys; exact zero_ne_one hys
        have hyu' : y ≠ u := by
          intro h; rw [h, OrthoF2.isAlt_symm hf, hsu] at hys; exact zero_ne_one hys
        have hsy : f s y = 1 := by rw [OrthoF2.isAlt_symm hf]; exact hys
        exact hstep y v (hstep s y hs hyu hy0 hyu' hsy) hvu hv0 hvu' hyv
      · exact hstep s v hs hvu hv0 hvu' h1'
    refine le_antisymm h2 fun k hk => ?_
    obtain ⟨e', he', he's⟩ := hall' _ (apply_sub_perp_of_mem_spRadical hf hk a')
    have : e' = k := spRadical_ext hf ha' (h2 he') hk (by rw [he's]; abel)
    rw [← this]
    exact he'

end TwoGroups

end CFSG.Fischer.Classification.Orth2
