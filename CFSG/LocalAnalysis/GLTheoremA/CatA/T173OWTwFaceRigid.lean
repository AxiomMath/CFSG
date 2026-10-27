module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OWTwFaceFactor

import CFSG.LinearAlgebra.LinearGroups.SLConjugationKer
import CFSG.LieType.Chevalley.SubsystemComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LieType.Chevalley.SubsysComp


private theorem mul_mem_centralizer_of_mul_eq_mul {G : Type*} [Group G] {C : Subgroup G}
    {y a r : G} (hy : y ∈ C) (hr : r ∈ C) (h : y = a * r) : a ∈ C := by
  have : a = y * r⁻¹ := by rw [h]; group
  rw [this]
  exact Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hr)

private theorem mem_subsystemGroup_range {F : Type} [Field F] {m : ℕ}
    {S : Set (Fin TwistTag.E6.tag.rank)} (f : LeviFactor F m S)
    (h : Matrix.SpecialLinearGroup (Fin m) F) :
    f.ι h ∈ subsystemGroup TwistTag.E6.tag F S := by
  rw [← f.range_eq]
  exact MonoidHom.mem_range.2 ⟨h, rfl⟩

private theorem subsystemGroup_le_centralizer_range {F : Type} [Field F] {m : ℕ}
    {S T : Set (Fin TwistTag.E6.tag.rank)} (f : LeviFactor F m S) (hST : Disjoint S T)
    (h0 : ∀ i ∈ S, ∀ j ∈ T, TwistTag.E6.tag.cartan i j = 0) :
    subsystemGroup TwistTag.E6.tag F T ≤
      Subgroup.centralizer (f.ι.range : Set (ModGL TwistTag.E6.tag F)) := by
  rw [f.range_eq]
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (commute_of_cartan_eq_zero (A := S) (B := T) (K := F) hST h0 x hx y hy).eq

private theorem subsystemGroup_le_centralizer_range' {F : Type} [Field F] {m : ℕ}
    {S T : Set (Fin TwistTag.E6.tag.rank)} (f : LeviFactor F m T) (hST : Disjoint S T)
    (h0 : ∀ i ∈ S, ∀ j ∈ T, TwistTag.E6.tag.cartan i j = 0) :
    subsystemGroup TwistTag.E6.tag F S ≤
      Subgroup.centralizer (f.ι.range : Set (ModGL TwistTag.E6.tag F)) := by
  rw [f.range_eq]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (commute_of_cartan_eq_zero (A := S) (B := T) (K := F) hST h0 x hx y hy).eq.symm

private theorem rootDiagUnit_apply_eq_one_of_mem_centralizer {F : Type} [Field F] {m : ℕ}
    {S : Set (Fin TwistTag.E6.tag.rank)} (f : LeviFactor F m S)
    {b' : Fin TwistTag.E6.tag.rank → Fˣ} {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ S)
    (hc : rootDiagUnit TwistTag.E6.tag b' ∈
      Subgroup.centralizer (f.ι.range : Set (ModGL TwistTag.E6.tag F))) :
    b' i = 1 := by
  have hx : xUnit TwistTag.E6.tag F i 1 ∈ f.ι.range := by
    rw [f.range_eq]
    exact xUnit_mem_subsystemGroup hi 1
  have hcomm : rootDiagUnit TwistTag.E6.tag b' * xUnit TwistTag.E6.tag F i 1 *
      (rootDiagUnit TwistTag.E6.tag b')⁻¹ = xUnit TwistTag.E6.tag F i 1 := by
    have h1 := Subgroup.mem_centralizer_iff.mp hc (xUnit TwistTag.E6.tag F i 1) hx
    rw [← h1]
    group
  have h2 := (root_diagonal_conjugation TwistTag.E6.tag F b').1 i 1
  have h3 : (b' i : F) * 1 = 1 := by
    apply pinnedX_injective (τ := TwistTag.E6.tag) (R := F) (α := Pi.single i 1)
    rw [pinnedX_single, pinnedX_single]
    exact h2.symm.trans hcomm
  exact Units.ext (by simpa using h3)

private theorem slConj_mul_inv_eq_self {F : Type} [Field F] {m : ℕ}
    {S : Set (Fin TwistTag.E6.tag.rank)} (f : LeviFactor F m S)
    (b : Fin TwistTag.E6.tag.rank → Fˣ) {h : Matrix.SpecialLinearGroup (Fin m) F}
    (D : Matrix.GeneralLinearGroup (Fin m) F)
    (hconj : ∀ g, rootDiagUnit TwistTag.E6.tag b * f.ι g *
      (rootDiagUnit TwistTag.E6.tag b)⁻¹ = f.ι (slConjugation m F D g))
    (hc : rootDiagUnit TwistTag.E6.tag b * f.ι h ∈
      Subgroup.centralizer (f.ι.range : Set (ModGL TwistTag.E6.tag F))) :
    ∀ g : Matrix.SpecialLinearGroup (Fin m) F,
      slConjugation m F D (h * g * h⁻¹) = g := by
  intro g
  apply f.injective
  have hmem := Subgroup.mem_centralizer_iff.mp hc (f.ι g) ⟨g, rfl⟩
  have h1 : rootDiagUnit TwistTag.E6.tag b * f.ι h * f.ι g * (f.ι h)⁻¹ *
      (rootDiagUnit TwistTag.E6.tag b)⁻¹ = f.ι g := by
    rw [← hmem]; group
  have h2 : rootDiagUnit TwistTag.E6.tag b * f.ι (h * g * h⁻¹) *
      (rootDiagUnit TwistTag.E6.tag b)⁻¹ = f.ι g := by
    rw [map_mul, map_mul, map_inv]
    simpa only [mul_assoc] using h1
  have h3 := hconj (h * g * h⁻¹)
  rw [h2] at h3
  exact h3.symm

private theorem mul_toGL_eq_scalar {F : Type} [Field F] {m : ℕ}
    (D : Matrix.GeneralLinearGroup (Fin m) F) (h : Matrix.SpecialLinearGroup (Fin m) F)
    (hfix : ∀ g : Matrix.SpecialLinearGroup (Fin m) F,
      slConjugation m F D (h * g * h⁻¹) = g) :
    ∃ a : F, (D : Matrix (Fin m) (Fin m) F) * (h : Matrix (Fin m) (Fin m) F) =
      Matrix.scalar (Fin m) a := by
  set B : Matrix.GeneralLinearGroup (Fin m) F := D * Matrix.SpecialLinearGroup.toGL h with hB
  have hcomm : ∀ g, B * Matrix.SpecialLinearGroup.toGL g =
      Matrix.SpecialLinearGroup.toGL g * B := by
    intro g
    have h1 := congrArg Matrix.SpecialLinearGroup.toGL (hfix g)
    rw [toGL_slConjugation] at h1
    rw [map_mul, map_mul, map_inv] at h1
    have h2 : B * Matrix.SpecialLinearGroup.toGL g * B⁻¹ =
        Matrix.SpecialLinearGroup.toGL g := by
      calc B * Matrix.SpecialLinearGroup.toGL g * B⁻¹
          = D * (Matrix.SpecialLinearGroup.toGL h * Matrix.SpecialLinearGroup.toGL g *
              (Matrix.SpecialLinearGroup.toGL h)⁻¹) * D⁻¹ := by
            rw [hB, mul_inv_rev]; group
        _ = Matrix.SpecialLinearGroup.toGL g := h1
    calc B * Matrix.SpecialLinearGroup.toGL g
        = B * Matrix.SpecialLinearGroup.toGL g * B⁻¹ * B := by group
      _ = Matrix.SpecialLinearGroup.toGL g * B := by rw [h2]
  have hBker : B ∈ (slConjugation m F).ker := by
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro g
    change slConjugation m F B g = g
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [toGL_slConjugation, hcomm g]
    group
  have hBcenter : B ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin m) F) := by
    rw [← CFSG.LinearGroups.ker_slConjugation m F]
    exact hBker
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hBcenter
  refine ⟨a, ?_⟩
  simp only [hB, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at ha ⊢
  exact ha.symm

theorem LeviFactor.diag_of_mem_centralizer {F : Type} [Field F] {m : ℕ}
    {S : Set (Fin TwistTag.E6.tag.rank)} (f : LeviFactor F m S)
    (b : Fin TwistTag.E6.tag.rank → Fˣ) {h : Matrix.SpecialLinearGroup (Fin m) F}
    (hc : rootDiagUnit TwistTag.E6.tag b * f.ι h ∈
      Subgroup.centralizer (f.ι.range : Set (ModGL TwistTag.E6.tag F))) :
    ∀ a a' : Fin m, a ≠ a' → (h : Matrix (Fin m) (Fin m) F) a a' = 0 := by
  obtain ⟨D, hD, hconj⟩ := f.diag_conj b
  obtain ⟨a, hBa⟩ := mul_toGL_eq_scalar D h (slConj_mul_inv_eq_self f b D hconj hc)
  have hDdiag : (D : Matrix (Fin m) (Fin m) F) =
      Matrix.diagonal (fun i => (D : Matrix (Fin m) (Fin m) F) i i) := by
    ext i j
    rw [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij]; exact hD i j hij
  have hDaa : ∀ a : Fin m, (D : Matrix (Fin m) (Fin m) F) a a ≠ 0 := by
    intro a h0
    have hDinv : (D : Matrix (Fin m) (Fin m) F) *
        ((D⁻¹ : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have hentry : (D : Matrix (Fin m) (Fin m) F) a a *
        ((D⁻¹ : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) a a = 1 := by
      have h1 := congrFun (congrFun hDinv a) a
      rw [hDdiag, Matrix.diagonal_mul] at h1
      simpa using h1
    rw [h0, zero_mul] at hentry
    exact one_ne_zero hentry.symm
  intro a a' haa'
  have h2 : (D : Matrix (Fin m) (Fin m) F) a a *
      (h : Matrix (Fin m) (Fin m) F) a a' = 0 := by
    have h1 : (Matrix.diagonal (fun i => (D : Matrix (Fin m) (Fin m) F) i i) *
        (h : Matrix (Fin m) (Fin m) F)) a a' = 0 := by
      rw [← hDdiag, hBa]
      simp [Matrix.scalar_apply, haa']
    rw [Matrix.diagonal_mul] at h1
    simpa using h1
  exact (mul_eq_zero.mp h2).resolve_left (hDaa a)

private theorem exists_mul_factors {F : Type} [Field F] {m₁ m₂ m₃ : ℕ}
    {S₁ S₂ S₃ : Set (Fin TwistTag.E6.tag.rank)}
    (f₁ : LeviFactor F m₁ S₁) (f₂ : LeviFactor F m₂ S₂) (f₃ : LeviFactor F m₃ S₃)
    (h12 : Disjoint S₁ S₂) (h13 : Disjoint S₁ S₃) (h23 : Disjoint S₂ S₃)
    (c12 : ∀ i ∈ S₁, ∀ j ∈ S₂, TwistTag.E6.tag.cartan i j = 0)
    (c13 : ∀ i ∈ S₁, ∀ j ∈ S₃, TwistTag.E6.tag.cartan i j = 0)
    (c23 : ∀ i ∈ S₂, ∀ j ∈ S₃, TwistTag.E6.tag.cartan i j = 0)
    {s : ModGL TwistTag.E6.tag F}
    (hs : s ∈ subsystemGroup TwistTag.E6.tag F (S₁ ∪ S₂ ∪ S₃)) :
    ∃ (h₁ : Matrix.SpecialLinearGroup (Fin m₁) F)
      (h₂ : Matrix.SpecialLinearGroup (Fin m₂) F)
      (h₃ : Matrix.SpecialLinearGroup (Fin m₃) F) (t₁ : ModGL TwistTag.E6.tag F),
      s = f₁.ι h₁ * t₁ ∧ t₁ = f₂.ι h₂ * f₃.ι h₃ ∧
        t₁ ∈ subsystemGroup TwistTag.E6.tag F (S₂ ∪ S₃) ∧
        f₁.ι h₁ ∈ subsystemGroup TwistTag.E6.tag F S₁ ∧
        f₂.ι h₂ ∈ subsystemGroup TwistTag.E6.tag F S₂ := by
  rw [Set.union_assoc] at hs
  have h01 : ∀ i ∈ S₁, ∀ j ∈ S₂ ∪ S₃, TwistTag.E6.tag.cartan i j = 0 := by
    rintro i hi j (hj | hj)
    · exact c12 i hi j hj
    · exact c13 i hi j hj
  have hdisj : Disjoint S₁ (S₂ ∪ S₃) := Set.disjoint_union_right.2 ⟨h12, h13⟩
  obtain ⟨h₁, t₁, ht₁, hs1⟩ := f₁.exists_eq_mul hdisj h01 hs
  obtain ⟨h₂, t₂, ht₂, ht1⟩ := f₂.exists_eq_mul h23 c23 ht₁
  have ht2range : t₂ ∈ f₃.ι.range := by rwa [f₃.range_eq]
  obtain ⟨h₃, h3eq⟩ := MonoidHom.mem_range.1 ht2range
  subst t₂
  exact ⟨h₁, h₂, h₃, t₁, hs1, ht1, ht₁, mem_subsystemGroup_range f₁ h₁,
    mem_subsystemGroup_range f₂ h₂⟩

private theorem centralizer_factor_one {F : Type} [Field F] {m₁ : ℕ}
    {S₁ S₂ S₃ : Set (Fin TwistTag.E6.tag.rank)}
    (f₁ : LeviFactor F m₁ S₁) (h12 : Disjoint S₁ S₂) (h13 : Disjoint S₁ S₃)
    (c12 : ∀ i ∈ S₁, ∀ j ∈ S₂, TwistTag.E6.tag.cartan i j = 0)
    (c13 : ∀ i ∈ S₁, ∀ j ∈ S₃, TwistTag.E6.tag.cartan i j = 0)
    (b : Fin TwistTag.E6.tag.rank → Fˣ) {s : ModGL TwistTag.E6.tag F}
    {h₁ : Matrix.SpecialLinearGroup (Fin m₁) F} {t₁ : ModGL TwistTag.E6.tag F}
    (hs1 : s = f₁.ι h₁ * t₁) (ht₁ : t₁ ∈ subsystemGroup TwistTag.E6.tag F (S₂ ∪ S₃))
    (hc₁ : rootDiagUnit TwistTag.E6.tag b * s ∈
      Subgroup.centralizer (f₁.ι.range : Set (ModGL TwistTag.E6.tag F))) :
    rootDiagUnit TwistTag.E6.tag b * f₁.ι h₁ ∈
      Subgroup.centralizer (f₁.ι.range : Set (ModGL TwistTag.E6.tag F)) := by
  have hdisj : Disjoint S₁ (S₂ ∪ S₃) := Set.disjoint_union_right.2 ⟨h12, h13⟩
  have h01 : ∀ i ∈ S₁, ∀ j ∈ S₂ ∪ S₃, TwistTag.E6.tag.cartan i j = 0 := by
    rintro i hi j (hj | hj)
    · exact c12 i hi j hj
    · exact c13 i hi j hj
  exact mul_mem_centralizer_of_mul_eq_mul hc₁
    (subsystemGroup_le_centralizer_range f₁ hdisj h01 ht₁) (by rw [hs1]; group)

private theorem centralizer_factors_two_three {F : Type} [Field F] {m₁ m₂ m₃ : ℕ}
    {S₁ S₂ S₃ : Set (Fin TwistTag.E6.tag.rank)}
    (f₁ : LeviFactor F m₁ S₁) (f₂ : LeviFactor F m₂ S₂) (f₃ : LeviFactor F m₃ S₃)
    (h12 : Disjoint S₁ S₂) (h13 : Disjoint S₁ S₃) (h23 : Disjoint S₂ S₃)
    (c12 : ∀ i ∈ S₁, ∀ j ∈ S₂, TwistTag.E6.tag.cartan i j = 0)
    (c13 : ∀ i ∈ S₁, ∀ j ∈ S₃, TwistTag.E6.tag.cartan i j = 0)
    (c23 : ∀ i ∈ S₂, ∀ j ∈ S₃, TwistTag.E6.tag.cartan i j = 0)
    (b : Fin TwistTag.E6.tag.rank → Fˣ) {s : ModGL TwistTag.E6.tag F}
    {h₁ : Matrix.SpecialLinearGroup (Fin m₁) F}
    {h₂ : Matrix.SpecialLinearGroup (Fin m₂) F} {h₃ : Matrix.SpecialLinearGroup (Fin m₃) F}
    {t₁ : ModGL TwistTag.E6.tag F}
    (hs1 : s = f₁.ι h₁ * t₁) (ht1 : t₁ = f₂.ι h₂ * f₃.ι h₃)
    (ha₁ : f₁.ι h₁ ∈ subsystemGroup TwistTag.E6.tag F S₁)
    (ha₂ : f₂.ι h₂ ∈ subsystemGroup TwistTag.E6.tag F S₂)
    (ha₃ : f₃.ι h₃ ∈ subsystemGroup TwistTag.E6.tag F S₃)
    (hc₂ : rootDiagUnit TwistTag.E6.tag b * s ∈
      Subgroup.centralizer (f₂.ι.range : Set (ModGL TwistTag.E6.tag F)))
    (hc₃ : rootDiagUnit TwistTag.E6.tag b * s ∈
      Subgroup.centralizer (f₃.ι.range : Set (ModGL TwistTag.E6.tag F))) :
    rootDiagUnit TwistTag.E6.tag b * f₂.ι h₂ ∈
        Subgroup.centralizer (f₂.ι.range : Set (ModGL TwistTag.E6.tag F)) ∧
      rootDiagUnit TwistTag.E6.tag b * f₃.ι h₃ ∈
        Subgroup.centralizer (f₃.ι.range : Set (ModGL TwistTag.E6.tag F)) := by
  have hc12 : Commute (f₁.ι h₁) (f₂.ι h₂) :=
    commute_of_cartan_eq_zero (A := S₁) (B := S₂) (K := F) h12 c12
      (f₁.ι h₁) ha₁ (f₂.ι h₂) ha₂
  have hc13 : Commute (f₁.ι h₁) (f₃.ι h₃) :=
    commute_of_cartan_eq_zero (A := S₁) (B := S₃) (K := F) h13 c13
      (f₁.ι h₁) ha₁ (f₃.ι h₃) ha₃
  have hc23 : Commute (f₂.ι h₂) (f₃.ι h₃) :=
    commute_of_cartan_eq_zero (A := S₂) (B := S₃) (K := F) h23 c23
      (f₂.ι h₂) ha₂ (f₃.ι h₃) ha₃
  refine ⟨?_, ?_⟩
  · refine mul_mem_centralizer_of_mul_eq_mul hc₂
      (Subgroup.mul_mem _ (subsystemGroup_le_centralizer_range' f₂ h12 c12 ha₁)
        (subsystemGroup_le_centralizer_range f₂ h23 c23 ha₃)) ?_
    rw [hs1, ht1]
    have e : f₁.ι h₁ * (f₂.ι h₂ * f₃.ι h₃) =
        f₂.ι h₂ * (f₁.ι h₁ * f₃.ι h₃) := by
      rw [← mul_assoc, hc12.eq, mul_assoc]
    rw [e]; group
  · refine mul_mem_centralizer_of_mul_eq_mul hc₃
      (Subgroup.mul_mem _ (subsystemGroup_le_centralizer_range' f₃ h13 c13 ha₁)
        (subsystemGroup_le_centralizer_range' f₃ h23 c23 ha₂)) ?_
    rw [hs1, ht1]
    have e : f₁.ι h₁ * (f₂.ι h₂ * f₃.ι h₃) =
        f₃.ι h₃ * (f₁.ι h₁ * f₂.ι h₂) := by
      rw [hc23.eq, ← mul_assoc, hc13.eq, mul_assoc]
    rw [e]; group

private theorem diag_eq_of_mem_centralizer {F : Type} [Field F] {m₁ m₂ m₃ : ℕ}
    {S₁ S₂ S₃ : Set (Fin TwistTag.E6.tag.rank)}
    (f₁ : LeviFactor F m₁ S₁) (f₂ : LeviFactor F m₂ S₂) (f₃ : LeviFactor F m₃ S₃)
    (b : Fin TwistTag.E6.tag.rank → Fˣ) {s : ModGL TwistTag.E6.tag F}
    {h₁ : Matrix.SpecialLinearGroup (Fin m₁) F}
    {h₂ : Matrix.SpecialLinearGroup (Fin m₂) F}
    {h₃ : Matrix.SpecialLinearGroup (Fin m₃) F} {t₁ : ModGL TwistTag.E6.tag F}
    (hs1 : s = f₁.ι h₁ * t₁) (ht1 : t₁ = f₂.ι h₂ * f₃.ι h₃)
    (hd₁ : rootDiagUnit TwistTag.E6.tag b * f₁.ι h₁ ∈
      Subgroup.centralizer (f₁.ι.range : Set (ModGL TwistTag.E6.tag F)))
    (hd₂ : rootDiagUnit TwistTag.E6.tag b * f₂.ι h₂ ∈
      Subgroup.centralizer (f₂.ι.range : Set (ModGL TwistTag.E6.tag F)))
    (hd₃ : rootDiagUnit TwistTag.E6.tag b * f₃.ι h₃ ∈
      Subgroup.centralizer (f₃.ι.range : Set (ModGL TwistTag.E6.tag F))) :
    ∃ b' : Fin TwistTag.E6.tag.rank → Fˣ,
      rootDiagUnit TwistTag.E6.tag b * s = rootDiagUnit TwistTag.E6.tag b' := by
  obtain ⟨c₁, hc₁eq⟩ := f₁.diag_mem h₁ (f₁.diag_of_mem_centralizer b hd₁)
  obtain ⟨c₂, hc₂eq⟩ := f₂.diag_mem h₂ (f₂.diag_of_mem_centralizer b hd₂)
  obtain ⟨c₃, hc₃eq⟩ := f₃.diag_mem h₃ (f₃.diag_of_mem_centralizer b hd₃)
  refine ⟨b * c₁ * c₂ * c₃, ?_⟩
  rw [hs1, ht1, ← show rootDiagUnit TwistTag.E6.tag c₁ = f₁.ι h₁ from hc₁eq,
    ← show rootDiagUnit TwistTag.E6.tag c₂ = f₂.ι h₂ from hc₂eq,
    ← show rootDiagUnit TwistTag.E6.tag c₃ = f₃.ι h₃ from hc₃eq,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  group

theorem exists_rootDiagUnit_eq_of_mem_centralizer {F : Type} [Field F] {m₁ m₂ m₃ : ℕ}
    {S₁ S₂ S₃ : Set (Fin TwistTag.E6.tag.rank)}
    (f₁ : LeviFactor F m₁ S₁) (f₂ : LeviFactor F m₂ S₂) (f₃ : LeviFactor F m₃ S₃)
    (h12 : Disjoint S₁ S₂) (h13 : Disjoint S₁ S₃) (h23 : Disjoint S₂ S₃)
    (c12 : ∀ i ∈ S₁, ∀ j ∈ S₂, TwistTag.E6.tag.cartan i j = 0)
    (c13 : ∀ i ∈ S₁, ∀ j ∈ S₃, TwistTag.E6.tag.cartan i j = 0)
    (c23 : ∀ i ∈ S₂, ∀ j ∈ S₃, TwistTag.E6.tag.cartan i j = 0)
    (b : Fin TwistTag.E6.tag.rank → Fˣ) {s : ModGL TwistTag.E6.tag F}
    (hs : s ∈ subsystemGroup TwistTag.E6.tag F (S₁ ∪ S₂ ∪ S₃))
    (hc₁ : rootDiagUnit TwistTag.E6.tag b * s ∈
      Subgroup.centralizer (f₁.ι.range : Set (ModGL TwistTag.E6.tag F)))
    (hc₂ : rootDiagUnit TwistTag.E6.tag b * s ∈
      Subgroup.centralizer (f₂.ι.range : Set (ModGL TwistTag.E6.tag F)))
    (hc₃ : rootDiagUnit TwistTag.E6.tag b * s ∈
      Subgroup.centralizer (f₃.ι.range : Set (ModGL TwistTag.E6.tag F))) :
    ∃ b' : Fin TwistTag.E6.tag.rank → Fˣ,
      rootDiagUnit TwistTag.E6.tag b * s = rootDiagUnit TwistTag.E6.tag b' ∧
        ∀ i ∈ S₁ ∪ S₂ ∪ S₃, b' i = 1 := by
  obtain ⟨h₁, h₂, h₃, t₁, hs1, ht1, ht₁, ha₁, ha₂⟩ :=
    exists_mul_factors f₁ f₂ f₃ h12 h13 h23 c12 c13 c23 hs
  have ha₃ := mem_subsystemGroup_range f₃ h₃
  obtain hd₁ := centralizer_factor_one f₁ h12 h13 c12 c13 b hs1 ht₁ hc₁
  obtain ⟨hd₂, hd₃⟩ := centralizer_factors_two_three f₁ f₂ f₃ h12 h13 h23 c12 c13 c23
    b hs1 ht1 ha₁ ha₂ ha₃ hc₂ hc₃
  obtain ⟨b', hbs⟩ := diag_eq_of_mem_centralizer f₁ f₂ f₃ b hs1 ht1 hd₁ hd₂ hd₃
  refine ⟨b', hbs, ?_⟩
  intro i hi
  rcases hi with hi | hi
  · rcases hi with hi | hi
    · exact rootDiagUnit_apply_eq_one_of_mem_centralizer f₁ hi (by rw [← hbs]; exact hc₁)
    · exact rootDiagUnit_apply_eq_one_of_mem_centralizer f₂ hi (by rw [← hbs]; exact hc₂)
  · exact rootDiagUnit_apply_eq_one_of_mem_centralizer f₃ hi (by rw [← hbs]; exact hc₃)

end CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace
