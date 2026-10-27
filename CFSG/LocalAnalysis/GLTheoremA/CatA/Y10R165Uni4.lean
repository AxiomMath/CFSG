module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni3
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockQuasisimple

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.LieType.SeitzGeneration HyperBlocks CFSG.Open
open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv
  coe_restrictEquiv exists_coe_add_of_isCompl)
open CFSG.LocalAnalysis.ComponentInitial
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable {σ : F →+* F} {B : V →ₛₗ[σ] V →ₗ[F] F}

def sesqSpecialUnitaryGroupLE (B : V →ₛₗ[σ] V →ₗ[F] F) : Subgroup (V ≃ₗ[F] V) :=
  (sesqSpecialUnitaryGroup B).map
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom

theorem mem_sesqSpecialUnitaryGroupLE {g : V ≃ₗ[F] V} :
    g ∈ sesqSpecialUnitaryGroupLE B ↔
      (∀ x y, B (g x) (g y) = B x y) ∧ LinearMap.det (g : V →ₗ[F] V) = 1 := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact (mem_sesqSpecialUnitaryGroup (B := B)).mp hg'
  · rintro ⟨hiso, hdet⟩
    refine Subgroup.mem_map.mpr ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv g, ?_, ?_⟩
    · exact (mem_sesqSpecialUnitaryGroup (B := B)).mpr ⟨hiso, hdet⟩
    · exact LinearEquiv.ext fun x => rfl

theorem sesqSpecialUnitaryGroupLE_mulEquiv :
    Nonempty (↥(sesqSpecialUnitaryGroupLE B) ≃* ↥(sesqSpecialUnitaryGroup B)) :=
  ⟨(Subgroup.equivMapOfInjective (sesqSpecialUnitaryGroup B)
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).injective).symm⟩

section Restriction

variable [FiniteDimensional F V] {U : Submodule F V}

private theorem mem_orthogonal_of_mem_orthogonal_map {g : V ≃ₗ[F] V}
    (hgU : ∀ u ∈ U, g u = u) (hgB : ∀ x y, B (g x) (g y) = B x y) {w : V}
    (hw : w ∈ Submodule.orthogonalBilin B U) :
    g w ∈ Submodule.orthogonalBilin B U := by
  rw [Submodule.mem_orthogonalBilin] at hw ⊢
  intro n hn
  have h1 : B (g n) (g w) = B n w := hgB n w
  rw [hgU n hn, hw n hn] at h1
  exact h1

private theorem symm_fixes {g : V ≃ₗ[F] V} (hgU : ∀ u ∈ U, g u = u) :
    ∀ u ∈ U, g.symm u = u := by
  intro u hu
  calc g.symm u = g.symm (g u) := by rw [hgU u hu]
    _ = u := g.symm_apply_apply u

private theorem symm_isometry {g : V ≃ₗ[F] V} (hgB : ∀ x y, B (g x) (g y) = B x y) :
    ∀ x y, B (g.symm x) (g.symm y) = B x y := by
  intro x y
  have h1 := hgB (g.symm x) (g.symm y)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
  exact h1.symm

private theorem glue_restrictEquiv_eq {W : Submodule F V} (hc : IsCompl U W)
    {g : V ≃ₗ[F] V} (hU1 : ∀ u ∈ U, g u ∈ U) (hU2 : ∀ u ∈ U, g.symm u ∈ U)
    (hW1 : ∀ w ∈ W, g w ∈ W) (hW2 : ∀ w ∈ W, g.symm w ∈ W) :
    glue hc (restrictEquiv U g hU1 hU2) (restrictEquiv W g hW1 hW2) = g := by
  ext v
  obtain ⟨u, r, rfl⟩ := exists_coe_add_of_isCompl hc v
  rw [glue_apply, coe_restrictEquiv, coe_restrictEquiv, map_add]

private noncomputable def restrictToComplement
    (g : ↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) U)) :
    Submodule.orthogonalBilin B U ≃ₗ[F] Submodule.orthogonalBilin B U :=
  restrictEquiv _ (((g : ↥(sesqSpecialUnitaryGroupLE B)) : V ≃ₗ[F] V))
    (fun w hw => mem_orthogonal_of_mem_orthogonal_map (mem_pointwiseStab.mp g.2)
      ((mem_sesqSpecialUnitaryGroupLE.mp
        (g : ↥(sesqSpecialUnitaryGroupLE B)).2).1) hw)
    (fun w hw => mem_orthogonal_of_mem_orthogonal_map (symm_fixes (mem_pointwiseStab.mp g.2))
      (symm_isometry ((mem_sesqSpecialUnitaryGroupLE.mp
        (g : ↥(sesqSpecialUnitaryGroupLE B)).2).1)) hw)

private theorem restrictToComplement_isometry
    (g : ↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) U)) (x y :
      Submodule.orthogonalBilin B U) :
    B (restrictToComplement g x) (restrictToComplement g y) = B x y := by
  rw [← (mem_sesqSpecialUnitaryGroupLE.mp (g : ↥(sesqSpecialUnitaryGroupLE B)).2).1
    (x : V) (y : V)]
  simp only [restrictToComplement, coe_restrictEquiv]

private theorem det_glue {W : Submodule F V} (hc : IsCompl U W) (a : U ≃ₗ[F] U)
    (b : W ≃ₗ[F] W) :
    LinearMap.det (glue hc a b : V →ₗ[F] V) =
      LinearMap.det (a : U →ₗ[F] U) * LinearMap.det (b : W →ₗ[F] W) := by
  have h2 : LinearMap.det (glue hc a b : V →ₗ[F] V) =
      LinearMap.det (LinearMap.prodMap (a : U →ₗ[F] U) (b : W →ₗ[F] W)) :=
    LinearMap.det_conj (LinearMap.prodMap (a : U →ₗ[F] U) (b : W →ₗ[F] W))
      (Submodule.prodEquivOfIsCompl U W hc)
  rw [h2, LinearMap.det_prodMap]

private theorem det_restrictToComplement
    (hc : IsCompl U (Submodule.orthogonalBilin B U))
    (g : ↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) U)) :
    LinearMap.det ((restrictToComplement g : Submodule.orthogonalBilin B U ≃ₗ[F]
      Submodule.orthogonalBilin B U) : Submodule.orthogonalBilin B U →ₗ[F]
        Submodule.orthogonalBilin B U) = 1 := by
  set G : V ≃ₗ[F] V := ((g : ↥(sesqSpecialUnitaryGroupLE B)) : V ≃ₗ[F] V) with hG
  have hgU : ∀ u ∈ U, G u = u := mem_pointwiseStab.mp g.2
  have hgB : ∀ x y, B (G x) (G y) = B x y :=
    (mem_sesqSpecialUnitaryGroupLE.mp (g : ↥(sesqSpecialUnitaryGroupLE B)).2).1
  have hdetG : LinearMap.det (G : V →ₗ[F] V) = 1 :=
    (mem_sesqSpecialUnitaryGroupLE.mp (g : ↥(sesqSpecialUnitaryGroupLE B)).2).2
  have hU1 : ∀ u ∈ U, G u ∈ U := fun u hu => by rw [hgU u hu]; exact hu
  have hU2 : ∀ u ∈ U, G.symm u ∈ U := fun u hu => by rw [symm_fixes hgU u hu]; exact hu
  have hW1 : ∀ w ∈ Submodule.orthogonalBilin B U, G w ∈ Submodule.orthogonalBilin B U :=
    fun w hw => mem_orthogonal_of_mem_orthogonal_map hgU hgB hw
  have hW2 : ∀ w ∈ Submodule.orthogonalBilin B U,
      G.symm w ∈ Submodule.orthogonalBilin B U :=
    fun w hw => mem_orthogonal_of_mem_orthogonal_map (symm_fixes hgU) (symm_isometry hgB) hw
  have hUid : restrictEquiv U G hU1 hU2 = 1 := by
    refine LinearEquiv.ext fun u => Subtype.ext ?_
    rw [coe_restrictEquiv]
    exact hgU u u.2
  have hcomp : restrictToComplement g =
      restrictEquiv (Submodule.orthogonalBilin B U) G hW1 hW2 := rfl
  have hglue : glue hc (restrictEquiv U G hU1 hU2)
      (restrictEquiv (Submodule.orthogonalBilin B U) G hW1 hW2) = G :=
    glue_restrictEquiv_eq hc hU1 hU2 hW1 hW2
  have hdetglue : LinearMap.det (G : V →ₗ[F] V) =
      LinearMap.det (restrictEquiv (Submodule.orthogonalBilin B U) G hW1 hW2 :
        Submodule.orthogonalBilin B U →ₗ[F] Submodule.orthogonalBilin B U) := by
    conv_lhs => rw [← hglue]
    rw [det_glue, hUid]
    simp
  rw [hcomp, ← hdetglue, hdetG]

private theorem glue_one_isometry (hrefl : B.IsRefl)
    (hc : IsCompl U (Submodule.orthogonalBilin B U))
    {h : Submodule.orthogonalBilin B U ≃ₗ[F] Submodule.orthogonalBilin B U}
    (hh : ∀ x y, B (h x) (h y) = B x y) :
    ∀ x y, B (glue hc 1 h x) (glue hc 1 h y) = B x y := by
  intro x y
  obtain ⟨u₁, w₁, rfl⟩ := exists_coe_add_of_isCompl hc x
  obtain ⟨u₂, w₂, rfl⟩ := exists_coe_add_of_isCompl hc y
  have h1 : B u₁ ((h w₂ : V)) = 0 := (Submodule.mem_orthogonalBilin.mp (h w₂).2) u₁ u₁.2
  have h2 : B ((h w₁ : V)) u₂ = 0 := hrefl.eq_zero ((Submodule.mem_orthogonalBilin.mp
    (h w₁).2) u₂ u₂.2)
  have h3 : B u₁ (w₂ : V) = 0 := (Submodule.mem_orthogonalBilin.mp w₂.2) u₁ u₁.2
  have h4 : B (w₁ : V) u₂ = 0 := hrefl.eq_zero ((Submodule.mem_orthogonalBilin.mp w₁.2)
    u₂ u₂.2)
  have e1 : ((1 : U ≃ₗ[F] U) u₁ : V) = (u₁ : V) := rfl
  have e2 : ((1 : U ≃ₗ[F] U) u₂ : V) = (u₂ : V) := rfl
  rw [glue_apply, glue_apply, e1, e2]
  simp only [map_add, LinearMap.add_apply, h1, h2, h3, h4, hh w₁ w₂, add_zero, zero_add]

private theorem glue_one_fixes (hc : IsCompl U (Submodule.orthogonalBilin B U))
    {h : Submodule.orthogonalBilin B U ≃ₗ[F] Submodule.orthogonalBilin B U} :
    ∀ u ∈ U, glue hc 1 h u = u := by
  intro u hu
  have h1 : ((⟨u, hu⟩ : U) : V) + ((0 : Submodule.orthogonalBilin B U) : V) = u := by simp
  rw [← h1, glue_apply]
  simp

private noncomputable def glueOfUnitary (hrefl : B.IsRefl)
    (hc : IsCompl U (Submodule.orthogonalBilin B U))
    (h : ↥(sesqSpecialUnitaryGroupLE (B.domRestrict₁₂ (Submodule.orthogonalBilin B U)
      (Submodule.orthogonalBilin B U)))) :
    ↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) U) :=
  ⟨⟨glue hc 1 (h : Submodule.orthogonalBilin B U ≃ₗ[F] Submodule.orthogonalBilin B U),
    (mem_sesqSpecialUnitaryGroupLE.mpr ⟨
      glue_one_isometry hrefl hc (mem_sesqSpecialUnitaryGroupLE.mp h.2).1,
      by
        rw [det_glue]
        simp [(mem_sesqSpecialUnitaryGroupLE.mp h.2).2]⟩)⟩,
    mem_pointwiseStab.mpr (glue_one_fixes hc)⟩

private noncomputable def restrictToUnitary (hc : IsCompl U (Submodule.orthogonalBilin B U))
    (g : ↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) U)) :
    ↥(sesqSpecialUnitaryGroupLE (B.domRestrict₁₂ (Submodule.orthogonalBilin B U)
      (Submodule.orthogonalBilin B U))) :=
  ⟨restrictToComplement g, mem_sesqSpecialUnitaryGroupLE.mpr
    ⟨restrictToComplement_isometry g, det_restrictToComplement hc g⟩⟩

private theorem restrictToComplement_glueOfUnitary (hrefl : B.IsRefl)
    (hc : IsCompl U (Submodule.orthogonalBilin B U))
    (h : ↥(sesqSpecialUnitaryGroupLE (B.domRestrict₁₂ (Submodule.orthogonalBilin B U)
      (Submodule.orthogonalBilin B U)))) :
    restrictToComplement (glueOfUnitary hrefl hc h) = h := by
  ext w
  have hglue : glue hc 1 (h : Submodule.orthogonalBilin B U ≃ₗ[F]
      Submodule.orthogonalBilin B U) (w : V) = ((h : Submodule.orthogonalBilin B U ≃ₗ[F]
        Submodule.orthogonalBilin B U) w : V) := by
    have hw0 : (((0 : U) : V) + (w : V)) = (w : V) := by simp
    conv_lhs => rw [← hw0]
    rw [glue_apply]
    simp
  simpa only [restrictToComplement, glueOfUnitary, coe_restrictEquiv] using hglue

private theorem glueOfUnitary_restrictToComplement (hrefl : B.IsRefl)
    (hc : IsCompl U (Submodule.orthogonalBilin B U))
    (g : ↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) U)) :
    glueOfUnitary hrefl hc (restrictToUnitary hc g) = g := by
  have hgU : ∀ u ∈ U, ((g : ↥(sesqSpecialUnitaryGroupLE B)) : V ≃ₗ[F] V) u = u :=
    mem_pointwiseStab.mp g.2
  refine Subtype.ext ?_
  refine Subtype.ext ?_
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, w, rfl⟩ := exists_coe_add_of_isCompl hc v
  show glue hc 1 ((restrictToUnitary hc g : ↥(sesqSpecialUnitaryGroupLE (B.domRestrict₁₂
      (Submodule.orthogonalBilin B U) (Submodule.orthogonalBilin B U)))) :
        Submodule.orthogonalBilin B U ≃ₗ[F] Submodule.orthogonalBilin B U)
      ((u : V) + (w : V)) = ((g : ↥(sesqSpecialUnitaryGroupLE B)) : V ≃ₗ[F] V)
      ((u : V) + (w : V))
  rw [glue_apply, map_add]
  simp only [restrictToUnitary, restrictToComplement, coe_restrictEquiv, hgU u u.2]
  rfl

private noncomputable def pointwiseStabRestrictHom
    (hc : IsCompl U (Submodule.orthogonalBilin B U)) :
    ↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) U) →*
      ↥(sesqSpecialUnitaryGroupLE (B.domRestrict₁₂ (Submodule.orthogonalBilin B U)
        (Submodule.orthogonalBilin B U))) where
  toFun g := restrictToUnitary hc g
  map_one' := by
    refine Subtype.ext ?_
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rfl
  map_mul' g g' := by
    refine Subtype.ext ?_
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rfl

theorem pointwiseStab_sesqSpecialUnitaryGroup_mulEquiv (hrefl : B.IsRefl)
    (hc : IsCompl U (Submodule.orthogonalBilin B U)) :
    Nonempty (↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) U) ≃*
      ↥(sesqSpecialUnitaryGroupLE (B.domRestrict₁₂ (Submodule.orthogonalBilin B U)
        (Submodule.orthogonalBilin B U)))) := by
  refine ⟨MulEquiv.ofBijective (pointwiseStabRestrictHom hc) ⟨?_, ?_⟩⟩
  · intro g g' hgg'
    have h1 : restrictToUnitary hc g = restrictToUnitary hc g' :=
      Subtype.ext (congrArg Subtype.val hgg')
    calc g = glueOfUnitary hrefl hc (restrictToUnitary hc g) :=
        (glueOfUnitary_restrictToComplement hrefl hc g).symm
      _ = glueOfUnitary hrefl hc (restrictToUnitary hc g') := by rw [h1]
      _ = g' := glueOfUnitary_restrictToComplement hrefl hc g'
  · intro h
    exact ⟨glueOfUnitary hrefl hc h, Subtype.ext (restrictToComplement_glueOfUnitary hrefl hc h)⟩

end Restriction

section Blocks

variable [FiniteDimensional F V]
variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ}

theorem pointwiseStab_blockSpace_mulEquiv (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (hB : InvariantSesq A B) (hrefl : B.IsRefl)
    (hBn : B.SeparatingLeft) (D : Hyperplane A p) :
    Nonempty (↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) (blockSpace A D.1)) ≃*
      ↥(sesqSpecialUnitaryGroupLE (B.domRestrict₁₂
        (Submodule.orthogonalBilin B (blockSpace A D.1))
        (Submodule.orthogonalBilin B (blockSpace A D.1))))) :=
  pointwiseStab_sesqSpecialUnitaryGroup_mulEquiv hrefl
    (isCompl_blockSpace_orthogonalBilin A hp hpF hA hB hrefl hBn D)

end Blocks

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
