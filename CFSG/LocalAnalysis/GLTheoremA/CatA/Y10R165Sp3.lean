module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Concl
public import CFSG.LieType.Universal.Symplectic
public import CFSG.Timmesfeld.Transvection.PresSp
public import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Orbits
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Induction
public import CFSG.RankThree.GF2n.Stroth80.Anisotropic
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec36
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace SpEngine

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {B : LinearMap.BilinForm F V}

abbrev linIsometryGroup (B : LinearMap.BilinForm F V) : Subgroup (V ≃ₗ[F] V) :=
  (bilinIsometryGroup B).map
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom

theorem mem_linIsometryGroup {g : V ≃ₗ[F] V} :
    g ∈ linIsometryGroup B ↔ ∀ x y, B (g x) (g y) = B x y := by
  rw [linIsometryGroup, Subgroup.mem_map_equiv, mem_bilinIsometryGroup]
  rfl

theorem isCompl_orthogonal_of_nondegenerate (hB : B.IsAlt) {U : Submodule F V}
    (hU : (B.restrict U).Nondegenerate) : IsCompl U (B.orthogonal U) :=
  LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hU

theorem orthogonal_nondegenerate (hB : B.IsAlt) (hBn : B.Nondegenerate) {U : Submodule F V}
    (hU : (B.restrict U).Nondegenerate) :
    (B.restrict (B.orthogonal U)).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hB.isRefl,
    LinearMap.BilinForm.orthogonal_orthogonal hBn hB.isRefl]
  exact (isCompl_orthogonal_of_nondegenerate hB hU).symm

noncomputable def restrictPointwise (hB : B.IsAlt) {U : Submodule F V}
    (hU : (B.restrict U).Nondegenerate) (g : pointwiseStab (linIsometryGroup B) U) :
    bilinIsometryGroup (B.restrict (B.orthogonal U)) := by
  have hfix : ∀ u ∈ U, ((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) u = u :=
    fun u hu => mem_pointwiseStab.mp g.2 u hu
  have hfixinv : ∀ u ∈ U, (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹ u = u :=
    fun u hu => mem_pointwiseStab.mp (Subgroup.inv_mem _ g.2) u hu
  have hmem : (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹ ∈ linIsometryGroup B :=
    Subgroup.inv_mem _ g.1.2
  have hgiso := mem_linIsometryGroup.mp g.1.2
  have hginviso := mem_linIsometryGroup.mp hmem
  refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv
    (restrictEquiv (B.orthogonal U) (g : V ≃ₗ[F] V) ?_ ?_), ?_⟩
  · intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
    intro u hu
    calc B u (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) x)
        = B ((((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹ u)
            ((((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹
              (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) x)) :=
          (hginviso u (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) x)).symm
      _ = B u x := by
        rw [hfixinv u hu]
        exact congrArg (fun z => B u z) ((↑↑(g : ↥(linIsometryGroup B)) :
          V ≃ₗ[F] V).symm_apply_apply x)
      _ = 0 := hx u hu
  · intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
    intro u hu
    calc B u ((((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹ x)
        = B (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) u)
            (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V)
              ((((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹ x)) :=
          (hgiso u ((((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹ x)).symm
      _ = B u x := by
        rw [hfix u hu]
        exact congrArg (fun z => B u z) ((↑↑(g : ↥(linIsometryGroup B)) :
          V ≃ₗ[F] V).apply_symm_apply x)
      _ = 0 := hx u hu
  · rw [mem_bilinIsometryGroup]
    intro x y
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict_apply, LinearMap.domRestrict_apply]
    simp only [LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, coe_restrictEquiv]
    exact hgiso x y

private theorem coe_restrictPointwise (hB : B.IsAlt) {U : Submodule F V}
    (hU : (B.restrict U).Nondegenerate) (g : pointwiseStab (linIsometryGroup B) U)
    (x : B.orthogonal U) :
    ((restrictPointwise hB hU g :
        LinearMap.GeneralLinearGroup F (B.orthogonal U)) :
        B.orthogonal U →ₗ[F] B.orthogonal U) x = (g : V ≃ₗ[F] V) x :=
  rfl

noncomputable def gluePointwise (hB : B.IsAlt) {U : Submodule F V}
    (hU : (B.restrict U).Nondegenerate)
    (φ : bilinIsometryGroup (B.restrict (B.orthogonal U))) :
    pointwiseStab (linIsometryGroup B) U := by
  let φL : LinearMap.GeneralLinearGroup F (B.orthogonal U) := φ
  let T : V ≃ₗ[F] V := glue (isCompl_orthogonal_of_nondegenerate hB hU) 1
    (LinearMap.GeneralLinearGroup.toLinearEquiv φL)
  refine ⟨⟨T, ?_⟩, ?_⟩
  · rw [mem_linIsometryGroup]
    intro x y
    obtain ⟨xu, xr, hx⟩ := exists_coe_add_of_isCompl
      (isCompl_orthogonal_of_nondegenerate hB hU) x
    obtain ⟨yu, yr, hy⟩ := exists_coe_add_of_isCompl
      (isCompl_orthogonal_of_nondegenerate hB hU) y
    rw [← hx, ← hy]
    change B (T ((xu : V) + (xr : V))) (T ((yu : V) + (yr : V))) = B ((xu : V) + (xr : V))
      ((yu : V) + (yr : V))
    have hxT : T ((xu : V) + (xr : V)) = (xu : V) +
        ((φL : B.orthogonal U →ₗ[F] B.orthogonal U) xr : V) := by
      dsimp only [T]
      rw [glue_apply]
      simp
    have hyT : T ((yu : V) + (yr : V)) = (yu : V) +
        ((φL : B.orthogonal U →ₗ[F] B.orthogonal U) yr : V) := by
      dsimp only [T]
      rw [glue_apply]
      simp
    have hBilin : ∀ a b c d : V, B (a + b) (c + d) = B a c + B a d + B b c + B b d := by
      intro a b c d
      simp only [map_add, LinearMap.add_apply]
      abel
    have hxr : ∀ u ∈ U, B u (xr : V) = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp xr.2)
    have hyr : ∀ u ∈ U, B u (yr : V) = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp yr.2)
    have hφ := mem_bilinIsometryGroup.mp φ.2 (xr : B.orthogonal U) (yr : B.orthogonal U)
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict_apply, LinearMap.domRestrict_apply] at hφ
    have hxφ : B (xu : V) (((φL : B.orthogonal U →ₗ[F] B.orthogonal U)) yr) = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp
        ((φL : B.orthogonal U →ₗ[F] B.orthogonal U) yr).2) (xu : V) xu.2
    have hφy : B (((φL : B.orthogonal U →ₗ[F] B.orthogonal U)) xr) (yu : V) = 0 :=
      hB.isRefl.eq_zero ((LinearMap.BilinForm.mem_orthogonal_iff.mp
        ((φL : B.orthogonal U →ₗ[F] B.orthogonal U) xr).2) (yu : V) yu.2)
    have hφxy : B (((φL : B.orthogonal U →ₗ[F] B.orthogonal U)) xr)
        (((φL : B.orthogonal U →ₗ[F] B.orthogonal U)) yr) = B (xr : V) (yr : V) := hφ
    rw [hxT, hyT, hBilin, hBilin]
    have hxry : B (xr : V) (yu : V) = 0 :=
      hB.isRefl.eq_zero ((LinearMap.BilinForm.mem_orthogonal_iff.mp xr.2) (yu : V) yu.2)
    rw [hyr (xu : V) xu.2, hxφ, hφy, hxry, hφxy]
  · rw [mem_pointwiseStab]
    intro u hu
    have hglue := glue_apply (isCompl_orthogonal_of_nondegenerate hB hU) (1 : U ≃ₗ[F] U)
      (LinearMap.GeneralLinearGroup.toLinearEquiv φL) (⟨u, hu⟩ : U) (0 : B.orthogonal U)
    rw [show u = ((⟨u, hu⟩ : U) : V) + ((0 : B.orthogonal U) : V) by simp]
    dsimp only [T]
    rw [hglue]
    simp

theorem gluePointwise_apply (hB : B.IsAlt) {U : Submodule F V}
    (hU : (B.restrict U).Nondegenerate)
    (φ : bilinIsometryGroup (B.restrict (B.orthogonal U))) (x : U) (y : B.orthogonal U) :
    ((gluePointwise hB hU φ : V ≃ₗ[F] V) ((x : V) + (y : V))) =
      (x : V) + ((φ : LinearMap.GeneralLinearGroup F (B.orthogonal U)) : B.orthogonal U →ₗ[F]
        B.orthogonal U) y := by
  change ((glue (isCompl_orthogonal_of_nondegenerate hB hU) 1
    (LinearMap.GeneralLinearGroup.toLinearEquiv
      (φ : LinearMap.GeneralLinearGroup F (B.orthogonal U)))) : V ≃ₗ[F] V)
    ((x : V) + (y : V)) = _
  rw [glue_apply]
  simp

noncomputable def pointwiseStabEquiv (hB : B.IsAlt) {U : Submodule F V}
    (hU : (B.restrict U).Nondegenerate) :
    pointwiseStab (linIsometryGroup B) U ≃* bilinIsometryGroup (B.restrict (B.orthogonal U)) where
  toFun := restrictPointwise hB hU
  invFun := gluePointwise hB hU
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨u, r, hu⟩ := exists_coe_add_of_isCompl
      (isCompl_orthogonal_of_nondegenerate hB hU) v
    rw [← hu, gluePointwise_apply, map_add, mem_pointwiseStab.mp g.2 (u : V) u.2]
    rfl
  right_inv φ := by
    apply Subtype.ext
    apply Units.ext
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    rw [coe_restrictPointwise]
    rw [show ((x : B.orthogonal U) : V) = ((0 : U) : V) + (x : V) by simp,
      gluePointwise_apply]
    simpa using zero_add ((φ : LinearMap.GeneralLinearGroup F (B.orthogonal U)) x : V)
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    refine LinearMap.ext fun x => ?_
    rfl

private theorem pointwiseStabEquiv_apply_coe (hB : B.IsAlt) {U : Submodule F V}
    (hU : (B.restrict U).Nondegenerate) (g : pointwiseStab (linIsometryGroup B) U)
    (x : B.orthogonal U) :
    ((pointwiseStabEquiv hB hU g :
        LinearMap.GeneralLinearGroup F (B.orthogonal U)) :
        B.orthogonal U →ₗ[F] B.orthogonal U) x = (g : V ≃ₗ[F] V) x :=
  rfl

theorem isQuasisimple_pointwiseStab (hB : B.IsAlt) (hBn : B.Nondegenerate) {U : Submodule F V}
    (hU : (B.restrict U).Nondegenerate) (h2 : 2 ≤ Module.finrank F (B.orthogonal U))
    (hK : 4 ≤ Nat.card F ∨ (Nat.card F = 3 ∧ 4 ≤ Module.finrank F (B.orthogonal U)) ∨
      (Nat.card F = 2 ∧ 6 ≤ Module.finrank F (B.orthogonal U))) :
    CFSG.IsQuasisimple ↥(pointwiseStab (linIsometryGroup B) U) := by
  have halt : (B.restrict (B.orthogonal U)).IsAlt := fun z => hB.self_eq_zero z
  have hnd := orthogonal_nondegenerate hB hBn hU
  have hq : CFSG.IsQuasisimple ↥(bilinIsometryGroup (B.restrict (B.orthogonal U))) := by
    exact CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt halt hnd h2 hK
  exact CFSG.IsQuasisimple.of_mulEquiv (pointwiseStabEquiv hB hU) hq

end SpEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
