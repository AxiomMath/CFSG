module

public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.Models CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_polar_isSimilitude_neg {ρ : V ≃ₗ[ZMod 3] V}
    (hρ : IsSimilitude Q ρ (-1)) (x y : V) :
    Q.polarBilin (ρ x) (ρ y) = (-1) * Q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [← ρ.map_add, hρ, hρ, hρ]
  simp only [Units.val_neg, Units.val_one, neg_mul, neg_neg]
  ring


@[simp] theorem ff_mem_orthogonalOperatorCentralizer_iff
    (T : Module.End (ZMod 3) V) (g : OGroup Q) :
    g ∈ orthogonalOperatorCentralizer Q T ↔
      ∀ x, (g : V ≃ₗ[ZMod 3] V) (T x) = T ((g : V ≃ₗ[ZMod 3] V) x) := by
  rw [orthogonalOperatorCentralizer, Subgroup.mem_comap]
  rfl

theorem ff_fixSub_simAct_eq_orthogonalOperatorCentralizer (ρ : ↥(simGroup Q)) :
    fixSub (simAct Q ρ) = orthogonalOperatorCentralizer Q (ρ : V ≃ₗ[ZMod 3] V).toLinearMap := by
  ext g
  constructor
  · intro hg x
    have h := congrArg (fun f : OGroup Q => (f : V ≃ₗ[ZMod 3] V)) hg
    rw [coe_simAct] at h
    have hx := congrArg (fun f : V ≃ₗ[ZMod 3] V => f ((ρ : V ≃ₗ[ZMod 3] V) x)) h
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply] at hx
    exact hx.symm
  · intro hg
    have hg' : ∀ y, (g : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) y) =
        (ρ : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) y) := by
      rw [ff_mem_orthogonalOperatorCentralizer_iff] at hg
      intro y
      simpa using hg y
    apply Subtype.ext
    rw [coe_simAct]
    apply LinearEquiv.ext
    intro x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
    have h1 : (g : V ≃ₗ[ZMod 3] V) x = (ρ : V ≃ₗ[ZMod 3] V)
        ((g : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V).symm x)) := by
      simpa using hg' ((ρ : V ≃ₗ[ZMod 3] V).symm x)
    exact h1.symm

theorem ff_specialLinear_perfect (W : Type) [AddCommGroup W] [Module (ZMod 3) W]
    [FiniteDimensional (ZMod 3) W] (hW : Module.finrank (ZMod 3) W = 3) :
    Group.IsPerfect (SpecialLinearGroup (ZMod 3) W) := by
  let b : Module.Basis (Fin 3) (ZMod 3) W := Module.finBasisOfFinrankEq (R := ZMod 3)
    (M := W) hW
  have hperfect : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := ZMod 3) (n := 3)
      (by norm_num)
  exact Group.IsPerfect.ofSurjective
    (f := (Matrix.SpecialLinearGroup.toLin_equiv (R := ZMod 3) (V := W) b).toMonoidHom)
    (fun x => ⟨(Matrix.SpecialLinearGroup.toLin_equiv (R := ZMod 3) (V := W) b).symm x,
      (Matrix.SpecialLinearGroup.toLin_equiv (R := ZMod 3) (V := W) b).apply_symm_apply x⟩)

theorem ff_center_specialLinear_fin_three_zmod_three :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr1 : r = 1 := by
    have h3 : r ^ 3 = 1 := by simpa using hr
    have hall : ∀ s : ZMod 3, s ^ 3 = 1 → s = 1 := by decide
    exact hall r h3
  apply Subtype.ext
  rw [← hA', hr1]
  ext i j
  simp [Matrix.scalar_apply, Pi.single_apply]

theorem ff_K4III_C_layerModel (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = v) :
    LayerModel ↥(omegaGroup hQ ⊓ fixSub (simAct Q ρ)) .PSL 3 1 := by
  rw [ff_fixSub_simAct_eq_orthogonalOperatorCentralizer ρ]
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hsquare : ∀ x : V, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) x) = (1 : ZMod 3) • x := by
    intro x; rw [hρρ x, one_smul]
  have hroot : (1 : ZMod 3) = 1 ^ 2 := by norm_num
  have hsim := ff_polar_isSimilitude_neg (Q := Q) hρ
  have hneg : (-1 : ZMod 3) / 1 = -1 := by norm_num
  have hQp : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  let e : orthogonalOperatorCentralizer Q (ρ : V ≃ₗ[ZMod 3] V).toLinearMap ≃*
      (positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1 ≃ₗ[ZMod 3]
        positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1) :=
    negativeSquareKernelCentralizerEquiv Q hQp (ρ : V ≃ₗ[ZMod 3] V) 1 (-1) 1
      one_ne_zero one_ne_zero h2 hsquare hroot hsim hneg
  have hfin : Module.finrank (ZMod 3) (positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1) = 3 := by
    have hgeo := negative_square_kernel_geometry Q hQp (ρ : V ≃ₗ[ZMod 3] V) 1 (-1) 1
      one_ne_zero one_ne_zero h2 hsquare hroot hsim hneg
    obtain ⟨-, -, -, -, h, -⟩ := hgeo
    rw [h, hdim]
  let b : Module.Basis (Fin 3) (ZMod 3) (positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1) :=
    Module.finBasisOfFinrankEq (R := ZMod 3) (M := _) hfin
  let SLsub : Subgroup (positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1 ≃ₗ[ZMod 3]
      positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1) :=
    (SpecialLinearGroup.toLinearEquiv (R := ZMod 3) (V :=
      positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1)).range
  have eSL : SpecialLinearGroup (ZMod 3) (positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1) ≃* SLsub :=
    MonoidHom.ofInjective (f := SpecialLinearGroup.toLinearEquiv (R := ZMod 3) (V :=
      positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1))
      SpecialLinearGroup.toLinearEquiv_injective
  have hperfect_SL : Group.IsPerfect SLsub := by
    haveI : Group.IsPerfect (SpecialLinearGroup (ZMod 3)
        (positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1)) := ff_specialLinear_perfect _ hfin
    exact Group.IsPerfect.ofSurjective (f := eSL.toMonoidHom)
      (fun x => ⟨eSL.symm x, eSL.apply_symm_apply x⟩)
  let D : Subgroup (OGroup Q) :=
    orthogonalOperatorCentralizer Q (ρ : V ≃ₗ[ZMod 3] V).toLinearMap
  let Ebig : Subgroup ↥D := SLsub.comap e.toMonoidHom
  have hmapE : Ebig.map e.toMonoidHom = SLsub :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective SLsub
  haveI : Group.IsPerfect ↥Ebig := by
    have h1 : ↥Ebig ≃* ↥SLsub := (e.subgroupMap Ebig).trans (MulEquiv.subgroupCongr hmapE)
    exact Group.IsPerfect.ofSurjective (f := (h1.symm : ↥SLsub →* ↥Ebig)) h1.symm.surjective
  let E : Subgroup (OGroup Q) := Ebig.map D.subtype
  let C : Subgroup (OGroup Q) := omegaGroup hQ ⊓ D
  have hE_le_C : E ≤ C := by
    haveI : Group.IsPerfect ↥E := Group.IsPerfect.ofSurjective
      (f := (Subgroup.equivMapOfInjective Ebig D.subtype D.subtype_injective).toMonoidHom)
      (fun x => ⟨(Subgroup.equivMapOfInjective Ebig D.subtype D.subtype_injective).symm x,
        (Subgroup.equivMapOfInjective Ebig D.subtype D.subtype_injective).apply_symm_apply x⟩)
    have hE_omega : E ≤ omegaGroup hQ := by
      calc E = ⁅E, E⁆ := (Subgroup.commutator_eq_self).symm
        _ ≤ commutator (OGroup Q) := Subgroup.commutator_mono le_top le_top
        _ ≤ omegaGroup hQ := commutator_le_omegaGroup hQ
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨hE_omega (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩), y.2⟩
  let χ : ↥D →* (ZMod 3)ˣ := (LinearEquiv.det (R := ZMod 3) (M :=
      positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1)).comp e.toMonoidHom
  have hSLsub : SLsub = (LinearEquiv.det (R := ZMod 3) (M :=
      positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1)).ker := by
    change (SpecialLinearGroup.toLinearEquiv (R := ZMod 3) (V :=
      positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1)).range = _
    ext f
    constructor
    · rintro ⟨A, rfl⟩
      exact SpecialLinearGroup.det_coe A
    · intro hf
      exact ⟨⟨f, hf⟩, rfl⟩
  have hχ : Ebig = χ.ker := by
    ext x
    simp only [Ebig, χ, Subgroup.mem_comap, hSLsub, MonoidHom.mem_ker,
      MonoidHom.comp_apply]
  let φ : ↥C →* (ZMod 3)ˣ := χ.comp (Subgroup.inclusion (inf_le_right : C ≤ D))
  have hE'eq : (φ.ker).map C.subtype = E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change φ y = 1 at hy
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion (inf_le_right : C ≤ D) y, by
        rw [hχ, MonoidHom.mem_ker]
        simpa [φ, MonoidHom.comp_apply] using hy, rfl⟩
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
      refine ⟨⟨D.subtype z, hE_le_C (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)⟩, ?_, rfl⟩
      change φ ⟨D.subtype z, hE_le_C (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)⟩ = 1
      rw [hχ, MonoidHom.mem_ker] at hz
      simpa [φ, χ, MonoidHom.comp_apply, Subgroup.inclusion] using hz
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = ⊥ :=
    ff_center_specialLinear_fin_three_zmod_three
  let ePSL : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3) :=
    (QuotientGroup.quotientBot (G := Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hcenter).symm
  have hiso : ↥(φ.ker) ≃* StatedProj (StatedSL 3 (ZMod 3)) :=
    (Subgroup.equivMapOfInjective (φ.ker) C.subtype C.subtype_injective).trans
      ((MulEquiv.subgroupCongr hE'eq).trans
        (((Subgroup.equivMapOfInjective Ebig D.subtype D.subtype_injective).symm).trans
          ((e.subgroupMap Ebig).trans
            ((MulEquiv.subgroupCongr hmapE).trans
              (eSL.symm.trans
                ((Matrix.SpecialLinearGroup.toLin_equiv (R := ZMod 3) (V := _) b).symm.trans
                  (ePSL.trans
                    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
                      3 (ZMod 3)))))))))
  have hadm : StatedLieAdmissible .PSL 3 3 1 := by
    unfold StatedLieAdmissible
    norm_num
  have hcard : Nat.card (ZMod 3) = 3 ^ 1 := by rw [Nat.card_zmod]; norm_num
  have hmodel : CFSG.Blueprint.LieModel (↥(φ.ker)) (StatedLieTag.PSL) 3 3 1 :=
    Or.inl ⟨by decide, ⟨hadm, ZMod 3, inferInstance, inferInstance, hcard, ⟨hiso⟩⟩⟩
  have hP : IsPGroup 2 (↥C ⧸ φ.ker) := by
    have hUnits : IsPGroup 2 ((ZMod 3)ˣ) :=
      IsPGroup.of_card (p := 2) (G := (ZMod 3)ˣ) (n := 1) (by
        rw [Nat.card_units, Nat.card_zmod]; norm_num)
    have hRange : IsPGroup 2 ↥φ.range :=
      IsPGroup.of_injective (p := 2) hUnits (Subgroup.subtype φ.range)
        Subtype.coe_injective
    exact IsPGroup.of_equiv (p := 2) hRange (QuotientGroup.quotientKerEquivRange φ).symm
  exact ⟨φ.ker, MonoidHom.normal_ker φ, hmodel, hP⟩

end CFSG.OddStandard.SmallF3.Omega
