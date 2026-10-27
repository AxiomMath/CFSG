module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IIIAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareNegative
open CFSG.Models CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_K4III_C_lieModel (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = v) :
    CFSG.Blueprint.LieModel ↥(omegaGroup hQ ⊓ fixSub (simAct Q ρ)) .PSL 3 3 1 := by
  rw [ff_fixSub_simAct_eq_orthogonalOperatorCentralizer ρ]
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hsq0 : ∀ x : V, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) x) = (1 : ZMod 3) • x := by
    intro x; rw [hρρ x, one_smul]
  have hroot : (1 : ZMod 3) = 1 ^ 2 := by norm_num
  have hsim := ff_polar_isSimilitude_neg (Q := Q) hρ
  have hne : (-1 : ZMod 3) / 1 = -1 := by norm_num
  have hQp : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  let T : Module.End (ZMod 3) V := (ρ : V ≃ₗ[ZMod 3] V).toLinearMap
  have hsquare_end : T * T = (1 : ZMod 3) ^ 2 • (1 : Module.End (ZMod 3) V) :=
    square_endomorphism_relation (ρ : V ≃ₗ[ZMod 3] V) 1 1 hsq0 hroot
  have hadj : ∀ x y : V, Q.polarBilin (T x) y = -Q.polarBilin x (T y) :=
    negative_square_adjoint Q (ρ : V ≃ₗ[ZMod 3] V) 1 (-1) one_ne_zero hsq0 hsim hne
  let e : orthogonalOperatorCentralizer Q T ≃*
      (T.eigenspace 1 ≃ₗ[ZMod 3] T.eigenspace 1) :=
    negativeCentralizerEquiv Q hQp T 1 one_ne_zero h2 hsquare_end hadj
  have hfin : Module.finrank (ZMod 3) (T.eigenspace 1) = 3 := by
    have hgeo := negative_square_kernel_geometry Q hQp (ρ : V ≃ₗ[ZMod 3] V) 1 (-1) 1
      one_ne_zero one_ne_zero h2 hsq0 hroot hsim hne
    obtain ⟨-, -, -, -, h, -⟩ := hgeo
    rw [← positiveSquareKernel_eq (ρ : V ≃ₗ[ZMod 3] V) 1 one_ne_zero, h, hdim]
  let b : Module.Basis (Fin 3) (ZMod 3) (T.eigenspace 1) :=
    Module.finBasisOfFinrankEq (R := ZMod 3) (M := _) hfin
  let SLsub : Subgroup (T.eigenspace 1 ≃ₗ[ZMod 3] T.eigenspace 1) :=
    (SpecialLinearGroup.toLinearEquiv (R := ZMod 3) (V := T.eigenspace 1)).range
  have hSLsub : SLsub = (LinearEquiv.det (R := ZMod 3) (M := T.eigenspace 1)).ker := by
    change (SpecialLinearGroup.toLinearEquiv (R := ZMod 3) (V := T.eigenspace 1)).range = _
    ext f
    constructor
    · rintro ⟨A, rfl⟩
      exact SpecialLinearGroup.det_coe A
    · intro hf
      exact ⟨⟨f, hf⟩, rfl⟩
  have eSL : SpecialLinearGroup (ZMod 3) (T.eigenspace 1) ≃* SLsub :=
    MonoidHom.ofInjective (f := SpecialLinearGroup.toLinearEquiv (R := ZMod 3)
      (V := T.eigenspace 1)) SpecialLinearGroup.toLinearEquiv_injective
  have hperfect_SL : Group.IsPerfect SLsub := by
    haveI : Group.IsPerfect (SpecialLinearGroup (ZMod 3) (T.eigenspace 1)) :=
      ff_specialLinear_perfect _ hfin
    exact Group.IsPerfect.ofSurjective (f := eSL.toMonoidHom)
      (fun x => ⟨eSL.symm x, eSL.apply_symm_apply x⟩)
  let D : Subgroup (OGroup Q) := orthogonalOperatorCentralizer Q T
  let Ebig : Subgroup ↥D := SLsub.comap e.toMonoidHom
  have hmapE : Ebig.map e.toMonoidHom = SLsub :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective SLsub
  haveI : Group.IsPerfect ↥Ebig := by
    have h1 : ↥Ebig ≃* ↥SLsub := (e.subgroupMap Ebig).trans (MulEquiv.subgroupCongr hmapE)
    exact Group.IsPerfect.ofSurjective (f := (h1.symm : ↥SLsub →* ↥Ebig)) h1.symm.surjective
  let E : Subgroup (OGroup Q) := Ebig.map D.subtype
  have hE_le_C : E ≤ omegaGroup hQ ⊓ D := by
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
  have hpiD : piOrth Q ∈ D := by
    rw [ff_mem_orthogonalOperatorCentralizer_iff]
    intro x
    rw [coe_piOrth_apply, coe_piOrth_apply, map_neg]
  let piD : ↥D := ⟨piOrth Q, hpiD⟩
  have he_pi : e piD = LinearEquiv.neg (ZMod 3) := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rw [negativeCentralizerEquiv_apply]
    exact coe_piOrth_apply (Q := Q) x.val
  have hdet_pi : LinearEquiv.det (e piD) = -1 := by
    rw [he_pi]
    apply Units.ext
    rw [LinearEquiv.coe_det]
    have h1 : ((LinearEquiv.neg (ZMod 3) : T.eigenspace 1 ≃ₗ[ZMod 3] T.eigenspace 1) :
        T.eigenspace 1 →ₗ[ZMod 3] T.eigenspace 1) =
        (-1 : ZMod 3) • (1 : T.eigenspace 1 →ₗ[ZMod 3] T.eigenspace 1) := by
      ext x; simp
    rw [h1, LinearMap.det_smul, map_one, mul_one, hfin]
    norm_num
  have hC_le_E : omegaGroup hQ ⊓ D ≤ E := by
    intro g hg
    have hgD : g ∈ D := hg.2
    have hgω : g ∈ omegaGroup hQ := hg.1
    let gD : ↥D := ⟨g, hgD⟩
    have hdet : LinearEquiv.det (e gD) = 1 := by
      by_contra hdet1
      have hdetm : LinearEquiv.det (e gD) = -1 := by
        rcases aux_unit_eq_one_or_neg_one (LinearEquiv.det (e gD)) with h | h
        · exact absurd h hdet1
        · exact h
      have hdetprod : LinearEquiv.det (e (gD * piD)) = 1 := by
        rw [map_mul, map_mul, hdetm, hdet_pi]
        norm_num
      have hmemEbig : gD * piD ∈ Ebig := by
        rw [Subgroup.mem_comap, hSLsub]
        exact hdetprod
      have hmemE : (gD * piD).val ∈ E :=
        Subgroup.mem_map.mpr ⟨gD * piD, hmemEbig, rfl⟩
      have hmemω : (gD * piD).val ∈ omegaGroup hQ := (hE_le_C hmemE).1
      have hpiω : piOrth Q ∈ omegaGroup hQ := by
        have h1 : g⁻¹ * (g * piOrth Q) ∈ omegaGroup hQ :=
          (omegaGroup hQ).mul_mem (Subgroup.inv_mem _ hgω) (by simpa using hmemω)
        simpa [mul_assoc] using h1
      exact ff_piOrth_not_mem_omega hQ hdim hsgn hpiω
    have : gD ∈ Ebig := by
      rw [Subgroup.mem_comap, hSLsub]
      exact hdet
    exact Subgroup.mem_map.mpr ⟨gD, this, rfl⟩
  have hCeq : omegaGroup hQ ⊓ D = E := le_antisymm hC_le_E hE_le_C
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = ⊥ :=
    ff_center_specialLinear_fin_three_zmod_three
  let ePSL : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3) :=
    (QuotientGroup.quotientBot (G := Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hcenter).symm
  let isoC : ↥(omegaGroup hQ ⊓ D) ≃* StatedProj (StatedSL 3 (ZMod 3)) :=
    (MulEquiv.subgroupCongr hCeq).trans
      (((Subgroup.equivMapOfInjective Ebig D.subtype D.subtype_injective).trans
        (MulEquiv.subgroupCongr rfl)).symm.trans
        ((e.subgroupMap Ebig).trans
          ((MulEquiv.subgroupCongr hmapE).trans
            (eSL.symm.trans
              ((Matrix.SpecialLinearGroup.toLin_equiv (R := ZMod 3) (V := T.eigenspace 1)
                b).symm.trans
                (ePSL.trans
                  (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
                    3 (ZMod 3))))))))
  have hadm : StatedLieAdmissible .PSL 3 3 1 := by
    unfold StatedLieAdmissible
    norm_num
  have hcard : Nat.card (ZMod 3) = 3 ^ 1 := by rw [Nat.card_zmod]; norm_num
  exact Or.inl ⟨by decide, ⟨hadm, ZMod 3, inferInstance, inferInstance, hcard, ⟨isoC⟩⟩⟩

end CFSG.OddStandard.SmallF3.Omega
