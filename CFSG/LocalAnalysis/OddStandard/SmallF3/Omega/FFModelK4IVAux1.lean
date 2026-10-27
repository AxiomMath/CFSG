module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution
open CFSG.LocalAnalysis.ComponentInitial

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_aux_hadj {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    ∀ x y, Q.polarBilin (((ρ : V ≃ₗ[ZMod 3] V)) x) y =
      Q.polarBilin x (((ρ : V ≃ₗ[ZMod 3] V)) y) := by
  have hpol : ∀ x y, Q.polarBilin ((ρ : V ≃ₗ[ZMod 3] V) x) ((ρ : V ≃ₗ[ZMod 3] V) y) =
      - Q.polarBilin x y := by
    intro x y
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar, QuadraticMap.polar, ← map_add, hρ (x + y), hρ x, hρ y]
    simp only [Units.val_neg, Units.val_one, neg_mul, neg_neg]
    ring
  intro x y
  have h := hpol x (-(ρ : V ≃ₗ[ZMod 3] V) y)
  have hρy : (ρ : V ≃ₗ[ZMod 3] V) (-(ρ : V ≃ₗ[ZMod 3] V) y) = y := by
    rw [map_neg, hρρ y, neg_neg]
  rw [hρy, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_neg_right] at h
  simpa using h

theorem ff_aux_hsquare {ρ : ↥(simGroup Q)}
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    ((ρ : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V) ^ 2 =
      algebraMap (ZMod 3) (Module.End (ZMod 3) V) (-1) := by
  rw [pow_two]
  ext v
  rw [Module.End.mul_apply]
  have h : ((ρ : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V)
      (((ρ : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V) v) = -v := by
    simpa using hρρ v
  rw [h]
  simp

theorem ff_aux_fixSub_eq {ρ : ↥(simGroup Q)} :
    fixSub (simAct Q ρ) = orthogonalOperatorCentralizer Q
      (((ρ : V ≃ₗ[ZMod 3] V)) : Module.End (ZMod 3) V) := by
  ext g
  rw [mem_fixSub_iff, orthogonalOperatorCentralizer, Subgroup.mem_comap]
  change (simAct Q ρ g = g) ↔
    ∀ x, (g : V ≃ₗ[ZMod 3] V) (((ρ : V ≃ₗ[ZMod 3] V)) x) =
      ((ρ : V ≃ₗ[ZMod 3] V)) ((g : V ≃ₗ[ZMod 3] V) x)
  constructor
  · intro hg x
    have h1 : ((simAct Q ρ g : OGroup Q) : V ≃ₗ[ZMod 3] V) = (g : V ≃ₗ[ZMod 3] V) :=
      congrArg (fun t : OGroup Q => (t : V ≃ₗ[ZMod 3] V)) hg
    rw [coe_simAct] at h1
    have h2 := congrArg (fun e : V ≃ₗ[ZMod 3] V => e ((ρ : V ≃ₗ[ZMod 3] V) x)) h1
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h2
    exact h2.symm
  · intro hg
    apply Subtype.ext
    rw [coe_simAct]
    ext y
    have h2 := hg ((ρ : V ≃ₗ[ZMod 3] V)⁻¹ y)
    simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h2
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv] using h2.symm

theorem ff_aux_layerModel_core' (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    LayerModel ↥(omegaGroup hQ ⊓ fixSub (simAct Q ρ)) .PSL 2 2 ∧
      ∃ G1 : Subgroup (OGroup Q),
        (∀ g h : OGroup Q, simAct Q ρ g = g → simAct Q ρ h = h → g * h * g⁻¹ * h⁻¹ ∈ G1) ∧
        G1 ≤ omegaGroup hQ ⊓ fixSub (simAct Q ρ) ∧ LieModel ↥G1 .PSL 2 3 2 := by
  haveI : Fact (¬ IsSquare (-1 : ZMod 3)) := ⟨by decide⟩
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 3) (by rw [hdim]; norm_num)
  let T : Module.End (ZMod 3) V := ((ρ : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V)
  have hns : ¬ IsSquare (-1 : ZMod 3) := by decide
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hd : (-1 : ZMod 3) ≠ 0 := by decide
  have hsquare : T ^ 2 = algebraMap (ZMod 3) (Module.End (ZMod 3) V) (-1) := ff_aux_hsquare hρρ
  have hadj : ∀ x y, Q.polarBilin (T x) y = Q.polarBilin x (T y) := ff_aux_hadj hρ hρρ
  have hQp : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  letI : Field (scalarAlgebra T) := scalarField T (-1) hns hsquare
  letI : Module (scalarAlgebra T) V := evaluationModule T
  haveI : IsScalarTower (ZMod 3) (scalarAlgebra T) V := evaluationScalarTower T
  haveI : Module.Finite (ZMod 3) (scalarAlgebra T) := scalarAlgebra_finite T (-1) hns hsquare
  haveI : Finite (scalarAlgebra T) := Module.finite_of_finite (ZMod 3)
  have hfin := scalar_square_actual_finite_dimension (K := ZMod 3) (V := V) T (-1) hns hsquare
  haveI : Module.Finite (scalarAlgebra T) V := hfin.1
  let QE : QuadraticForm (scalarAlgebra T) V :=
    actualPositiveQuadratic Q T (-1) hd hns hsquare hadj
  obtain ⟨-, -, -, hQEnd, -, -, e1, -, -, -, -⟩ :=
    positive_nonsquare_centralizer_structure Q hQp T (-1) hd hns hsquare h2 hadj
  have hdimK : Module.finrank (scalarAlgebra T) V = 3 := by rw [hfin.2.2, hdim]
  have hcard : Nat.card (scalarAlgebra T) = 3 ^ 2 := by
    rw [scalarAlgebra_card T (-1) hns hsquare, Nat.card_zmod]
  have hodd : Odd (Nat.card (scalarAlgebra T)) := by rw [hcard]; decide
  have hK3 : Nat.card (scalarAlgebra T) ≠ 3 := by rw [hcard]; decide
  obtain ⟨dK, ψ, etz, hψ, hetz, hcomm, hquasi, hsq⟩ :=
    orthogonal_three_derived hodd hK3 QE hQEnd hdimK
  let Gc : Subgroup (OGroup Q) := orthogonalOperatorCentralizer Q T
  let E1 : Subgroup ↥Gc := ⁅(⊤ : Subgroup ↥Gc), ⊤⁆
  have hE1_normal : E1.Normal := Subgroup.commutator_normal ⊤ ⊤
  have hE1_map : E1.map e1.toMonoidHom =
      commutator (TauCeti.QuadraticMap.orthogonalGroup QE) := by
    change ((⁅(⊤ : Subgroup ↥Gc), (⊤ : Subgroup ↥Gc)⁆ : Subgroup ↥Gc)).map e1.toMonoidHom =
      _root_.commutator ↥(TauCeti.QuadraticMap.orthogonalGroup QE)
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective e1.toMonoidHom e1.surjective,
      _root_.commutator_def]
  have eE1 : ↥E1 ≃* ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup QE)) :=
    (Subgroup.equivMapOfInjective E1 e1.toMonoidHom e1.injective).trans
      (MulEquiv.subgroupCongr hE1_map)
  have eOq : ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup QE)) ≃*
      ↥(traceZeroSpecialImage (scalarAlgebra T)) :=
    (MulEquiv.subgroupCongr hcomm).trans
      (Subgroup.equivMapOfInjective (traceZeroSpecialImage (scalarAlgebra T))
        etz.symm.toMonoidHom etz.symm.injective).symm
  have ePSL : ↥(traceZeroSpecialImage (scalarAlgebra T)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (scalarAlgebra T) :=
    CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3.traceZeroSpecialImageEquiv (scalarAlgebra T)
  have eAll : ↥E1 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (scalarAlgebra T) :=
    eE1.trans (eOq.trans ePSL)
  have hLie : LieModel ↥E1 .PSL 2 3 2 :=
    CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3.lieModel_psl2_of_equiv
      (p := 3) (f := 2) (by decide) (by omega) (by norm_num) hcard eAll
  have hE1_quot : IsPGroup 2 (↥Gc ⧸ E1) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    refine ⟨1, ?_⟩
    refine QuotientGroup.induction_on g (fun x => ?_)
    change (QuotientGroup.mk' E1 x) ^ 2 = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hx : (e1 x) ^ 2 ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup QE) := hsq (e1 x)
    rw [← hE1_map] at hx
    have hx' : e1 (x ^ 2) ∈ E1.map e1.toMonoidHom := by rw [map_pow]; exact hx
    obtain ⟨y, hyE, hyeq⟩ := Subgroup.mem_map.mp hx'
    have hy : y = x ^ 2 := e1.injective hyeq
    rwa [hy] at hyE
  have hE_omega : E1.map Gc.subtype ≤ omegaGroup hQ := by
    rw [omegaGroup_eq_commutator hQ (by rw [hdim]; norm_num), _root_.commutator_def]
    have h1 : E1.map Gc.subtype ≤ ⁅Gc, Gc⁆ := by
      change ((⁅(⊤ : Subgroup ↥Gc), (⊤ : Subgroup ↥Gc)⁆ : Subgroup ↥Gc)).map Gc.subtype ≤ ⁅Gc, Gc⁆
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono (Subgroup.map_subtype_le ⊤) (Subgroup.map_subtype_le ⊤)
    exact le_trans h1 (Subgroup.commutator_mono le_top le_top)
  let C0 : Subgroup (OGroup Q) := omegaGroup hQ ⊓ Gc
  have hEC0 : E1.map Gc.subtype ≤ C0 := le_inf hE_omega (Subgroup.map_subtype_le E1)
  let D : Subgroup ↥Gc := C0.subgroupOf Gc
  have hE1_le_D : E1 ≤ D := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hEC0 (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  let E0 : Subgroup ↥D := E1.subgroupOf D
  have hE0_normal : E0.Normal := Subgroup.Normal.subgroupOf hE1_normal D
  let eE0 : ↥E0 ≃* ↥E1 :=
    { toFun := fun x => ⟨(x.1 : ↥Gc), x.2⟩
      invFun := fun y => ⟨⟨y.1, hE1_le_D y.2⟩, y.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl
      map_mul' := fun x y => by ext; rfl }
  have hLie' : LieModel ↥E0 .PSL 2 3 2 :=
    CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3.lieModel_psl2_of_equiv
      (p := 3) (f := 2) (by decide) (by omega) (by norm_num) hcard (eE0.trans eAll)
  have hD2 : ∀ x : ↥D, x ^ 2 ∈ E0 := by
    intro x
    have hx : (e1 (x : ↥Gc)) ^ 2 ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup QE) :=
      hsq (e1 (x : ↥Gc))
    rw [← hE1_map] at hx
    have hx' : e1 ((x : ↥Gc) ^ 2) ∈ E1.map e1.toMonoidHom := by rw [map_pow]; exact hx
    obtain ⟨y, hyE, hyeq⟩ := Subgroup.mem_map.mp hx'
    have hy : y = (x : ↥Gc) ^ 2 := e1.injective hyeq
    rw [hy] at hyE
    rw [Subgroup.mem_subgroupOf]
    simpa using hyE
  have hD_quot : IsPGroup 2 (↥D ⧸ E0) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    refine ⟨1, ?_⟩
    refine QuotientGroup.induction_on g (fun x => ?_)
    change (QuotientGroup.mk' E0 x) ^ 2 = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hD2 x
  have hLM_D : LayerModel ↥D .PSL 2 2 := ⟨E0, hE0_normal, hLie', hD_quot⟩
  have hC0_le_Gc : C0 ≤ Gc := inf_le_right
  let eD : ↥D ≃* ↥C0 :=
    { toFun := fun x => ⟨(x.1 : OGroup Q), x.2⟩
      invFun := fun y => ⟨⟨(y : OGroup Q), hC0_le_Gc y.2⟩,
        show (y : OGroup Q) ∈ C0 from y.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl
      map_mul' := fun x y => by ext; rfl }
  have hLM_C0 : LayerModel ↥C0 .PSL 2 2 := ff_layerModel_congr eD hLM_D
  have hGc_eq : Gc = fixSub (simAct Q ρ) := (ff_aux_fixSub_eq).symm
  refine ⟨ff_layerModel_congr (MulEquiv.subgroupCongr (by
    change omegaGroup hQ ⊓ Gc = omegaGroup hQ ⊓ fixSub (simAct Q ρ)
    rw [hGc_eq])) hLM_C0, E1.map Gc.subtype, fun g h hg hh => ?_,
    le_inf hE_omega (by rw [← hGc_eq]; exact Subgroup.map_subtype_le E1),
    CFSG.Blueprint.LieModel.of_mulEquiv
      (Subgroup.equivMapOfInjective E1 Gc.subtype Gc.subtype_injective) hLie⟩
  have hgG : g ∈ Gc := by rw [hGc_eq]; exact mem_fixSub_iff.mpr hg
  have hhG : h ∈ Gc := by rw [hGc_eq]; exact mem_fixSub_iff.mpr hh
  exact Subgroup.mem_map.mpr ⟨⁅(⟨g, hgG⟩ : ↥Gc), ⟨h, hhG⟩⁆,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), rfl⟩

theorem ff_aux_layerModel_core (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    LayerModel ↥(omegaGroup hQ ⊓ fixSub (simAct Q ρ)) .PSL 2 2 :=
  (ff_aux_layerModel_core' hQ hdim hsgn hρ hρρ).1

end CFSG.OddStandard.SmallF3.Omega
