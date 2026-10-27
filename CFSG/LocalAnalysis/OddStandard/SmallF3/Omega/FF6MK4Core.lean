module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IVAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement
open CFSG.GroupTheory.WeirSylow
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution
open CFSG.LocalAnalysis.ComponentInitial

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6m_K4_split (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {x : ProjSim Q} (hx2 : x * x = 1) (hx : KM4 x) :
    ∃ ρ : ↥(simGroup Q), (QuotientGroup.mk ρ : ProjSim Q) = x ∧
      IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1) ∧
      ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v := by
  obtain ⟨ρ, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨c, hc⟩ := ρ.2
  have hunits : ∀ c : (ZMod 3)ˣ, c = 1 ∨ c = -1 := by decide
  rcases hunits c with rfl | rfl
  · exfalso
    apply hx
    have hmem : (ρ : V ≃ₗ[ZMod 3] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      isSimilitude_one_iff.mp hc
    refine ⟨toProj Q ⟨(ρ : V ≃ₗ[ZMod 3] V), hmem⟩, ?_⟩
    rw [projOrthToProjSim_toProj]
    exact congrArg QuotientGroup.mk (Subtype.ext rfl)
  · refine ⟨ρ, rfl, hc, ?_⟩
    have h1 : ρ * ρ ∈ piSim Q :=
      (QuotientGroup.eq_one_iff (ρ * ρ)).mp (by rw [QuotientGroup.mk_mul]; exact hx2)
    rcases mem_piSim_iff.mp h1 with h | h
    · exfalso
      have hfix : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = v := by
        intro v
        have hv := congrArg (fun g : simGroup Q => (g : V ≃ₗ[ZMod 3] V) v) h
        simpa using hv
      have hQp : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
      have h2 : (2 : ZMod 3) ≠ 0 := by decide
      have hsq : ∀ v : V, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) =
          (1 : ZMod 3) • v := by
        intro v; rw [hfix v, one_smul]
      have hsim : ∀ u v : V, Q.polarBilin ((ρ : V ≃ₗ[ZMod 3] V) u)
          ((ρ : V ≃ₗ[ZMod 3] V) v) = (-1) * Q.polarBilin u v := by
        intro u v
        simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
        rw [← map_add, hc, hc, hc]
        simp only [Units.val_neg, Units.val_one, neg_mul, neg_neg]
        ring
      have hgeo := negative_square_kernel_geometry Q hQp (ρ : V ≃ₗ[ZMod 3] V) 1 (-1) 1
        one_ne_zero one_ne_zero h2 hsq (by norm_num) hsim (by norm_num)
      obtain ⟨hpos, -, -, -, hhalf, -⟩ := hgeo
      have hplus : IsPlusType Q := by
        refine ⟨positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1, ?_, hpos⟩
        rw [hhalf, hdim]
      have hquad : quadSign Q = 1 :=
        (isPlusType_iff_quadSign_eq_one hQ (d := 3) (by omega)).mp hplus
      have hne : quadSign Q ≠ 1 := by rw [hsgn]; decide
      exact hne hquad
    · intro v
      have hv := congrArg (fun g : simGroup Q => (g : V ≃ₗ[ZMod 3] V) v) h
      simpa [coe_piOrth_apply] using hv

theorem ff6m_K4_core (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {ρ : ↥(simGroup Q)} (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    LieModel ↥⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ .PSL 2 3 2 ∧
      ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ ≤ omegaGroup hQ ∧
      ∀ g : OGroup Q, simAct Q ρ g = g →
        g * g ∈ ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ := by
  haveI : Fact (¬ IsSquare (-1 : ZMod 3)) := ⟨by decide⟩
  haveI : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := ZMod 3) (by rw [hdim]; norm_num)
  let T : Module.End (ZMod 3) V := ((ρ : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V)
  have hns : ¬ IsSquare (-1 : ZMod 3) := by decide
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hd : (-1 : ZMod 3) ≠ 0 := by decide
  have hsquare : T ^ 2 = algebraMap (ZMod 3) (Module.End (ZMod 3) V) (-1) :=
    ff_aux_hsquare hρρ
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
  have hsquare_mem : ∀ x : ↥Gc, x ^ 2 ∈ E1 := by
    intro x
    have hx : (e1 x) ^ 2 ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup QE) := hsq (e1 x)
    rw [← hE1_map] at hx
    have hx' : e1 (x ^ 2) ∈ E1.map e1.toMonoidHom := by rw [map_pow]; exact hx
    obtain ⟨y, hyE, hyeq⟩ := Subgroup.mem_map.mp hx'
    have hy : y = x ^ 2 := e1.injective hyeq
    rwa [hy] at hyE
  have hE1_map_Gc : E1.map Gc.subtype = ⁅Gc, Gc⁆ := Subgroup.map_subtype_commutator Gc
  have hGc_eq : Gc = fixSub (simAct Q ρ) := (ff_aux_fixSub_eq).symm
  have hE1_map_fix : E1.map Gc.subtype = ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ := by
    rw [hE1_map_Gc, hGc_eq]
  have hE_omega : E1.map Gc.subtype ≤ omegaGroup hQ := by
    rw [hE1_map_Gc, omegaGroup_eq_commutator hQ (by rw [hdim]; norm_num),
      _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hLie_fix : LieModel ↥⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ .PSL 2 3 2 := by
    rw [← hE1_map_fix]
    exact CFSG.Blueprint.LieModel.of_mulEquiv
      (Subgroup.equivMapOfInjective E1 Gc.subtype Gc.subtype_injective) hLie
  refine ⟨hLie_fix, ?_, ?_⟩
  · rwa [hE1_map_fix] at hE_omega
  · intro g hg
    have hgG : g ∈ Gc := by rw [hGc_eq]; exact mem_fixSub_iff.mpr hg
    have hmem : (⟨g, hgG⟩ : ↥Gc) ^ 2 ∈ E1 := hsquare_mem ⟨g, hgG⟩
    rw [← hE1_map_fix]
    refine Subgroup.mem_map.mpr ⟨(⟨g, hgG⟩ : ↥Gc) ^ 2, hmem, ?_⟩
    simp [pow_two]

end CFSG.OddStandard.SmallF3.Omega
