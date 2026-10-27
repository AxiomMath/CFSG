module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IIIAux4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IIIAux3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK3Aux2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IIIAux2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutOrth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}


theorem ff_simAct_eq_simConj {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1)) (t : OGroup Q) :
    simAct Q ρ t = simConj hρ t := by
  apply Subtype.ext
  rw [coe_simAct, coe_simConj]

theorem ff_simAct_reflOf {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1)) (u : V) (hu : Q u ≠ 0) :
    simAct Q ρ (reflOf Q u hu) =
      reflOf Q ((ρ : V ≃ₗ[ZMod 3] V) u)
        (by rw [hρ u]; exact mul_ne_zero (by decide) hu) := by
  rw [ff_simAct_eq_simConj hρ, ff_simConj_reflOf hρ u hu]

theorem ff_invType_reflPair (hQ : Q.Nondegenerate) {v u : V} (hv : Q v ≠ 0) (hu : Q u ≠ 0)
    (huv : polar Q v u = 0) (hQv : Q v = 1) (hQu : Q u = -1) :
    invType (reflOf Q v hv * reflOf Q u hu) = (2, 1) := by
  have hvv : reflOf Q v hv * reflOf Q v hv = 1 := reflOf_mul_self v hv
  have huu : reflOf Q u hu * reflOf Q u hu = 1 := reflOf_mul_self u hu
  have horth : ∀ x ∈ commSp (reflOf Q v hv), ∀ y ∈ commSp (reflOf Q u hu),
      polar Q x y = 0 := by
    intro x hx y hy
    rw [ff_commSp_reflOf hQ hv, Submodule.mem_span_singleton] at hx
    rw [ff_commSp_reflOf hQ hu, Submodule.mem_span_singleton] at hy
    obtain ⟨kx, rfl⟩ := hx
    obtain ⟨ky, rfl⟩ := hy
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, huv, smul_zero, smul_zero]
  rw [invType_mul_of_orth hQ hvv huu horth]
  have htv := ff_invType_reflOf hQ hv
  have htu := ff_invType_reflOf hQ hu
  rw [show invDim (reflOf Q v hv) = 1 from congrArg Prod.fst htv,
    show invDim (reflOf Q u hu) = 1 from congrArg Prod.fst htu,
    show invSign (reflOf Q v hv) = toSign (Units.mk0 (Q v) hv) from congrArg Prod.snd htv,
    show invSign (reflOf Q u hu) = toSign (Units.mk0 (Q u) hu) from congrArg Prod.snd htu]
  have ev : Units.mk0 (Q v) hv = 1 := Units.ext (by rw [Units.val_mk0, hQv, Units.val_one])
  have eu : Units.mk0 (Q u) hu = -1 :=
    Units.ext (by rw [Units.val_mk0, hQu, Units.val_neg, Units.val_one])
  rw [ev, eu, map_one, aux_toSign_neg_one]
  norm_num

theorem ff_invType_reflQuad (hQ : Q.Nondegenerate) {g₂ g₃ : OGroup Q} (hg₂ : g₂ * g₂ = 1)
    (hg₃ : g₃ * g₃ = 1) (ht₂ : invType g₂ = (2, 1)) (ht₃ : invType g₃ = (2, 1))
    (horth : ∀ x ∈ commSp g₂, ∀ y ∈ commSp g₃, polar Q x y = 0) :
    invType (g₂ * g₃) = (4, 1) := by
  rw [invType_mul_of_orth hQ hg₂ hg₃ horth,
    show invDim g₂ = 2 from congrArg Prod.fst ht₂,
    show invDim g₃ = 2 from congrArg Prod.fst ht₃,
    show invSign g₂ = 1 from congrArg Prod.snd ht₂,
    show invSign g₃ = 1 from congrArg Prod.snd ht₃]
  norm_num

theorem ff_exists_hyperbolic_pair (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = v) :
    ∃ x₂ x₃ y₂ y₃ : V,
      x₂ ∈ positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1 ∧
      x₃ ∈ positiveSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1 ∧
      y₂ ∈ negativeSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1 ∧
      y₃ ∈ negativeSquareKernel (ρ : V ≃ₗ[ZMod 3] V) 1 ∧
      Q.polarBilin x₂ y₂ = 1 ∧ Q.polarBilin x₃ y₃ = 1 ∧
      Q.polarBilin x₂ y₃ = 0 ∧ Q.polarBilin x₃ y₂ = 0 := by
  let A : V ≃ₗ[ZMod 3] V := ρ
  let Vpos : Submodule (ZMod 3) V := positiveSquareKernel A 1
  let Vneg : Submodule (ZMod 3) V := negativeSquareKernel A 1
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hQp : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hsq : ∀ x : V, A (A x) = (1 : ZMod 3) • x := by
    intro x; rw [hρρ x, one_smul]
  have hgeo := negative_square_kernel_geometry Q hQp A 1 (-1) 1 one_ne_zero one_ne_zero h2
    hsq (by norm_num) (ff_polar_isSimilitude_neg (Q := Q) hρ) (by norm_num)
  obtain ⟨-, -, hperf, -, hhalf, -⟩ := hgeo
  have hfin : Module.finrank (ZMod 3) Vpos = 3 := by
    change Module.finrank (ZMod 3) (positiveSquareKernel A 1) = 3
    rw [hhalf, hdim]
  let b : Module.Basis (Fin 3) (ZMod 3) Vpos :=
    Module.finBasisOfFinrankEq (R := ZMod 3) (M := Vpos) hfin
  letI : (crossPairing Q.polarBilin Vpos Vneg).IsPerfPair := hperf
  let e : Vneg ≃ₗ[ZMod 3] Module.Dual (ZMod 3) Vpos :=
    (crossPairing Q.polarBilin Vpos Vneg).flip.toPerfPair
  have hkey : ∀ i j : Fin 3,
      Q.polarBilin ((b i : Vpos) : V) (((e.symm (b.dualBasis j) : Vneg) : V)) =
        if i = j then 1 else 0 := by
    intro i j
    have h1 : crossPairing Q.polarBilin Vpos Vneg (b i) (e.symm (b.dualBasis j)) =
        e (e.symm (b.dualBasis j)) (b i) := rfl
    change crossPairing Q.polarBilin Vpos Vneg (b i) (e.symm (b.dualBasis j)) =
        if i = j then 1 else 0
    rw [h1, LinearEquiv.apply_symm_apply, b.dualBasis_apply_self]
  refine ⟨((b 1 : Vpos) : V), ((b 2 : Vpos) : V),
    ((e.symm (b.dualBasis 1) : Vneg) : V), ((e.symm (b.dualBasis 2) : Vneg) : V),
    (b 1).2, (b 2).2, (e.symm (b.dualBasis 1)).2, (e.symm (b.dualBasis 2)).2,
    ?_, ?_, ?_, ?_⟩
  · simpa using hkey 1 1
  · simpa using hkey 2 2
  · simpa using hkey 1 2
  · simpa using hkey 2 1


theorem ff_K4III_cover_of_data (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = v)
    {u₂ u₃ v₂ v₃ : V}
    (hu₂ : Q u₂ = -1) (hu₃ : Q u₃ = -1) (hv₂ : Q v₂ = 1) (hv₃ : Q v₃ = 1)
    (hvu₂ : polar Q v₂ u₂ = 0) (hvu₃ : polar Q v₃ u₃ = 0)
    (hvu₂₃ : polar Q v₂ u₃ = 0) (hvu₃₂ : polar Q v₃ u₂ = 0)
    (hvv : polar Q v₂ v₃ = 0) (huu : polar Q u₂ u₃ = 0)
    (hρu₂ : (ρ : V ≃ₗ[ZMod 3] V) u₂ = v₂) (hρu₃ : (ρ : V ≃ₗ[ZMod 3] V) u₃ = v₃) :
    ∃ w : ↥(omegaProj hQ),
      w ∈ twoPrimeRes (twoRes (ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q))) ∧
      w * w = 1 ∧ KM0 (projOrthToProjSim Q (w : ProjOrth Q)) ∧
      ∃ a : ↥(omegaProj hQ),
        ffSimOmegaAct hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q) a * a⁻¹ = w := by
  have hu₂ne : Q u₂ ≠ 0 := by rw [hu₂]; decide
  have hu₃ne : Q u₃ ≠ 0 := by rw [hu₃]; decide
  have hv₂ne : Q v₂ ≠ 0 := by rw [hv₂]; decide
  have hv₃ne : Q v₃ ≠ 0 := by rw [hv₃]; decide
  have hρv₂ : (ρ : V ≃ₗ[ZMod 3] V) v₂ = u₂ := by rw [← hρu₂, hρρ]
  have hρv₃ : (ρ : V ≃ₗ[ZMod 3] V) v₃ = u₃ := by rw [← hρu₃, hρρ]
  have huu' : polar Q u₃ u₂ = 0 := (QuadraticMap.polar_comm Q u₃ u₂).trans huu
  let a : OGroup Q := reflOf Q u₂ hu₂ne * reflOf Q u₃ hu₃ne
  let g₂ : OGroup Q := reflOf Q v₂ hv₂ne * reflOf Q u₂ hu₂ne
  let g₃ : OGroup Q := reflOf Q v₃ hv₃ne * reflOf Q u₃ hu₃ne
  let t : OGroup Q := simAct Q ρ a * a⁻¹
  have ha_mem : a ∈ omegaGroup hQ := by
    rw [show a = reflOf Q u₂ hu₂ne * reflOf Q u₃ hu₃ne from rfl]
    exact reflOf_mul_reflOf_mem_omegaGroup hQ u₂ u₃ hu₂ne hu₃ne (by rw [hu₂, hu₃])
  have ht_mem : t ∈ omegaGroup hQ := by
    rw [show t = simAct Q ρ a * a⁻¹ from rfl]
    exact mul_mem (ff_simAct_mem_omegaGroup hQ (by omega) ρ ha_mem)
      (inv_mem ha_mem)
  have h2dim : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hsimp : simAct Q ρ a =
      reflOf Q v₂ hv₂ne * reflOf Q v₃ hv₃ne := by
    rw [show a = reflOf Q u₂ hu₂ne * reflOf Q u₃ hu₃ne from rfl, map_mul]
    simp only [ff_simAct_reflOf hρ u₂ hu₂ne, ff_simAct_reflOf hρ u₃ hu₃ne, hρu₂, hρu₃]
  have hainv : a⁻¹ = reflOf Q u₃ hu₃ne * reflOf Q u₂ hu₂ne := by
    rw [show a = reflOf Q u₂ hu₂ne * reflOf Q u₃ hu₃ne from rfl, mul_inv_rev,
      reflOf_inv, reflOf_inv]
  have ht_eq : t = g₂ * g₃ := by
    rw [show t = simAct Q ρ a * a⁻¹ from rfl, hsimp, hainv]
    rw [show g₂ * g₃ = (reflOf Q v₂ hv₂ne * reflOf Q u₂ hu₂ne) *
        (reflOf Q v₃ hv₃ne * reflOf Q u₃ hu₃ne) from rfl]
    rw [mul_comm_reflOf_of_orth u₃ u₂ hu₃ne hu₂ne huu']
    rw [mul_assoc (reflOf Q v₂ hv₂ne) (reflOf Q v₃ hv₃ne)
        (reflOf Q u₂ hu₂ne * reflOf Q u₃ hu₃ne)]
    rw [← mul_assoc (reflOf Q v₃ hv₃ne) (reflOf Q u₂ hu₂ne) (reflOf Q u₃ hu₃ne)]
    rw [mul_comm_reflOf_of_orth v₃ u₂ hv₃ne hu₂ne hvu₃₂]
    rw [mul_assoc (reflOf Q u₂ hu₂ne) (reflOf Q v₃ hv₃ne) (reflOf Q u₃ hu₃ne)]
    rw [← mul_assoc (reflOf Q v₂ hv₂ne) (reflOf Q u₂ hu₂ne)
        (reflOf Q v₃ hv₃ne * reflOf Q u₃ hu₃ne)]
  have hgg₂ : g₂ * g₂ = 1 := by
    have hc : reflOf Q v₂ hv₂ne * reflOf Q u₂ hu₂ne =
        reflOf Q u₂ hu₂ne * reflOf Q v₂ hv₂ne :=
      mul_comm_reflOf_of_orth v₂ u₂ hv₂ne hu₂ne hvu₂
    rw [show g₂ = reflOf Q v₂ hv₂ne * reflOf Q u₂ hu₂ne from rfl]
    calc (reflOf Q v₂ hv₂ne * reflOf Q u₂ hu₂ne) *
          (reflOf Q v₂ hv₂ne * reflOf Q u₂ hu₂ne)
        = reflOf Q v₂ hv₂ne * (reflOf Q u₂ hu₂ne * reflOf Q v₂ hv₂ne) *
          reflOf Q u₂ hu₂ne := by group
      _ = reflOf Q v₂ hv₂ne * (reflOf Q v₂ hv₂ne * reflOf Q u₂ hu₂ne) *
          reflOf Q u₂ hu₂ne := by rw [← hc]
      _ = 1 := by rw [← mul_assoc, reflOf_mul_self, one_mul, reflOf_mul_self]
  have hgg₃ : g₃ * g₃ = 1 := by
    have hc : reflOf Q v₃ hv₃ne * reflOf Q u₃ hu₃ne =
        reflOf Q u₃ hu₃ne * reflOf Q v₃ hv₃ne :=
      mul_comm_reflOf_of_orth v₃ u₃ hv₃ne hu₃ne hvu₃
    rw [show g₃ = reflOf Q v₃ hv₃ne * reflOf Q u₃ hu₃ne from rfl]
    calc (reflOf Q v₃ hv₃ne * reflOf Q u₃ hu₃ne) *
          (reflOf Q v₃ hv₃ne * reflOf Q u₃ hu₃ne)
        = reflOf Q v₃ hv₃ne * (reflOf Q u₃ hu₃ne * reflOf Q v₃ hv₃ne) *
          reflOf Q u₃ hu₃ne := by group
      _ = reflOf Q v₃ hv₃ne * (reflOf Q v₃ hv₃ne * reflOf Q u₃ hu₃ne) *
          reflOf Q u₃ hu₃ne := by rw [← hc]
      _ = 1 := by rw [← mul_assoc, reflOf_mul_self, one_mul, reflOf_mul_self]
  have htype₂ : invType g₂ = (2, 1) :=
    ff_invType_reflPair hQ hv₂ne hu₂ne hvu₂ hv₂ hu₂
  have htype₃ : invType g₃ = (2, 1) :=
    ff_invType_reflPair hQ hv₃ne hu₃ne hvu₃ hv₃ hu₃
  have hvu₃₂' : polar Q u₂ v₃ = 0 := (QuadraticMap.polar_comm Q u₂ v₃).trans hvu₃₂
  have horth : ∀ x ∈ commSp g₂, ∀ y ∈ commSp g₃, polar Q x y = 0 := by
    intro x hx y hy
    rw [show g₂ = reflOf Q v₂ hv₂ne * reflOf Q u₂ hu₂ne from rfl,
      commSp_reflOf_mul_reflOf_of_orth hQ v₂ u₂ hv₂ne hu₂ne hvu₂] at hx
    rw [show g₃ = reflOf Q v₃ hv₃ne * reflOf Q u₃ hu₃ne from rfl,
      commSp_reflOf_mul_reflOf_of_orth hQ v₃ u₃ hv₃ne hu₃ne hvu₃] at hy
    obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨d₁, d₂, rfl⟩ := Submodule.mem_span_pair.mp hy
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
    rw [hvv, hvu₂₃, hvu₃₂', huu]
    ring
  have ht_type : invType t = (4, 1) := by
    rw [ht_eq]
    exact ff_invType_reflQuad hQ hgg₂ hgg₃ htype₂ htype₃ horth
  have ht_self : t * t = 1 := by
    rw [ht_eq]
    exact mul_mul_self_of_orth hQ hgg₂ hgg₃ horth
  have ht_ne : toProj Q t ≠ 1 := by
    intro h1
    have hker : t ∈ (toProj Q).ker := MonoidHom.mem_ker.mpr h1
    rw [QuotientGroup.ker_mk' (piGroup Q)] at hker
    rcases mem_piGroup_iff.mp hker with ht1 | htpi
    · rw [ht1, invType_one] at ht_type
      exact absurd ht_type (by decide)
    · rw [htpi, invType_piOrth hQ, hdim, hsgn] at ht_type
      exact absurd ht_type (by decide)
  have hg₂_fix : simAct Q ρ g₂ = g₂ := by
    rw [show g₂ = reflOf Q v₂ hv₂ne * reflOf Q u₂ hu₂ne from rfl, map_mul]
    simp only [ff_simAct_reflOf hρ v₂ hv₂ne, ff_simAct_reflOf hρ u₂ hu₂ne, hρv₂, hρu₂]
    rw [mul_comm_reflOf_of_orth u₂ v₂ _ _ ((QuadraticMap.polar_comm Q u₂ v₂).trans hvu₂)]
  have hg₃_fix : simAct Q ρ g₃ = g₃ := by
    rw [show g₃ = reflOf Q v₃ hv₃ne * reflOf Q u₃ hu₃ne from rfl, map_mul]
    simp only [ff_simAct_reflOf hρ v₃ hv₃ne, ff_simAct_reflOf hρ u₃ hu₃ne, hρv₃, hρu₃]
    rw [mul_comm_reflOf_of_orth u₃ v₃ _ _ ((QuadraticMap.polar_comm Q u₃ v₃).trans hvu₃)]
  have ht_fix : simAct Q ρ t = t := by
    rw [ht_eq, map_mul, hg₂_fix, hg₃_fix]
  let w : ↥(omegaProj hQ) :=
    ⟨toProj Q t, (mem_omegaProj_iff hQ).mpr ⟨t, ht_mem, rfl⟩⟩
  have hw_self : w * w = 1 := by
    apply Subtype.ext
    change toProj Q t * toProj Q t = 1
    rw [← map_mul, ht_self, map_one]
  haveI hSimple : IsSimpleGroup ↥(ffFix hQ h2dim
      (QuotientGroup.mk ρ : ProjSim Q)) := by
    have hC : IsSimpleGroup ↥(omegaGroup hQ ⊓ fixSub (simAct Q ρ)) :=
      (ff_simple_of_lieModel_psl3 (ff_K4III_C_lieModel hQ hdim hsgn hρ hρρ)).1
    obtain ⟨e, -⟩ := ff_fixEquiv_sim hQ hdim hsgn ρ
    exact e.symm.isSimpleGroup
  have hnc : ∃ x y : ↥(ffFix hQ h2dim (QuotientGroup.mk ρ : ProjSim Q)),
      x * y ≠ y * x := by
    have hC := (ff_simple_of_lieModel_psl3 (ff_K4III_C_lieModel hQ hdim hsgn hρ hρρ)).2
    obtain ⟨e, -⟩ := ff_fixEquiv_sim hQ hdim hsgn ρ
    obtain ⟨x, y, hxy⟩ := hC
    exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul, h]))⟩
  have hw_ffFix : w ∈ ffFix hQ h2dim (QuotientGroup.mk ρ : ProjSim Q) :=
    (ff_mem_ffFix_sim_iff hQ hdim hsgn ρ w).mpr
      ⟨t, Subgroup.mem_inf.mpr ⟨ht_mem, mem_fixSub_iff.mpr ht_fix⟩, rfl⟩
  have hw_X : w ∈ twoPrimeRes (twoRes (ffFix hQ h2dim
      (QuotientGroup.mk ρ : ProjSim Q))) :=
    ff_mem_X_of_simple _ _ le_rfl hSimple hnc hw_ffFix hw_self
  have hKM0 : KM0 (projOrthToProjSim Q (w : ProjOrth Q)) :=
    ⟨toProj Q t, rfl, ht_ne, t, ht_self, ht_type, rfl⟩
  refine ⟨w, hw_X, hw_self, hKM0, ⟨toProj Q a, (mem_omegaProj_iff hQ).mpr ⟨a, ha_mem, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change ((ffSimOmegaAct hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)
    (⟨toProj Q a, (mem_omegaProj_iff hQ).mpr ⟨a, ha_mem, rfl⟩⟩ : ↥(omegaProj hQ)) :
      ↥(omegaProj hQ)) : ProjOrth Q) *
    ((⟨toProj Q a, (mem_omegaProj_iff hQ).mpr ⟨a, ha_mem, rfl⟩⟩ : ↥(omegaProj hQ))⁻¹ :
      ↥(omegaProj hQ)) = (w : ↥(omegaProj hQ))
  rw [coe_ffSimOmegaAct, projSimAct_mk, projActAux_toProj]
  change toProj Q (simAct Q ρ a) * (toProj Q a)⁻¹ = toProj Q t
  rw [show t = simAct Q ρ a * a⁻¹ from rfl, ← map_inv, ← map_mul]

theorem ff_exists_cover_vectors (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = v) :
    ∃ u₂ u₃ v₂ v₃ : V,
      Q u₂ = -1 ∧ Q u₃ = -1 ∧ Q v₂ = 1 ∧ Q v₃ = 1 ∧
      polar Q v₂ u₂ = 0 ∧ polar Q v₃ u₃ = 0 ∧
      polar Q v₂ u₃ = 0 ∧ polar Q v₃ u₂ = 0 ∧
      polar Q v₂ v₃ = 0 ∧ polar Q u₂ u₃ = 0 ∧
      (ρ : V ≃ₗ[ZMod 3] V) u₂ = v₂ ∧ (ρ : V ≃ₗ[ZMod 3] V) u₃ = v₃ := by
  obtain ⟨x₂, x₃, y₂, y₃, hx₂, hx₃, hy₂, hy₃, hxy22, hxy33, hxy23, hxy32⟩ :=
    ff_exists_hyperbolic_pair hQ hdim hsgn hρ hρρ
  have hx₂q : Q x₂ = 0 := ff_posKernel_singular hρ hx₂
  have hx₃q : Q x₃ = 0 := ff_posKernel_singular hρ hx₃
  have hy₂q : Q y₂ = 0 := ff_negKernel_singular hρ hy₂
  have hy₃q : Q y₃ = 0 := ff_negKernel_singular hρ hy₃
  have hxx : polar Q x₂ x₃ = 0 := ff_posKernel_polar hρ hx₂ hx₃
  have hyy : polar Q y₂ y₃ = 0 := ff_negKernel_polar hρ hy₂ hy₃
  have hp22 : polar Q x₂ y₂ = 1 := by
    simpa only [QuadraticMap.polarBilin_apply_apply] using hxy22
  have hp33 : polar Q x₃ y₃ = 1 := by
    simpa only [QuadraticMap.polarBilin_apply_apply] using hxy33
  have hp23 : polar Q x₂ y₃ = 0 := by
    simpa only [QuadraticMap.polarBilin_apply_apply] using hxy23
  have hp32 : polar Q x₃ y₂ = 0 := by
    simpa only [QuadraticMap.polarBilin_apply_apply] using hxy32
  have hxx' : polar Q x₃ x₂ = 0 := (QuadraticMap.polar_comm Q x₃ x₂).trans hxx
  have hyy' : polar Q y₃ y₂ = 0 := (QuadraticMap.polar_comm Q y₃ y₂).trans hyy
  have hyx22 : polar Q y₂ x₂ = 1 := (QuadraticMap.polar_comm Q y₂ x₂).trans hp22
  have hyx33 : polar Q y₃ x₃ = 1 := (QuadraticMap.polar_comm Q y₃ x₃).trans hp33
  have hyx23 : polar Q y₂ x₃ = 0 := (QuadraticMap.polar_comm Q y₂ x₃).trans hp32
  have hyx32 : polar Q y₃ x₂ = 0 := (QuadraticMap.polar_comm Q y₃ x₂).trans hp23
  refine ⟨x₂ - y₂, x₃ - y₃, x₂ + y₂, x₃ + y₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ff_map_sub, hx₂q, hy₂q, hp22]; norm_num
  · rw [ff_map_sub, hx₃q, hy₃q, hp33]; norm_num
  · rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq Q, hx₂q, hy₂q, hp22]; norm_num
  · rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq Q, hx₃q, hy₃q, hp33]; norm_num
  · rw [QuadraticMap.polar_comm, ff_polar_sub_add, QuadraticMap.polar_self, QuadraticMap.polar_self,
      hx₂q, hy₂q, hp22, hyx22]; norm_num
  · rw [QuadraticMap.polar_comm, ff_polar_sub_add, QuadraticMap.polar_self, QuadraticMap.polar_self,
      hx₃q, hy₃q, hp33, hyx33]; norm_num
  · rw [QuadraticMap.polar_comm, ff_polar_sub_add, hxx', hp32, hyx32, hyy']; norm_num
  · rw [QuadraticMap.polar_comm, ff_polar_sub_add, hxx, hp23, hyx23, hyy]; norm_num
  · rw [ff_polar_add_add, hxx, hp23, hyx23, hyy]; norm_num
  · rw [ff_polar_sub_sub, hxx, hp23, hyx23, hyy]; norm_num
  · rw [map_sub, ff_posKernel_apply hx₂, ff_negKernel_apply hy₂, sub_neg_eq_add]
  · rw [map_sub, ff_posKernel_apply hx₃, ff_negKernel_apply hy₃, sub_neg_eq_add]




end CFSG.OddStandard.SmallF3.Omega
