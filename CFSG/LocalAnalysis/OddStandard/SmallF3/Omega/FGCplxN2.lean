module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCplxGrp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCplxCls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGFixMem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCyc4
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN2Core
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelFix
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MShapes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_exists_gamma0 {p : V ≃ₗ[ZMod 3] V}
    (hpO : p ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hpp : ∀ v, p (p v) = -v) :
    ∃ g : ↥(simGroup Q), ∀ v, (g : V ≃ₗ[ZMod 3] V) v = v + p v := by
  have h2 : (-2 : ZMod 3) = 1 := by decide
  have hcplx := fg_cplx_of_similitude (isSimilitude_one_iff.mpr hpO) hpp
  have hB : ∀ v, Q.polarBilin v (p v) = 0 := fun v =>
    hcplx.pair_zero Units.val_one v
  have hQp := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hpO
  let e : V ≃ₗ[ZMod 3] V := LinearEquiv.ofLinearMap (LinearMap.id + (p : V →ₗ[ZMod 3] V))
    ((p : V →ₗ[ZMod 3] V) - LinearMap.id)
    (by
      ext v
      change (p v - v) + p (p v - v) = v
      rw [map_sub, hpp]
      calc p v - v + (-v - p v) = (-2 : ZMod 3) • v := by module
        _ = v := by rw [h2, one_smul])
    (by
      ext v
      change p (v + p v) - (v + p v) = v
      rw [map_add, hpp]
      calc p v + -v - (v + p v) = (-2 : ZMod 3) • v := by module
        _ = v := by rw [h2, one_smul])
  refine ⟨⟨e, -1, fun v => ?_⟩, fun v => rfl⟩
  change Q (v + p v) = ((-1 : (ZMod 3)ˣ) : ZMod 3) * Q v
  rw [QuadraticMap.map_add Q v (p v), hQp v, ← QuadraticMap.polarBilin_apply_apply, hB v]
  have h : ∀ a : ZMod 3, a + a + 0 = ((-1 : (ZMod 3)ˣ) : ZMod 3) * a := by decide
  exact h _

theorem fg_gamma0_pow {p : V ≃ₗ[ZMod 3] V} (hpp : ∀ v, p (p v) = -v) {g : ↥(simGroup Q)}
    (hg : ∀ v, (g : V ≃ₗ[ZMod 3] V) v = v + p v) :
    (∀ v, ((g ^ 2 : ↥(simGroup Q)) : V ≃ₗ[ZMod 3] V) v = -(p v)) ∧
      (∀ v, ((g ^ 3 : ↥(simGroup Q)) : V ≃ₗ[ZMod 3] V) v = v - p v) ∧
      ∀ v, ((g ^ 4 : ↥(simGroup Q)) : V ≃ₗ[ZMod 3] V) v = -v := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  have hmul : ∀ (a b : ↥(simGroup Q)) (v : V), ((a * b : ↥(simGroup Q)) : V ≃ₗ[ZMod 3] V) v =
      (a : V ≃ₗ[ZMod 3] V) ((b : V ≃ₗ[ZMod 3] V) v) := fun a b v => rfl
  have e2 : ∀ v, ((g ^ 2 : ↥(simGroup Q)) : V ≃ₗ[ZMod 3] V) v = -(p v) := by
    intro v
    rw [pow_two, hmul, hg, hg, map_add, hpp]
    calc v + p v + (p v + -v) = (2 : ZMod 3) • p v := by module
      _ = -(p v) := by rw [h2, neg_smul, one_smul]
  have e3 : ∀ v, ((g ^ 3 : ↥(simGroup Q)) : V ≃ₗ[ZMod 3] V) v = v - p v := by
    intro v
    rw [pow_succ, hmul, hg, e2, map_add, hpp]
    abel
  refine ⟨e2, e3, fun v => ?_⟩
  rw [pow_succ, hmul, hg, e3, map_add, hpp]
  calc v + p v - (p v + -v) = (2 : ZMod 3) • v := by module
    _ = -v := by rw [h2, neg_smul, one_smul]

theorem fg_cent_kn2 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (h2 : 2 ≤ Module.finrank (ZMod 3) V) {p : OGroup Q}
    (hp : p * p = piOrth Q)
    (hLM : LayerModel ↥(ffFix hQ h2 (QuotientGroup.mk (orthToSim Q p) : ProjSim Q)) .PSU 3 1)
    {J : Subgroup ↥(omegaProj hQ)}
    (hJ : IsComponentIn J (ffFix hQ h2 (QuotientGroup.mk (orthToSim Q p) : ProjSim Q)))
    {A : Subgroup (ProjSim Q)}
    (hAJ : ∀ a ∈ A, ∀ j ∈ J, projSimAct Q a (j : ProjOrth Q) = (j : ProjOrth Q)) :
    Nat.card A ≤ 2 ∨ Nonempty (↥A ≃* Multiplicative (ZMod 4)) := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 3) (by rw [hdim]; norm_num)
  have hpp : ∀ v, (p : V ≃ₗ[ZMod 3] V) ((p : V ≃ₗ[ZMod 3] V) v) = -v := by
    intro v
    have h1 := congrArg (fun s : OGroup Q => (s : V ≃ₗ[ZMod 3] V) v) hp
    simpa [coe_piOrth_apply] using h1
  have hpO : (p : V ≃ₗ[ZMod 3] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := p.2
  have hcplx : FGCplx Q.polarBilin ((orthToSim Q p : ↥(simGroup Q)) : V ≃ₗ[ZMod 3] V).toLinearMap
      1 := by
    have h := fg_cplx_of_similitude (isSimilitude_one_iff.mpr hpO) hpp
    simpa using h
  obtain ⟨hlie, hΩ, -⟩ := ff6m_N2_core hQ hdim hsgn hp
  rw [← ff_fixSub_orthToSim p] at hlie hΩ
  have hsn := ff_simple_of_lieModel_psu3 hlie
  have hperf := (ff_isQuasisimple_of_simple hsn.1 hsn.2).1
  have hcard : ¬ Nat.card ↥⁅fixSub (simAct Q (orthToSim Q p)),
      fixSub (simAct Q (orthToSim Q p))⁆ ∣ 11232 := by
    rw [ff_card_model_psu3 hlie]
    norm_num
  have ha := fg_ha_of_component hQ h2 (fun E _ hE => ff_simple_of_lieModel_psu3 hE) hLM hJ hΩ
    (fg_comm_le_self _) hperf hAJ
  obtain ⟨g, hg⟩ := fg_exists_gamma0 hpO hpp
  obtain ⟨e2, e3, e4⟩ := fg_gamma0_pow hpp hg
  have hA : A ≤ Subgroup.zpowers (QuotientGroup.mk g : ProjSim Q) := by
    intro a haA
    obtain ⟨γ, α, β, rfl, hγ⟩ := fg_cplx_lifts hQ hdim hcplx hsn.1 hsn.2 hcard (ha a haA)
    have hγ' : ∀ v, (γ : V ≃ₗ[ZMod 3] V) v = α • v + β • (p : V ≃ₗ[ZMod 3] V) v := hγ
    have key : ∀ α β : ZMod 3, (α ≠ 0 ∨ β ≠ 0) → ∃ ε : ZMod 3, ε ≠ 0 ∧
        ((α = ε ∧ β = 0) ∨ (α = ε ∧ β = ε) ∨ (α = 0 ∧ β = -ε) ∨ (α = ε ∧ β = -ε)) := by
      decide
    obtain ⟨ε, hε, hc⟩ := key α β (fg_ab_ne_zero hγ')
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hγ'
      have := fg_mk_eq_of_smul (γ' := 1) hε (fun v => by rw [hγ' v]; simp)
      rw [this, QuotientGroup.mk_one]
      exact one_mem _
    · rw [h1, h2] at hγ'
      have := fg_mk_eq_of_smul (γ' := g) hε (fun v => by rw [hγ' v, hg v, smul_add])
      rw [this]
      exact mem_zpowers _
    · rw [h1, h2] at hγ'
      have := fg_mk_eq_of_smul (γ' := g ^ 2) hε (fun v => by
        rw [hγ' v, e2 v]
        simp)
      rw [this, QuotientGroup.mk_pow]
      exact pow_mem (mem_zpowers _) 2
    · rw [h1, h2] at hγ'
      have := fg_mk_eq_of_smul (γ' := g ^ 3) hε (fun v => by
        rw [hγ' v, e3 v, smul_sub]
        simp [neg_smul, sub_eq_add_neg])
      rw [this, QuotientGroup.mk_pow]
      exact pow_mem (mem_zpowers _) 3
  have h4 : (QuotientGroup.mk g : ProjSim Q) ^ 4 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine mem_piSim_iff.mpr (Or.inr ?_)
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change ((g ^ 4 : ↥(simGroup Q)) : V ≃ₗ[ZMod 3] V) v =
      ((orthToSim Q (piOrth Q) : ↥(simGroup Q)) : V ≃ₗ[ZMod 3] V) v
    rw [e4 v, coe_orthToSim, coe_piOrth_apply]
  exact fg_card_le_two_or_cyclic_four h4 hA

end CFSG.OddStandard.SmallF3.Omega
