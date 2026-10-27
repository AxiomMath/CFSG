module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4Cover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem t5_cov5_model (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {ρ : simGroup Q}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    ∃ w ∈ twoRes (omegaGroup hQ ⊓ fixSub (simAct Q ρ)), w * w = 1 ∧ invType w = (4, 1) ∧
      ∃ c : omegaGroup hQ, w = (c : OGroup Q) * simAct Q ρ (c : OGroup Q)⁻¹ := by
  obtain ⟨t, a, ha, htG1, htt, hty, hta⟩ := ff6m_K4_cover_expl hQ hdim hsgn hρ hρρ
  obtain ⟨hLie, hG1le, -⟩ := ff6m_K4_core hQ hdim hρ hρρ
  let C : Subgroup (OGroup Q) := fixSub (simAct Q ρ)
  let G1 : Subgroup (OGroup Q) := ⁅C, C⁆
  have hG1leC : G1 ≤ C := by
    show ⁅C, C⁆ ≤ C
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hg hh) (C.inv_mem hg)) (C.inv_mem hh)
  obtain ⟨hGfin, hGsimple⟩ := ff_fin_simple_psl2 hLie
  haveI := hGfin
  obtain ⟨-, hnc⟩ := ff_simple_of_lieModel_psl2 hLie
  have hfB : ∀ x : ↥G1, G1.subtype x ∈ omegaGroup hQ ⊓ C := fun x => ⟨hG1le x.2, hG1leC x.2⟩
  have hX : t ∈ twoPrimeRes (twoRes (omegaGroup hQ ⊓ C)) :=
    ff_mem_X_of_simple_hom (omegaGroup hQ ⊓ C) G1.subtype Subtype.val_injective hfB hGsimple hnc
      ⟨⟨t, htG1⟩, rfl⟩ htt
  have hw : t ∈ twoRes (omegaGroup hQ ⊓ C) :=
    (Subgroup.closure_le (twoRes (omegaGroup hQ ⊓ C))).mpr (fun g hg => hg.1) hX
  have hρρ' : ρ * ρ = orthToSim Q (piOrth Q) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = (piOrth Q : V ≃ₗ[ZMod 3] V) v
    rw [hρρ v, coe_piOrth_apply]
  have hρ2 : simAct Q ρ (simAct Q ρ a) = a := by
    have h1 : simAct Q (ρ * ρ) a = simAct Q ρ (simAct Q ρ a) := by
      rw [map_mul]
      rfl
    have hinv : (piOrth Q)⁻¹ = piOrth Q := inv_eq_of_mul_eq_one_right piOrth_mul_self
    rw [← h1, hρρ', simAct_orthToSim, hinv]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    simp [coe_piOrth_apply]
  refine ⟨t, hw, htt, hty, ⟨simAct Q ρ a, ff_simAct_mem_omegaGroup hQ (by omega) ρ ha⟩, ?_⟩
  change t = simAct Q ρ a * simAct Q ρ (simAct Q ρ a)⁻¹
  rw [map_inv, hρ2]
  exact hta.symm

end CFSG.OddStandard.SmallF3.Omega
