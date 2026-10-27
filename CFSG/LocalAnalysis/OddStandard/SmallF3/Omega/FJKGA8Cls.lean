module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Vocab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutComp
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesWeir
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareSquareStructure

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.GroupTheory.WeirSylow
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fj_K4_split {d : ℕ} (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 2 * d)
    (hsgn : quadSign Q = -1) {x : ProjSim Q} (hx2 : x * x = 1) (hx : ¬ SimInGStar x) :
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
        omega
      have hquad : quadSign Q = 1 := (isPlusType_iff_quadSign_eq_one hQ hdim).mp hplus
      have hne : quadSign Q ≠ 1 := by rw [hsgn]; decide
      exact hne hquad
    · intro v
      have hv := congrArg (fun g : simGroup Q => (g : V ≃ₗ[ZMod 3] V) v) h
      simpa [coe_piOrth_apply] using hv

theorem fj_involution_cases_eight_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) (hsgn : quadSign Q = -1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {x : ProjSim Q} (hx2 : x * x = 1) :
    (∃ s : OGroup Q, s * s = 1 ∧ ffSimOmegaAct hQ h2 x = projAut hQ s) ∨
      ∃ ρ : ↥(simGroup Q), (QuotientGroup.mk ρ : ProjSim Q) = x ∧
        IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1) ∧
        ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v := by
  by_cases hx : SimInGStar x
  · left
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
    have hyy : toProj Q t * toProj Q t = 1 :=
      projOrthToProjSim_injective (by rw [map_mul, map_one]; exact hx2)
    have htmem : t * t ∈ piGroup Q :=
      (QuotientGroup.eq_one_iff (t * t)).mp (by
        change toProj Q (t * t) = 1
        rw [map_mul]
        exact hyy)
    rcases mem_piGroup_iff.mp htmem with h1 | h1
    · refine ⟨t, h1, ?_⟩
      rw [ffSimOmegaAct_projOrthToProjSim]
      rfl
    · exfalso
      obtain ⟨-, hs⟩ := (exists_mul_self_eq_piOrth_iff hQ).mp ⟨t, h1⟩
      rw [hsgn, hdim] at hs
      revert hs
      decide
  · right
    exact fj_K4_split (d := 4) hQ (by rw [hdim]) hsgn hx2 hx

end CFSG.OddStandard.SmallF3.Omega
