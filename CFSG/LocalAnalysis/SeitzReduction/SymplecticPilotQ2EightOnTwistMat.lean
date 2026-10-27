module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOnTwist
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDAlignMinus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module Matrix CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus quadMinus coe_quadMinus)
open scoped commutatorElement

section Lin

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem on_reflect_conj_mem_commutator (v : V) {g : V ≃ₗ[K] V}
    (hg : g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    reflect Q v * g * reflect Q v ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have e : reflect Q v * g * reflect Q v = g * ⁅g⁻¹, reflect Q v⁆ := by
    rw [commutatorElement_def, reflect_inv]
    group
  rw [e]
  exact Subgroup.mul_mem _ hg (Subgroup.commutator_mem_commutator
    (Subgroup.inv_mem _ (on_commutator_le_self _ hg)) (reflect_mem_orthogonalGroup Q v))

end Lin

section Mat

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem on_map_statedOmega_eq (Q : QuadraticForm K (ι → K)) :
    (StatedOmega ⇑Q).map pdLinEquiv.toMonoidHom =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hC : (closure {B : GL ι K | ∀ v, Q ((B : Matrix ι ι K) *ᵥ v) = Q v}).map
      pdLinEquiv.toMonoidHom = TauCeti.QuadraticMap.orthogonalGroup Q := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, closure_le]
      intro B hB
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
        rw [MulEquiv.coe_toMonoidHom, pdLinEquiv_apply]
        exact hB v
    · intro g hg
      refine ⟨pdLinEquiv.symm g, subset_closure fun v => ?_, by simp⟩
      rw [← pdLinEquiv_apply, MulEquiv.apply_symm_apply]
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg v
  rw [StatedOmega, Subgroup.map_commutator, hC]

theorem on_pdLinEquiv_pdSym (Q : QuadraticForm K (ι → K)) (v : ι → K) :
    pdLinEquiv (pdSym Q v) = reflect Q v := by
  rw [pdSym, MulEquiv.apply_symm_apply]

variable [Finite K] [CharP K 2]

omit [Finite K] in
theorem on_eq_one_or_eq_of_commute_mat (hK : Nat.card K = 2) (Q : QuadraticForm K (ι → K))
    {Q0 : (ι → K) → K} (hQ0 : ⇑Q = Q0) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 6 ≤ Fintype.card ι) {v : ι → K} (hv : Q v = 1) (β α : MulAut (StatedOmega Q0))
    (hβ : ∀ A, ((β A : StatedOmega Q0) : GL ι K) = pdSym Q v * (A : GL ι K) * pdSym Q v)
    (hfix : ∀ A, β A = A → α A = A) (hcomm : ∀ A, α (β A) = β (α A)) : α = 1 ∨ α = β := by
  subst hQ0
  obtain ⟨e, hecoe⟩ : ∃ e : StatedOmega ⇑Q ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, ∀ A,
        ((e A : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
          (ι → K) ≃ₗ[K] (ι → K)) = pdLinEquiv (A : GL ι K) :=
    ⟨(MulEquiv.subgroupMap pdLinEquiv (StatedOmega ⇑Q)).trans
      (MulEquiv.subgroupCongr (by rw [← on_map_statedOmega_eq Q]; rfl)), fun A => rfl⟩
  have hβe : ∀ A, ((e (β A) : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) : (ι → K) ≃ₗ[K] (ι → K)) =
        reflect Q v * (e A : (ι → K) ≃ₗ[K] (ι → K)) * reflect Q v := by
    intro A
    rw [hecoe, hecoe, hβ, map_mul, map_mul, on_pdLinEquiv_pdSym]
  obtain ⟨α', hα'e⟩ : ∃ α' : MulAut ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, ∀ A, α' (e A) = e (α A) :=
    ⟨(e.symm.trans α).trans e, fun A => by simp⟩
  have hdim' : 6 ≤ finrank K (ι → K) := by rwa [Module.finrank_fintype_fun_eq_card]
  have hfix' : ∀ g : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, (g : (ι → K) ≃ₗ[K] (ι → K)) v = v → α' g = g := by
    intro g hg
    obtain ⟨A, rfl⟩ := e.surjective g
    rw [hα'e]
    congr 1
    refine hfix A (e.injective (Subtype.ext ?_))
    rw [hβe]
    have hgO : ((e A : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆) : (ι → K) ≃ₗ[K] (ι → K)) ∈
          TauCeti.QuadraticMap.orthogonalGroup Q := on_commutator_le_self _ (e A).2
    have h1 := reflect_conj hgO v
    rw [hg] at h1
    calc reflect Q v * ((e A : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆) : (ι → K) ≃ₗ[K] (ι → K)) * reflect Q v =
        reflect Q v * (((e A : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆) : (ι → K) ≃ₗ[K] (ι → K)) * reflect Q v *
          ((e A : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
            TauCeti.QuadraticMap.orthogonalGroup Q⁆) : (ι → K) ≃ₗ[K] (ι → K))⁻¹) *
            ((e A : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
              TauCeti.QuadraticMap.orthogonalGroup Q⁆) : (ι → K) ≃ₗ[K] (ι → K)) := by group
      _ = _ := by rw [h1, reflect_mul_self, one_mul]
  have hcomm' : ∀ g h : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      (h : (ι → K) ≃ₗ[K] (ι → K)) = reflect Q v * g * reflect Q v →
        ((α' h : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆) : (ι → K) ≃ₗ[K] (ι → K)) =
          reflect Q v * α' g * reflect Q v := by
    intro g h hgh
    obtain ⟨A, rfl⟩ := e.surjective g
    have hh : h = e (β A) := Subtype.ext (by rw [hβe, hgh])
    rw [hh, hα'e, hα'e, hcomm, hβe]
  rcases eq_one_or_eq_conj_reflect_of_commute_conj
      (Ω := ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
      hK hQ hdim' hv (on_commutator_le_self _)
      (fun hx hy => reflect_mul_reflect_mem_commutator hK hQ hdim' hx hy)
      (fun g hg => on_reflect_conj_mem_commutator v hg) α' hfix' hcomm' with h | h
  · left
    refine MulEquiv.ext fun A => e.injective ?_
    rw [← hα'e, h]
    rfl
  · right
    refine MulEquiv.ext fun A => e.injective (Subtype.ext ?_)
    rw [← hα'e, h, hβe]

end Mat

theorem omegaPlusOverlapTwist_two : OmegaPlusOverlapTwist 2 := by
  intro K _ _ _ hK α hfix hcomm
  exact on_eq_one_or_eq_of_commute_mat hK (quadPlus (2 + 1) K) (coe_quadPlus (2 + 1) K)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (2 + 1) K) (by simp)
    (kOmega_quadPlus_vec K 2) (kOmegaBetaC K 2) α
    (fun A => pd_coe_omegaSymmetryAut _ (quadPlus (2 + 1) K) (coe_quadPlus (2 + 1) K)
      (kOmega_matrixDerivedScalars_eq_bot K 2) (kOmega_quadPlus_vec K 2) A)
    (fun A hA => hfix A hA) hcomm

theorem omegaMinusOverlapTwist_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (α : MulAut (StatedOmega (StatedQuadMinus (2 + 1) K 1 1)))
    (hfix : ∀ g ∈ fixedSubgroup (kOmMBetaC K 2 1 1), α g = g)
    (hcomm : ∀ g, α (kOmMBetaC K 2 1 1 g) = kOmMBetaC K 2 1 1 (α g)) :
    α = 1 ∨ α = kOmMBetaC K 2 1 1 :=
  on_eq_one_or_eq_of_commute_mat hK (quadMinus (2 + 1) K 1 1) (coe_quadMinus (2 + 1) K 1 1)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (2 + 1) K
      (q2Omega_irreducible_one_one hK)) (by simp) (kOmM_quadMinus_vec K 2) (kOmMBetaC K 2 1 1) α
    (fun A => pd_coe_omegaSymmetryAut _ (quadMinus (2 + 1) K 1 1) (coe_quadMinus (2 + 1) K 1 1)
      (kOmM_matrixDerivedScalars_eq_bot K 2 1 1) (kOmM_quadMinus_vec K 2) A)
    (fun A hA => hfix A hA) hcomm

end CFSG.SeitzReduction.SymplecticPilot
