module

public import CFSG.ClassicalInvolution.SmallOrth.PlusFourGroups
public import CFSG.ClassicalInvolution.SmallOrth.Layer
public import CFSG.ClassicalInvolution.SmallOrth.PlusFour

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap Matrix
open scoped MatrixGroups

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  [FiniteDimensional K V] {P P' : HypPair Q} (h : P.Orth P') (hdim : Module.finrank K V = 4)

theorem thetaL_mem_elementaryGroup (A : SL(2, K)) : thetaL h hdim A ∈ elementaryGroup Q := by
  refine SL2.transvection_induction (fun A => thetaL h hdim A ∈ elementaryGroup Q) ?_ ?_ A
  · intro i j hij c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [thetaL_transvection_zero_one]
      exact eichler_mem_elementaryGroup Q _ _
    · rw [thetaL_transvection_one_zero]
      exact eichler_mem_elementaryGroup Q _ _
    · exact absurd rfl hij
  · intro A B hA hB
    rw [map_mul]
    exact mul_mem hA hB

theorem thetaR_mem_elementaryGroup (A : SL(2, K)) : thetaR h hdim A ∈ elementaryGroup Q := by
  refine SL2.transvection_induction (fun A => thetaR h hdim A ∈ elementaryGroup Q) ?_ ?_ A
  · intro i j hij c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [thetaR_transvection_zero_one]
      exact eichler_mem_elementaryGroup Q _ _
    · rw [thetaR_transvection_one_zero]
      exact eichler_mem_elementaryGroup Q _ _
    · exact absurd rfl hij
  · intro A B hA hB
    rw [map_mul]
    exact mul_mem hA hB

theorem range_sup_le_orthogonalGroup :
    (thetaL h hdim).range ⊔ (thetaR h hdim).range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine sup_le ?_ ?_
  · rintro _ ⟨A, rfl⟩
    exact thetaL_mem_orthogonalGroup h hdim A
  · rintro _ ⟨A, rfl⟩
    exact thetaR_mem_orthogonalGroup h hdim A

theorem range_sup_le_elementaryGroup :
    (thetaL h hdim).range ⊔ (thetaR h hdim).range ≤ elementaryGroup Q := by
  refine sup_le ?_ ?_
  · rintro _ ⟨A, rfl⟩
    exact thetaL_mem_elementaryGroup h hdim A
  · rintro _ ⟨A, rfl⟩
    exact thetaR_mem_elementaryGroup h hdim A

theorem exists_mem_range_sup_apply_e_eq_f :
    ∃ g ∈ (thetaL h hdim).range ⊔ (thetaR h hdim).range, g P.e = P.f := by
  obtain ⟨w, hw⟩ : ∃ w : SL(2, K), (w : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] :=
    ⟨⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩, rfl⟩
  refine ⟨thetaL h hdim w * thetaR h hdim w,
    mul_mem (Subgroup.mem_sup_left ⟨w, rfl⟩) (Subgroup.mem_sup_right ⟨w, rfl⟩), ?_⟩
  rw [← coord_E11, LinearEquiv.mul_apply, thetaR_apply, thetaL_apply, ← coord_E22]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hw, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem eichler_mem_range_sup {w : V} (hw : polar Q P.e w = 0) :
    eichler Q P.e w ∈ (thetaL h hdim).range ⊔ (thetaR h hdim).range := by
  obtain ⟨n, rfl⟩ := coord_surjective h hdim w
  have hn : n 1 1 = 0 := by
    have := polar_coord h !![1, 0; 0, 0] n
    rw [coord_E11, hw] at this
    simpa [pol] using this.symm
  have hdec : coord P P' n = (n 0 1 • P'.e + (-n 1 0) • P'.f) + n 0 0 • P.e := by
    rw [coord_apply, hn]
    module
  have h1 : polar Q P.e (n 0 1 • P'.e) = 0 := by rw [polar_smul_right_eq, h.ee, mul_zero]
  have h2 : polar Q P.e ((-n 1 0) • P'.f) = 0 := by rw [polar_smul_right_eq, h.ef, mul_zero]
  have h3 : eichler Q P.e ((-n 1 0) • P'.f) = eichler Q P'.f ((-(-n 1 0)) • P.e) := by
    rw [eichler_swap P.Q_e (by rw [map_smul_eq_sq, P'.Q_f, mul_zero]) h2, eichler_smul_left]
    congr 1
    module
  rw [hdec, eichler_add_smul_self P.Q_e, ← eichler_mul h1 h2, h3,
    ← thetaL_transvection_zero_one h hdim, ← thetaR_transvection_one_zero h hdim]
  exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)

theorem elementaryGroup_eq_sup (hQ : (polarBilin Q).Nondegenerate) :
    elementaryGroup Q = (thetaL h hdim).range ⊔ (thetaR h hdim).range :=
  le_antisymm
    (elementaryGroup_le_of_subgroup _ hQ (range_sup_le_orthogonalGroup h hdim)
      (fun _ hw => eichler_mem_range_sup h hdim hw) (exists_mem_range_sup_apply_e_eq_f h hdim))
    (range_sup_le_elementaryGroup h hdim)

theorem isQuasisimple_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : CFSG.Open.IsQuasisimple G) : CFSG.Open.IsQuasisimple H := by
  obtain ⟨hperf, hsimple⟩ := hG
  refine ⟨?_, ?_⟩
  · have : commutator H = (commutator G).map e.toMonoidHom := by
      rw [commutator, commutator, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]
    rw [this, hperf, Subgroup.map_top_of_surjective _ e.surjective]
  · exact (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e
      (Subgroup.map_center_eq e)).symm.isSimpleGroup

theorem isQuasisimple_specialLinearGroup_two [Finite K] (h4 : 4 ≤ Nat.card K) :
    CFSG.Open.IsQuasisimple SL(2, K) := by
  obtain ⟨a, ha, hasq⟩ := exists_ne_zero_sq_ne_one (K := K) h4
  exact ⟨SL2.commutator_eq_top ha hasq, ProjectiveSpecialLinearGroup.rank_two_simple h4⟩

theorem isQuasisimple_range_thetaL [Finite K] (h4 : 4 ≤ Nat.card K) :
    CFSG.Open.IsQuasisimple ↥(thetaL h hdim).range :=
  isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (thetaL_injective h hdim))
    (isQuasisimple_specialLinearGroup_two h4)

theorem isQuasisimple_range_thetaR [Finite K] (h4 : 4 ≤ Nat.card K) :
    CFSG.Open.IsQuasisimple ↥(thetaR h hdim).range :=
  isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (thetaR_injective h hdim))
    (isQuasisimple_specialLinearGroup_two h4)

include h hdim in
theorem exists_quasisimple_pair_of_plus_four [Finite K] (h4 : 4 ≤ Nat.card K)
    (hQ : (polarBilin Q).Nondegenerate) :
    ∃ H₁ H₂ : Subgroup (V ≃ₗ[K] V), H₁ ≤ elementaryGroup Q ∧ H₂ ≤ elementaryGroup Q ∧
      CFSG.Open.IsQuasisimple ↥H₁ ∧ CFSG.Open.IsQuasisimple ↥H₂ ∧
      elementaryGroup Q ≤ H₁ ⊔ H₂ ∧ (∀ g ∈ elementaryGroup Q, ∀ x ∈ H₁, g * x * g⁻¹ ∈ H₁) ∧
      ∀ g ∈ elementaryGroup Q, ∀ x ∈ H₂, g * x * g⁻¹ ∈ H₂ := by
  have hE := elementaryGroup_eq_sup h hdim hQ
  have hLR : (thetaR h hdim).range ≤ Subgroup.centralizer ((thetaL h hdim).range : Set _) := by
    intro y hy
    obtain ⟨B, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    exact thetaL_thetaR_comm h hdim A B
  have hRL : (thetaL h hdim).range ≤ Subgroup.centralizer ((thetaR h hdim).range : Set _) := by
    intro y hy
    obtain ⟨A, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨B, rfl⟩
    exact (thetaL_thetaR_comm h hdim A B).symm
  have hN₁ : elementaryGroup Q ≤ Subgroup.normalizer ((thetaL h hdim).range : Set (V ≃ₗ[K] V)) := by
    rw [hE]
    exact sup_le Subgroup.le_normalizer (hLR.trans (Subgroup.centralizer_le_normalizer _))
  have hN₂ : elementaryGroup Q ≤ Subgroup.normalizer ((thetaR h hdim).range : Set (V ≃ₗ[K] V)) := by
    rw [hE]
    exact sup_le (hRL.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  refine ⟨(thetaL h hdim).range, (thetaR h hdim).range, ?_, ?_,
    isQuasisimple_range_thetaL h hdim h4, isQuasisimple_range_thetaR h hdim h4, hE.le,
    fun g hg x hx => ?_, fun g hg x hx => ?_⟩
  · exact le_sup_left.trans (range_sup_le_elementaryGroup h hdim)
  · exact le_sup_right.trans (range_sup_le_elementaryGroup h hdim)
  · exact (Subgroup.mem_normalizer_iff.mp (hN₁ hg) x).mp hx
  · exact (Subgroup.mem_normalizer_iff.mp (hN₂ hg) x).mp hx

end CFSG.ClassicalGroups.Orthogonal.Small
