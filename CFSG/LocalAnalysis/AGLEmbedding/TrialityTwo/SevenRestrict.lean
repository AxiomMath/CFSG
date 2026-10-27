module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenCoord
public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenFixed

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Seven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open scoped Pointwise

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {t : Module.End K V}

@[expose] def levStab (Q : QuadraticForm K V) (t : Module.End K V) (F : Frame Q t) :
    Subgroup (V ≃ₗ[K] V) :=
  TauCeti.QuadraticMap.orthogonalGroup Q ⊓ MulAction.stabilizer (V ≃ₗ[K] V) F.w₁ ⊓
    MulAction.stabilizer (V ≃ₗ[K] V) F.w₂ ⊓ MulAction.stabilizer (V ≃ₗ[K] V) (spU₁ t) ⊓
      MulAction.stabilizer (V ≃ₗ[K] V) (spU₂ t)

theorem mem_levStab {F : Frame Q t} {σ : V ≃ₗ[K] V} :
    σ ∈ levStab Q t F ↔ σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ σ F.w₁ = F.w₁ ∧
      σ F.w₂ = F.w₂ ∧ (spU₁ t).map (σ : V →ₗ[K] V) = spU₁ t ∧
        (spU₂ t).map (σ : V →ₗ[K] V) = spU₂ t := by
  simp only [levStab, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, and_assoc]
  exact Iff.rfl

section Restrict

variable [FiniteDimensional K V] (hV : finrank K V = 2 * 4) (h7 : t ^ 7 = 1) (h2 : (2 : K) = 0)
  (hQt : ∀ v, Q (t v) = Q v) (F : Frame Q t)

omit [FiniteDimensional K V] in
theorem apply_e_mem {σ : V ≃ₗ[K] V} (hσ : σ ∈ levStab Q t F) (i : Fin 3) :
    σ (F.e i) ∈ spU₁ t := by
  have h := (mem_levStab.1 hσ).2.2.2.1
  rw [← h]
  exact Submodule.mem_map_of_mem (F.mem_U₁ i)

omit [FiniteDimensional K V] in
theorem apply_f_mem {σ : V ≃ₗ[K] V} (hσ : σ ∈ levStab Q t F) (i : Fin 3) :
    σ (F.f i) ∈ spU₂ t := by
  have h := (mem_levStab.1 hσ).2.2.2.2
  rw [← h]
  exact Submodule.mem_map_of_mem (F.mem_U₂ i)

include hV h7 h2 hQt in
@[expose] noncomputable def restrictHom : levStab Q t F →* Matrix (Fin 3) (Fin 3) K where
  toFun σ := Matrix.of fun j i => polar Q ((σ : V ≃ₗ[K] V) (F.e i)) (F.f j)
  map_one' := by
    ext j i
    rw [Matrix.of_apply, Subgroup.coe_one, LinearEquiv.coe_one, id, F.polar_e_f, Matrix.one_apply]
    simp only [eq_comm]
  map_mul' σ τ := by
    ext j i
    rw [Matrix.of_apply, Matrix.mul_apply]
    simp only [Matrix.of_apply, Subgroup.coe_mul, LinearEquiv.mul_apply]
    conv_lhs => rw [eq_sum_of_mem_spU₁ hV h7 h2 hQt F (apply_e_mem F τ.2 i)]
    simp only [map_sum, map_smul]
    rw [CFSG.LocalAnalysis.ComponentInitial.polar_sum_smul_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem restrictHom_apply (σ : levStab Q t F) (i j : Fin 3) :
    restrictHom hV h7 h2 hQt F σ j i = polar Q ((σ : V ≃ₗ[K] V) (F.e i)) (F.f j) := rfl

@[expose] noncomputable def restrictGL : levStab Q t F →* GL (Fin 3) K :=
  (restrictHom hV h7 h2 hQt F).toHomUnits

theorem coe_restrictGL (σ : levStab Q t F) :
    (restrictGL hV h7 h2 hQt F σ : Matrix (Fin 3) (Fin 3) K) = restrictHom hV h7 h2 hQt F σ :=
  rfl

theorem restrictGL_injective : Function.Injective (restrictGL hV h7 h2 hQt F) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hM : restrictHom hV h7 h2 hQt F σ = 1 := by
    rw [← coe_restrictGL, hσ, Units.val_one]
  obtain ⟨hO, h₁, h₂, -, -⟩ := mem_levStab.1 σ.2
  have he : ∀ i, (σ : V ≃ₗ[K] V) (F.e i) = F.e i := by
    intro i
    rw [eq_sum_of_mem_spU₁ hV h7 h2 hQt F (apply_e_mem F σ.2 i)]
    conv_rhs => rw [eq_sum_of_mem_spU₁ hV h7 h2 hQt F (x := F.e i) (F.mem_U₁ i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [← restrictHom_apply hV h7 h2 hQt F σ i k, hM, F.polar_e_f, Matrix.one_apply]
    simp only [eq_comm]
  have hf : ∀ j, (σ : V ≃ₗ[K] V) (F.f j) = F.f j := by
    intro j
    rw [eq_sum_of_mem_spU₂ hV h7 h2 hQt F (apply_f_mem F σ.2 j)]
    conv_rhs => rw [eq_sum_of_mem_spU₂ hV h7 h2 hQt F (y := F.f j) (F.mem_U₂ j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hp : polar Q ((σ : V ≃ₗ[K] V) (F.f j)) (F.e k) = polar Q (F.f j) (F.e k) := by
      conv_lhs => rw [← he k]
      exact polar_map_of_mem hO _ _
    rw [hp]
  obtain ⟨bb, hbb⟩ := exists_basis_of_hyp F.polar_lr F.polar_ll F.polar_rr hV
  apply Subtype.ext
  rw [Subgroup.coe_one]
  refine bb.ext' fun z => ?_
  rw [hbb, LinearEquiv.coe_one, id]
  rcases z with i | i
  · induction i using Fin.lastCases with
    | last => exact h₁
    | cast i => exact he i
  · induction i using Fin.lastCases with
    | last => exact h₂
    | cast i => exact hf i

end Restrict

end CFSG.AGLEmbedding.TrialityTwo.Seven
