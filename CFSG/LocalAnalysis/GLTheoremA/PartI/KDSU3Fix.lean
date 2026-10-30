module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPolarRecovery
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix

variable {n : ℕ} {K : Type} [Field K]

private theorem exists_fixed_isotropic_core (h : UnitaryFieldData 2 n K)
    {B : (Fin 3 → K) →ₛₗ[h.bar] (Fin 3 → K) →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {M : Matrix (Fin 3) (Fin 3) K} (hM2 : M * M = 1)
    (hiso : ∀ x y, B (M *ᵥ x) (M *ᵥ y) = B x y) {x₀ : Fin 3 → K} (hx₀ : M *ᵥ x₀ ≠ x₀) :
    ∃ w : Fin 3 → K, w ≠ 0 ∧ B w w = 0 ∧ M *ᵥ w = w ∧
      ∀ v : Fin 3 → K, v ≠ 0 → B v v = 0 → ∀ μ : K, M *ᵥ v = μ • v → ∃ c : K, v = c • w := by
  have h2 : CharP K 2 := h.charP
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → K, w = M *ᵥ x₀ + x₀ := ⟨_, rfl⟩
  have hMM : ∀ x : Fin 3 → K, M *ᵥ (M *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hM2, Matrix.one_mulVec]
  have hMw : M *ᵥ w = w := by
    rw [hw, Matrix.mulVec_add, hMM, add_comm]
  have hw0 : w ≠ 0 := by
    intro hzero
    apply hx₀
    rw [hw] at hzero
    rw [eq_neg_of_add_eq_zero_left hzero]
    funext i
    simp [CharTwo.neg_eq]
  have hBw : ∀ y, B w (M *ᵥ y) = B w y := fun y => by
    have := hiso w y
    rwa [hMw] at this
  have hBww : B w w = 0 := by
    have e1 : B w w = B w (M *ᵥ x₀) + B w x₀ := by
      rw [← map_add, ← hw]
    rw [e1, hBw]
    exact CharTwo.add_self_eq_zero _
  refine ⟨w, hw0, hBww, hMw, ?_⟩
  intro v hv0 hvv μ hμ
  have hμ1 : μ = 1 := by
    have h1 : M *ᵥ (M *ᵥ v) = v := hMM v
    rw [hμ, Matrix.mulVec_smul, hμ, smul_smul] at h1
    have h3 : (μ * μ - 1) • v = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    have h4 : μ * μ = 1 := by
      rcases smul_eq_zero.mp h3 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv0
    rcases mul_self_eq_one_iff.mp h4 with h | h
    · exact h
    · exact h.trans (CharTwo.neg_eq 1)
  have hMv : M *ᵥ v = v := by rw [hμ, hμ1, one_smul]
  have hBv : ∀ y, B v (M *ᵥ y) = B v y := fun y => by
    have := hiso v y
    rwa [hMv] at this
  have hBvw : B v w = 0 := by
    have e1 : B v w = B v (M *ᵥ x₀) + B v x₀ := by
      rw [← map_add, ← hw]
    rw [e1, hBv]
    exact CharTwo.add_self_eq_zero _
  have hBwv : B w v = 0 := by
    have := hB.eq v w
    rwa [hBvw, map_zero, eq_comm] at this
  by_contra hcon
  push Not at hcon
  have hli : LinearIndependent K ![v, w] :=
    linearIndependent_fin2.mpr ⟨hw0, fun a ha => hcon a ha.symm⟩
  have hT : ∀ x ∈ Set.range ![v, w], ∀ y ∈ Set.range ![v, w], B x y = 0 := by
    simp only [Set.forall_mem_range, Fin.forall_fin_two]
    simp [hvv, hBvw, hBwv, hBww]
  have hle := finrank_le_of_isTotIso h hB hBl (isTotIso_span hT)
  rw [finrank_span_eq_card hli, Fintype.card_fin, Module.finrank_fin_fun] at hle
  omega

theorem exists_fixed_isotropic (h : UnitaryFieldData 2 n K) (g : GL (Fin 3) K)
    (hg : g ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    ∃ w : Fin 3 → K, w ≠ 0 ∧ gramForm h (1 : Matrix (Fin 3) (Fin 3) K) w w = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w ∧
      ∀ v : Fin 3 → K, v ≠ 0 → gramForm h (1 : Matrix (Fin 3) (Fin 3) K) v v = 0 → ∀ μ : K,
        (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = μ • v → ∃ c : K, v = c • w := by
  have hM2 : (g : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, hg2, Units.val_one]
  have hiso : ∀ x y, gramForm h (1 : Matrix (Fin 3) (Fin 3) K)
      ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ x) ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ y) =
        gramForm h (1 : Matrix (Fin 3) (Fin 3) K) x y := by
    rw [gramForm_isometry_iff]
    have := mem_primeFormUnitary.mp hg
    rwa [Units.val_one] at this
  have hne : ∃ x₀ : Fin 3 → K, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ x₀ ≠ x₀ := by
    by_contra hcon
    push Not at hcon
    apply hg1
    refine Units.ext (Matrix.ext fun a b => ?_)
    have := congrFun (hcon (Pi.single b 1)) a
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this
  obtain ⟨x₀, hx₀⟩ := hne
  exact exists_fixed_isotropic_core h
    (gramForm_isSymm h (by simp)) (gramForm_separatingLeft h (by simp)) hM2 hiso hx₀

end CFSG.LocalAnalysis.GLTheoremA
