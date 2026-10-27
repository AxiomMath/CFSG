module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowMinusOut

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)

theorem eq_one_or_eq_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {κ β : C}
    (hκ : κ ≠ 1) (hκ2 : κ ^ 2 = 1) (hβ2 : β ^ 2 = 1) : β = 1 ∨ β = κ := by
  classical
  have := Fintype.ofFinite C
  by_contra h
  push Not at h
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, κ, β} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact hκ2
    · exact hβ2
  have h3 : ({1, κ, β} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h.2)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hκ, Ne.symm h.1⟩
  have := Finset.card_le_card hsub
  omega

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem exists_isometry_eq_of_cyclic_complement {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hinj : Function.Injective
      ((matrixProjectiveConjugationHom Q).comp (matrixIsometryInclusion Q)))
    {v : Fin d → K} (hκout : symmetryAut Q v ∉
      (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range)
    (C : Subgroup (MulAut (matrixProjectiveDerived Q))) (hCcyc : IsCyclic C)
    (hCInn : ∀ β ∈ C, β ∈ (MulAut.conj : matrixProjectiveDerived Q →*
      MulAut (matrixProjectiveDerived Q)).range → β = 1)
    (hNF : ∀ α, ∃ g, ∃ β ∈ C, α = MulAut.conj g * β) (hvC : symmetryAut Q v ∈ C)
    {α : MulAut (matrixProjectiveDerived Q)} (hαα : α * α = 1) :
    ∃ s : matrixIsometries Q, s * s = 1 ∧
      α = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) := by
  have := finite_mulAut_matrixProjectiveDerived Q
  obtain ⟨y, β, hβC, rfl⟩ := hNF α
  have h1 : MulAut.conj y * β * (MulAut.conj y * β) =
      MulAut.conj (y * β y) * (β * β) := by
    calc MulAut.conj y * β * (MulAut.conj y * β) =
        MulAut.conj y * (β * MulAut.conj y) * β := by group
      _ = MulAut.conj y * (MulAut.conj (β y) * β) * β := by
        rw [RankThree.CASymplecticSubfield.mul_conj_eq β y]
      _ = MulAut.conj (y * β y) * (β * β) := by rw [map_mul]; group
  have hβ2 : β * β = 1 := by
    have h2 : MulAut.conj (y * β y) * (β * β) = 1 := h1 ▸ hαα
    have h3 : β * β = MulAut.conj (y * β y)⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right h2
    exact hCInn (β * β) (mul_mem hβC hβC) ⟨_, h3.symm⟩
  have hκ1 : symmetryAut Q v ≠ 1 := by
    intro h
    apply hκout
    rw [h]
    exact ⟨1, map_one _⟩
  have : IsCyclic C := hCcyc
  have hcases := eq_one_or_eq_of_isCyclic (C := C) (κ := ⟨_, hvC⟩) (β := ⟨β, hβC⟩)
    (fun h => hκ1 (congrArg Subtype.val h)) (Subtype.ext (symmetryAut_sq Q v))
    (Subtype.ext (by rw [pow_two]; exact hβ2))
  obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q y
  have hs₀ : MulAut.conj (matrixProjectiveProjection Q g) =
      matrixProjectiveConjugationHom Q
        (matrixIsometryInclusion Q (Subgroup.inclusion (matrixDerived_le_isometries Q) g)) :=
    (kappa_derived_eq_conj g).symm
  have hκs : ∀ s : matrixIsometries Q,
      MulAut.conj (matrixProjectiveProjection Q g) * β =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) →
      ∃ s : matrixIsometries Q, s * s = 1 ∧ MulAut.conj (matrixProjectiveProjection Q g) * β =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) := by
    intro s hs
    refine ⟨s, hinj ?_, hs⟩
    change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q (s * s)) =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q 1)
    rw [map_mul, map_mul, ← hs, hαα, map_one, map_one]
  rcases hcases with h | h
  · have hβ1 : β = 1 := congrArg Subtype.val h
    refine hκs (Subgroup.inclusion (matrixDerived_le_isometries Q) g) ?_
    rw [hβ1, mul_one, hs₀]
  · have hβκ : β = symmetryAut Q v := congrArg Subtype.val h
    refine hκs (Subgroup.inclusion (matrixDerived_le_isometries Q) g * symmetryIsometry Q v) ?_
    rw [hβκ, hs₀, map_mul, map_mul]

theorem exists_isometry_eq_of_mul_self_minus {f N : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hN : 4 ≤ N) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadMinus N K (by omega) b c))}
    (hαα : α * α = 1) :
    ∃ s : matrixIsometries (coordinateQuadMinus N K (by omega) b c), s * s = 1 ∧
      α = matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) := by
  have hreg := regular_coordinateQuadMinus N K b c hN hirr
  have hE := commutator_coordinateQuadMinus N K b c hN hirr
  obtain ⟨-, -, -, -, -, -, -, hinj, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.evenOrthogonalRealization_of_regular hf hK
      (by omega) _ hreg.1 hreg.2 hE
  obtain ⟨v, hv, C, hCcyc, hCInn, hNF, hvC⟩ := omegaMinusOutInput_holds K N hN b c hirr
  exact exists_isometry_eq_of_cyclic_complement hinj
    (F4Pilot.symmetryAut_not_mem_inner_of_regular hreg.1 hreg.2 hE hv) C hCcyc hCInn hNF hvC hαα

omit [Finite K] [CharP K 2] in
theorem exists_isometry_eq_of_lieModel_minus {G₀ : Type} [Group G₀] {n f : ℕ} (hn : 3 ≤ n)
    (hty : LieModel G₀ .POmegaMinus (n + 1) 2 f) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (b c : K') (_ : ∀ s : K', s ^ 2 + b * s + c ≠ 0)
      (ε : G₀ ≃* matrixProjectiveDerived (coordinateQuadMinus (n + 1) K' (by omega) b c)),
      Nat.card K' = 2 ^ f ∧ ∀ α : MulAut G₀, α * α = 1 →
        ∃ s : matrixIsometries (coordinateQuadMinus (n + 1) K' (by omega) b c), s * s = 1 ∧
          MulAut.congr ε α = matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) := by
  have hC := CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel
    (by decide) hty
  obtain ⟨⟨-, hf1, hn4'⟩, K', _, _, hK', b, c, hirr, ⟨eE⟩⟩ := hC
  have hn4 : 4 ≤ n + 1 := hn4'
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  refine ⟨K', inferInstance, inferInstance, b, c, hirr,
    coordinateMinusWitnessEquiv K' (by omega) b c eE, hK', fun α hαα => ?_⟩
  exact exists_isometry_eq_of_mul_self_minus hf1 hK' hn4 hirr
    (by rw [← map_mul, hαα, map_one])

end CFSG.SeitzReduction.SymplecticPilot
