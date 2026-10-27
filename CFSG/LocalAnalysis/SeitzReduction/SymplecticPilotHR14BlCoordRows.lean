module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlCoordCoset

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)

theorem rank_eq_one_of_linearClassCoord {κ : Sp2mKind} (h1 : SpOmegaStepOneInput κ)
    (hB : SpOmegaBClassExclusionCoord κ)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hn : 4 ≤ n) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin n, RootKindSp e t f k κ) (hglob : SpOmegaRowGlobal e t f κ)
    (htN : t ∈ normalizer (spGlobal e : Set G)) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G))
    {K' : Type} [Field K'] [Finite K'] {Q : QuadraticForm K' (Fin (2 * (n + 1)) → K')}
    (hK' : Nat.card K' = 2 ^ f) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (n + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hImg : matrixProjectiveImage Q = ⊤) (ε : spGlobal e ≃* matrixProjectiveDerived Q)
    (hθt : ∃ (β₀ : MulAut (matrixProjectiveDerived Q)) (s₁ : matrixIsometries Q), s₁ * s₁ = 1 ∧
      β₀⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩) * β₀ =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₁))
    (β : MulAut (matrixProjectiveDerived Q)) (s : matrixIsometries Q) (hs : s * s = 1)
    (hβ : β⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) * β =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) :
    (((s : GL (Fin (2 * (n + 1))) K') : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K') -
      1).rank = 1 := by
  rcases Nat.even_or_odd (((s : GL (Fin (2 * (n + 1))) K') :
      Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K') - 1).rank with hev | hodd
  · exact (false_of_linearClass_of_even h1 hset hn hKc hf e ht hKt hroot hglob hg hK' hQ hT ε β
      s hev hβ).elim
  · by_contra h1'
    obtain ⟨j, hj⟩ := hodd
    exact hB G L hset n f K hn hKc hf e t ht hKt hroot hglob htN K' Q hK' hQ hT hE hImg ε hθt j
      (by omega) g hg ⟨β, s, hs, hj, hβ⟩

theorem spGraphStandardClassInput_omegaMinus_of_coord (h1 : SpOmegaStepOneInput .omegaMinus)
    (hB : SpOmegaBClassExclusionCoord .omegaMinus) : SpGraphStandardClassInput .omegaMinus := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob htN g hg
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hty : LieModel (spGlobal e) .POmegaMinus (n + 1) 2 f := hglob.1
  obtain ⟨K', _, _, b, c, hirr, ε, hK', hlinα⟩ :=
    exists_isometry_eq_of_lieModel_minus (by omega) hty
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hreg := regular_coordinateQuadMinus (n + 1) K' b c (by omega) hirr
  have hE := commutator_coordinateQuadMinus (n + 1) K' b c (by omega) hirr
  have hImg := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K'
    (n + 1) (by omega) b c hirr
  have hg1 : (1 : G)⁻¹ * t * 1 ∈ normalizer (spGlobal e : Set G) := by simpa using htN
  obtain ⟨s, hs, hsα⟩ := hlinα _ (normalizerMonoidHom_mul_self (mul_self_inv_conj_eq_one htt g) hg)
  obtain ⟨s₀, hs₀, hs₀α⟩ :=
    hlinα _ (normalizerMonoidHom_mul_self (mul_self_inv_conj_eq_one htt 1) hg1)
  have hsα' : (1 : MulAut _)⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom
      ⟨g⁻¹ * t * g, hg⟩) * 1 = matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) := by
    rw [inv_one, one_mul, mul_one]
    exact hsα
  have hs₀α' : (1 : MulAut _)⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom
      ⟨(1 : G)⁻¹ * t * 1, hg1⟩) * 1 =
        matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s₀) := by
    rw [inv_one, one_mul, mul_one]
    exact hs₀α
  have hθt : ∃ (β₀ : MulAut _) (s₁ : matrixIsometries _), s₁ * s₁ = 1 ∧
      β₀⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩) * β₀ =
        matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s₁) := by
    refine ⟨1, s₀, hs₀, ?_⟩
    rw [← normalizerMonoidHom_one_conj_eq htN hg1]
    exact hs₀α'
  have r1 := rank_eq_one_of_linearClassCoord h1 hB hset hn hKc hf e ht hKt hroot hglob htN hg hK'
    hreg.1 hreg.2 hE hImg ε hθt 1 s hs hsα'
  have r0 := rank_eq_one_of_linearClassCoord h1 hB hset hn hKc hf e ht hKt hroot hglob htN hg1 hK'
    hreg.1 hreg.2 hE hImg ε hθt 1 s₀ hs₀ hs₀α'
  obtain ⟨γ, hγ⟩ := exists_conj_of_rank_eq_one hreg.1 hreg.2 hs hs₀ r1 r0
  rw [normalizerMonoidHom_one_conj_eq htN hg1] at hs₀α'
  exact exists_conj_of_linearClass_conj ε hsα' hs₀α' hγ

theorem spGraphStandardClassInput_omegaPlus_of_coord (hU18 : OmegaMinusSpNonembeddingInput)
    (h1 : SpOmegaStepOneInput .omegaPlus) (hB : SpOmegaBClassExclusionCoord .omegaPlus) :
    SpGraphStandardClassInput .omegaPlus := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob htN g hg
  have hty : LieModel (spGlobal e) .POmegaPlus (n + 1) 2 f := hglob.1
  have hC := CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel
    (by decide) hty
  obtain ⟨-, K', _, _, hK', ⟨e'⟩⟩ := hC
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hreg := regular_coordinateQuadPlus (n + 1) K' (by omega)
  have hE := commutator_coordinateQuadPlus (n + 1) K' (by omega)
  have hImg := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K'
    (n + 1) (by omega)
  have hconj : ∀ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus (n + 1) K')),
      α * α = 1 → ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage (coordinateQuadPlus (n + 1) K') :=
    fun α _ => ⟨1, by rw [hImg]; exact Subgroup.mem_top _⟩
  have hg1 : (1 : G)⁻¹ * t * 1 ∈ normalizer (spGlobal e : Set G) := by simpa using htN
  obtain ⟨β, s, hs, hβ⟩ := exists_conj_linear_of_conj_of_input hU18 hset hn hKc (by omega) e ht
    hKt hK' hreg.1 hreg.2 hE hconj (coordinatePlusWitnessEquiv K' e') hg
  obtain ⟨β₀, s₀, hs₀, hβ₀⟩ := exists_conj_linear_of_conj_of_input hU18 hset hn hKc (by omega) e
    ht hKt hK' hreg.1 hreg.2 hE hconj (coordinatePlusWitnessEquiv K' e') hg1
  have hθt : ∃ (β₀ : MulAut _) (s₁ : matrixIsometries _), s₁ * s₁ = 1 ∧
      β₀⁻¹ * MulAut.congr (coordinatePlusWitnessEquiv K' e')
        ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩) * β₀ =
        matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s₁) := by
    refine ⟨β₀, s₀, hs₀, ?_⟩
    rw [← normalizerMonoidHom_one_conj_eq htN hg1]
    exact hβ₀
  have r1 := rank_eq_one_of_linearClassCoord h1 hB hset hn hKc hf e ht hKt hroot hglob htN hg hK'
    hreg.1 hreg.2 hE hImg _ hθt β s hs hβ
  have r0 := rank_eq_one_of_linearClassCoord h1 hB hset hn hKc hf e ht hKt hroot hglob htN hg1 hK'
    hreg.1 hreg.2 hE hImg _ hθt β₀ s₀ hs₀ hβ₀
  obtain ⟨γ, hγ⟩ := exists_conj_of_rank_eq_one hreg.1 hreg.2 hs hs₀ r1 r0
  rw [normalizerMonoidHom_one_conj_eq htN hg1] at hβ₀
  exact exists_conj_of_linearClass_conj _ hβ hβ₀ hγ

theorem spOmegaRowUniqueInput_omegaMinus_of_coord (hA2 : SpOmegaLagrangianATwoInput .omegaMinus)
    (hB : SpOmegaBClassExclusionCoord .omegaMinus) : SpOmegaRowUniqueInput .omegaMinus :=
  spOmegaRowUniqueInput_of_standardClass (spGraphStandardClassInput_omegaMinus_of_coord
    (spOmegaStepOneInput_of_aTwo (Or.inr rfl) hA2) hB)

theorem spOmegaRowUniqueInput_omegaPlus_of_coord (hU18 : OmegaMinusSpNonembeddingInput)
    (hA2 : SpOmegaLagrangianATwoInput .omegaPlus) (hB : SpOmegaBClassExclusionCoord .omegaPlus) :
    SpOmegaRowUniqueInput .omegaPlus :=
  spOmegaRowUniqueInput_of_standardClass (spGraphStandardClassInput_omegaPlus_of_coord hU18
    (spOmegaStepOneInput_of_aTwo (Or.inl rfl) hA2) hB)

end CFSG.SeitzReduction.SymplecticPilot
