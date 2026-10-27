module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldDefs
public import CFSG.RankThree.PartOne.S11d.FixedFactsOrth

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedClassicalModel StatedLieAdmissible)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveImage)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus coordinatePlusWitnessEquiv coordinateMinusWitnessEquiv
    coordinate_model_witness_plus coordinate_model_witness_minus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (orthPlus_hyps orthMinus_hyps)

theorem fixesNonLocalized_pomegaPlus {T : Type} [Group T] [Finite T] {p n f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hC : StatedClassicalModel T .POmegaPlus n 2 f) {α : MulAut T}
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) : FixesNonLocalized α := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hC.1.2.1
  have hn4 : 4 ≤ n := hC.1.2.2
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hαord : orderOf α = p := orderOf_eq_prime hαp (fun h1 => hαinn (h1 ▸ (innerAut T).one_mem))
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hC
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, -, hidx⟩ := orthPlus_hyps hC K hK e
  obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_plus hC K hK e
  obtain ⟨a, ha_def⟩ : ∃ a, a = MulAut.congr (coordinatePlusWitnessEquiv K e) α := ⟨_, rfl⟩
  have ha : orderOf a = p := by
    rw [ha_def]
    exact (orderOf_congr _ α).trans hαord
  have hainn : a ∉ innerAut (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    rw [ha_def]
    exact fun h => hαinn ((mem_innerAut_congr _ α).mp h)
  have haE : a ∈ matrixProjectiveImage (coordinateQuadPlus n K) :=
    orth_mem_image_of_orderOf _ hidx hp hp3 ha
  have hap : a ^ p = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have haD : a ∉ (linearConjugationHom (coordinateQuadPlus n K)).range :=
    orth_not_mem_linearRange_of_not_inner _ hnd hS3 hp hp2 hap hainn
  obtain ⟨hpf, -⟩ := CFSG.RankThree.PartOne.orthogonal_prime_semilinear_actual_fixed_form_descent
    T .POmegaPlus (Or.inr (Or.inl rfl)) n 2 f p hC hp hp3 hp2 K hK e a haE haD ha
  obtain ⟨f₀, rfl⟩ := hpf
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · simp [h0] at hf
    · exact h0
  exact FixesNonLocalized.of_fixedFacts
    (fixedFacts_POmegaPlus hp hp5 ((lieModel_classical_iff (by decide)).mpr hC) hf₀ α hαp hαinn)

theorem fixesNonLocalized_pomegaMinus {T : Type} [Group T] [Finite T] {p n f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hC : StatedClassicalModel T .POmegaMinus n 2 f) {α : MulAut T}
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) : FixesNonLocalized α := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hC.1.2.1
  have hn4 : 4 ≤ n := hC.1.2.2
  have hn1 : 1 ≤ n := by omega
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hαord : orderOf α = p := orderOf_eq_prime hαp (fun h1 => hαinn (h1 ▸ (innerAut T).one_mem))
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id hC
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, -, hidx⟩ := orthMinus_hyps hC K hK b c hirr hn1 e
  obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_minus hC K hK b c hirr e
  obtain ⟨a, ha_def⟩ : ∃ a, a = MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) α :=
    ⟨_, rfl⟩
  have ha : orderOf a = p := by
    rw [ha_def]
    exact (orderOf_congr _ α).trans hαord
  have hainn : a ∉ innerAut (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) := by
    rw [ha_def]
    exact fun h => hαinn ((mem_innerAut_congr _ α).mp h)
  have haE : a ∈ matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) :=
    orth_mem_image_of_orderOf _ hidx hp hp3 ha
  have hap : a ^ p = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have haD : a ∉ (linearConjugationHom (coordinateQuadMinus n K hn1 b c)).range :=
    orth_not_mem_linearRange_of_not_inner _ hnd hS3 hp hp2 hap hainn
  obtain ⟨hpf, -⟩ := CFSG.RankThree.PartOne.orthogonal_prime_semilinear_actual_fixed_form_descent
    T .POmegaMinus (Or.inr (Or.inr rfl)) n 2 f p hC hp hp3 hp2 hn1 K hK b c hirr e a haE haD ha
  obtain ⟨f₀, rfl⟩ := hpf
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · simp [h0] at hf
    · exact h0
  exact FixesNonLocalized.of_fixedFacts
    (fixedFacts_POmegaMinus hp hp5 ((lieModel_classical_iff (by decide)).mpr hC) hf₀ α hαp hαinn)

end CFSG.AGLEmbedding.LieOut
