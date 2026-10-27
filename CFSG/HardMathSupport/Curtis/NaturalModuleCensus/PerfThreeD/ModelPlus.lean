module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.Model
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthModel

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open Module QuadraticMap CFSG.AGLEmbedding.ToralCensus CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

theorem exists_totallySingular_quadPlus (r : ℕ) (K : Type) [Field K] :
    ∃ U : Submodule K (Fin r ⊕ Fin r → K), finrank K U = r ∧ ∀ u ∈ U, quadPlus r K u = 0 := by
  have hli : LinearIndependent K (fun i : Fin r =>
      (Pi.basisFun K (Fin r ⊕ Fin r)) (Sum.inl i)) :=
    (Pi.basisFun K (Fin r ⊕ Fin r)).linearIndependent.comp _ Sum.inl_injective
  refine ⟨Submodule.span K (Set.range fun i : Fin r => Pi.basisFun K (Fin r ⊕ Fin r) (.inl i)),
    ?_, ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · intro u hu
    have hz : ∀ j : Fin r, u (.inr j) = 0 := by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu (p := fun u _ => ∀ j : Fin r, u (.inr j) = 0)
      · rintro _ ⟨i, rfl⟩ j
        simp [Pi.basisFun_apply]
      · intro j; rfl
      · intro a b _ _ ha hb j
        simp [ha j, hb j]
      · intro c a _ ha j
        simp [ha j]
    rw [quadPlus_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [hz i, mul_zero]

theorem exists_mulEquiv_stated_of_model_pomegaPlus {X : Type} [Group X] {r : ℕ}
    (h : StatedClassicalModel X .POmegaPlus r 2 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ∧
      Nonempty (X ≃* StatedProj (StatedOmega (StatedQuadPlus r K))) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have := Fintype.ofFinite K
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK])
  exact ⟨K, inferInstance, inferInstance, hchar, by simpa using hK, ⟨e⟩⟩

noncomputable def statedProjEquivDerivedQuadPlus (r : ℕ) (hr : 1 ≤ r) (K : Type) [Field K]
    [CharP K 2] :
    StatedProj (StatedOmega (StatedQuadPlus r K)) ≃*
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)⁆ :=
  haveI : Nonempty (Fin r ⊕ Fin r) := ⟨.inl ⟨0, by omega⟩⟩
  statedProjOmegaEquivDerivedCharTwo (coe_quadPlus r K) (nondegenerate_polarBilin_quadPlus r K)

open Matrix in
theorem statedProjEquivDerivedQuadPlus_mk (r : ℕ) (hr : 1 ≤ r) (K : Type) [Field K] [CharP K 2]
    (A : StatedOmega (StatedQuadPlus r K)) (w : Fin r ⊕ Fin r → K) :
    ((statedProjEquivDerivedQuadPlus r hr K (QuotientGroup.mk A) :
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)⁆) : (Fin r ⊕ Fin r → K) ≃ₗ[K]
          (Fin r ⊕ Fin r → K)) w =
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w := by
  rfl


theorem perfThreeCent_of_model_pomegaPlus {X : Type} [Group X] {r : ℕ} (hr : 5 ≤ r)
    (h : StatedClassicalModel X .POmegaPlus r 2 1) (v : X) (hv : v ^ 3 = 1) : PerfThreeCent v := by
  obtain ⟨K, _, _, _, hK, ⟨e0⟩⟩ := exists_mulEquiv_stated_of_model_pomegaPlus h
  have : Nonempty (Fin r ⊕ Fin r) := ⟨.inl ⟨0, by omega⟩⟩
  let e := e0.trans (statedProjEquivDerivedQuadPlus r (by omega) K)
  have hdim : finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]
  refine PerfThreeCent.of_mulEquiv e ?_
  refine perfThreeCent_orthDerived (nondegenerate_polarBilin_quadPlus r K) _ ?_
    (fun hx => perfectThreeIn_isometryCentralizer_card_two hK hx hdim
      (exists_totallySingular_quadPlus r K) (by omega) (by omega))
  rw [← map_pow, hv, map_one]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
