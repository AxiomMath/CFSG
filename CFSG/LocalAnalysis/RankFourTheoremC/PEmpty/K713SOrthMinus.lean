module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SOrth
import CFSG.Blueprint.SourceClassicalTransportOrthogonal

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.RankThree.Classical.SteinbergBY
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)

theorem coordinateQuadMinus_fieldAut_of_fixed {K : Type} [Field K] (n : ℕ) (hn : 1 ≤ n)
    {σ : K ≃+* K} {b c : K} (hb : σ b = b) (hc : σ c = c) (v : Fin (2 * n) → K) :
    coordinateQuadMinus n K hn b c (coordinateFieldMap (2 * n) σ v) =
      σ (coordinateQuadMinus n K hn b c v) := by
  rw [coordinateQuadMinus_apply, coordinateQuadMinus_apply]
  simp [coordinateFieldMap_apply, map_sum, map_mul, map_add, map_pow, hb, hc]

@[expose] noncomputable def fieldPairSubHom {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (H : Subgroup (K ≃+* K))
    (hQ : ∀ σ ∈ H, ∀ v : Fin d → K, Q (coordinateFieldMap d σ v) = σ (Q v)) :
    H →* similarityPairs Q where
  toFun σ := CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair Q σ.1 (hQ σ.1 σ.2)
  map_one' := Subtype.ext (SemidirectProduct.ext rfl rfl)
  map_mul' σ τ := Subtype.ext (SemidirectProduct.ext (by
    change (1 : GL (Fin d) K) = 1 * (glFieldAut (Fin d) K σ.1) 1
    simp) rfl)

theorem rootFree_of_odd_finrank {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hdeg : Odd (Module.finrank k K)) (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (s : K) : s ^ 2 + (b : K) * s + (c : K) ≠ 0 := by
  intro hs
  have hfd : FiniteDimensional k K := Module.finite_of_finrank_pos hdeg.pos
  have hint : IsIntegral k s := Algebra.IsIntegral.isIntegral s
  have h1 := minpoly.degree_dvd hint
  have hmon : (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c :
      Polynomial k).Monic := by monicity!
  have hdvd : minpoly k s ∣ (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c :
      Polynomial k) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_def]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    exact hs
  have h2 : (minpoly k s).natDegree ≤ 2 :=
    (Polynomial.natDegree_le_of_dvd hdvd hmon.ne_zero).trans (by compute_degree!)
  have h3 : Odd (minpoly k s).natDegree := Odd.of_dvd_nat hdeg h1
  have h5 : 0 < (minpoly k s).natDegree := minpoly.natDegree_pos hint
  have h4 : (minpoly k s).natDegree = 1 := by
    obtain ⟨m, hm⟩ := h3
    omega
  obtain ⟨s₀, hs₀⟩ := minpoly.natDegree_eq_one_iff.mp h4
  apply hirr s₀
  apply Subtype.ext
  have : ((s₀ : K)) = s := hs₀
  push_cast
  rw [this]
  exact hs

theorem exists_fixed_rootFree_quadratic {K : Type} [Field K] [Finite K]
    (H : Subgroup (K ≃+* K)) (hodd : Odd (Nat.card H)) :
    ∃ b c : K, (∀ σ ∈ H, σ b = b ∧ σ c = c) ∧ ∀ s : K, s ^ 2 + b * s + c ≠ 0 := by
  haveI := finite_ringAut K
  haveI : Fintype H := Fintype.ofFinite H
  have hdeg : Module.finrank (FixedPoints.subfield H K) K = Nat.card H := by
    rw [Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card H K
  obtain ⟨b, c, hbc⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic
    (FixedPoints.subfield H K)
  refine ⟨b, c, fun σ hσ => ⟨?_, ?_⟩,
    rootFree_of_odd_finrank (FixedPoints.subfield H K) (hdeg ▸ hodd) b c hbc⟩
  · exact b.2 ⟨σ, hσ⟩
  · exact c.2 ⟨σ, hσ⟩

theorem liftClause_classical_POmegaMinus {n p f : ℕ} :
    FamilyLift fun S _ => StatedClassicalModel S .POmegaMinus n p f := by
  intro S _ _ _ hnonab h ℓ hℓ hℓ2 hSℓ
  have h0 := h
  obtain ⟨⟨hp, hf, hn4⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hn1 : 1 ≤ n := by omega
  haveI := finite_ringAut K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨P⟩ : Nonempty (Sylow ℓ (K ≃+* K)) := inferInstance
  have hcard : Nat.card (P : Subgroup (K ≃+* K)) = ℓ ^ (Nat.card (K ≃+* K)).factorization ℓ :=
    P.card_eq_multiplicity
  have hodd : Odd (Nat.card (P : Subgroup (K ≃+* K))) := by
    rw [hcard]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨b', c', hfix, hirr'⟩ := exists_fixed_rootFree_quadratic (P : Subgroup (K ≃+* K)) hodd
  obtain ⟨e'⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv hn1 hirr hirr'
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates S .POmegaMinus
    (Or.inr (Or.inr rfl)) n p f h hn1 K hK b' c' hirr' (e.trans e')
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn4
    b' c' hirr'
  haveI : Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b' c')) :=
    Finite.of_equiv S (coordinateMinusWitnessEquiv K hn1 b' c' (e.trans e')).toEquiv
  refine OutLift.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b' c' (e.trans e')) ?_
  refine outLift_of_orthogonalGates (coordinateQuadMinus n K hn1 b' c') hℓ hℓ2 hg
    (by rw [htop, Subgroup.index_top]; exact hℓ.not_dvd_one) (P : Subgroup (K ≃+* K)) ?_
    (fieldPairSubHom _ (P : Subgroup (K ≃+* K)) fun σ hσ v =>
      coordinateQuadMinus_fieldAut_of_fixed n hn1 (hfix σ hσ).1 (hfix σ hσ).2 v) fun σ => rfl
  rw [hcard, Nat.Prime.factorization_pow hℓ, Finsupp.single_eq_same]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
