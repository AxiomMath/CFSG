module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5OmegaC
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5OmegaB

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.TwoL5.Omega

open CFSG Subgroup Module CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.CatLeafProof.X10Sp (centralModel_unitary_component)
open CFSG.ComponentClassification.SolMax.FiveCat.C5PSL (eq_psl_two_one_of_a5)
open CFSG.ComponentClassification.SolMax.FiveCat.C5Omega (le_four_of_modelIn_orthTuples)
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
  CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

@[expose] def NoAFiveComp (G : Type) [Group G] : Prop :=
  ∀ L : Subgroup G, IsComponent L → ¬ AFive ↥L

theorem NoAFiveComp.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : NoAFiveComp H) : NoAFiveComp G := fun L hL hA =>
  h _ (LocalCores.isComponent_map_mulEquiv e hL)
    (AFive.of_mulEquiv (L.equivMapOfInjective e.toMonoidHom e.injective) hA)

theorem NoAFiveComp.liftedLitUnique {G : Type} [Group G] (h : NoAFiveComp G) (P : G → Prop) :
    LiftedLitUnique P := fun M₁ _ hM₁ _ => (h M₁ hM₁.1 hM₁.2.1).elim

section Prod

variable {K : Type} [Field K] [Finite K] {W₁ W₂ : Type} [AddCommGroup W₁] [Module K W₁]
  [FiniteDimensional K W₁] [AddCommGroup W₂] [Module K W₂] [FiniteDimensional K W₂]

theorem lifted_left {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f)
    (Q₁ : QuadraticForm K W₁) (hQ₁ : Q₁.polarBilin.Nondegenerate) (Q₂ : QuadraticForm K W₂)
    {G : Type} [Group G] (e : G ≃* (↥(TauCeti.QuadraticMap.orthogonalGroup Q₁) ×
      ↥(TauCeti.QuadraticMap.orthogonalGroup Q₂))) {M : Subgroup G} (hM : IsComponent M)
    (hA : AFive ↥M) (hC : CInv ↥M) (h2 : ∀ x ∈ M, (e x).2 = 1) :
    Module.finrank K W₁ = 3 ∧ ∀ g : G, g ∈ M ↔
      (e g).2 = 1 ∧ (e g).1 ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q₁) := by
  obtain ⟨ρ, hρi, hρc, hρ⟩ := OddClassSelector.restrict_component e hM h2
  let eρ : ↥M ≃* ↥ρ.range := MonoidHom.ofInjective hρi
  have hlit : LitLayer ρ.range :=
    litLayer_iff.2 ⟨hρc, AFive.of_mulEquiv eρ hA, CInv.of_mulEquiv eρ hC⟩
  obtain ⟨hd3, hrange⟩ := finrank_eq_three_of_litLayer hf hK Q₁ hQ₁ hlit
  refine ⟨hd3, fun g => ⟨fun hg => ⟨h2 g hg, ?_⟩, fun ⟨hg2, hg1⟩ => ?_⟩⟩
  · have h1 : (e g).1 ∈ ρ.range := ⟨⟨g, hg⟩, hρ ⟨g, hg⟩⟩
    rwa [hrange] at h1
  · rw [← hrange] at hg1
    obtain ⟨m, hm⟩ := hg1
    have hm1 : (e (m : G)).1 = (e g).1 := (hρ m).symm.trans hm
    have hmg : (m : G) = g := e.injective (Prod.ext hm1 ((h2 m m.2).trans hg2.symm))
    rw [← hmg]
    exact m.2

theorem liftedLitUnique_of_prod {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f)
    (Q₁ : QuadraticForm K W₁) (hQ₁ : Q₁.polarBilin.Nondegenerate) (Q₂ : QuadraticForm K W₂)
    (hQ₂ : Q₂.polarBilin.Nondegenerate) {G : Type} [Group G]
    (e : G ≃* (↥(TauCeti.QuadraticMap.orthogonalGroup Q₁) ×
      ↥(TauCeti.QuadraticMap.orthogonalGroup Q₂))) (P : G → Prop)
    (hP₁ : ∀ x, P x → (e x).2 = 1 → x = 1) (hP₂ : ∀ x, P x → (e x).1 = 1 → x = 1)
    (hd : 7 ≤ Module.finrank K W₁ + Module.finrank K W₂) : LiftedLitUnique P := by
  have typ : ∀ M : Subgroup G, IsComponent M →
      (∀ x ∈ M, (e x).2 = 1) ∨ (∀ x ∈ M, (e x).1 = 1) := by
    intro M hM
    have hM' := LocalCores.isComponent_map_mulEquiv e hM
    rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      hM' with h | h
    · exact Or.inl fun x hx => h (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx)
    · exact Or.inr fun x hx => h (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx)
  have left : ∀ M : Subgroup G, LiftedLit P M → (∀ x ∈ M, (e x).2 = 1) →
      Module.finrank K W₁ = 3 ∧ ∀ g : G, g ∈ M ↔
        (e g).2 = 1 ∧ (e g).1 ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q₁) := by
    rintro M ⟨hc, hA, hz⟩ h2
    refine lifted_left hf hK Q₁ hQ₁ Q₂ e hc hA (fun z hzc hzz => ?_) h2
    exact Subtype.ext (hP₁ _ (hz z hzc hzz) (h2 z z.2))
  have right : ∀ M : Subgroup G, LiftedLit P M → (∀ x ∈ M, (e x).1 = 1) →
      Module.finrank K W₂ = 3 ∧ ∀ g : G, g ∈ M ↔
        (e g).1 = 1 ∧ (e g).2 ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q₂) := by
    rintro M ⟨hc, hA, hz⟩ h1
    refine lifted_left hf hK Q₂ hQ₂ Q₁ (e.trans MulEquiv.prodComm) hc hA
      (fun z hzc hzz => ?_) h1
    exact Subtype.ext (hP₂ _ (hz z hzc hzz) (h1 z z.2))
  rintro M₁ M₂ h₁ h₂
  rcases typ M₁ h₁.1 with t₁ | t₁ <;> rcases typ M₂ h₂.1 with t₂ | t₂
  · obtain ⟨-, k₁⟩ := left M₁ h₁ t₁
    obtain ⟨-, k₂⟩ := left M₂ h₂ t₂
    ext g
    rw [k₁, k₂]
  · obtain ⟨d₁, -⟩ := left M₁ h₁ t₁
    obtain ⟨d₂, -⟩ := right M₂ h₂ t₂
    omega
  · obtain ⟨d₁, -⟩ := right M₁ h₁ t₁
    obtain ⟨d₂, -⟩ := left M₂ h₂ t₂
    omega
  · obtain ⟨-, k₁⟩ := right M₁ h₁ t₁
    obtain ⟨-, k₂⟩ := right M₂ h₂ t₂
    ext g
    rw [k₁, k₂]

end Prod

theorem liftedLitUnique_orthogonalOperatorCentralizer {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 5 ^ f) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hd : 7 ≤ Module.finrank K V) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (d μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    LiftedLitUnique (fun z : ↥(orthogonalOperatorCentralizer Q A.toLinearMap) =>
      (z : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ scalarSigns Q) := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (Nat.prime_five.odd_of_ne_two (by norm_num)).pow
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨hsign, -, hsq, hnsq⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure 5 f
      Nat.prime_five (by norm_num) hf hK (by omega) Q hQ A d μ hsquare hsim hnonscalar
  by_cases hsqd : IsSquare (d : K)
  ·
    obtain ⟨r, hr⟩ := hsqd
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact d.ne_zero (by simpa using hr)
    obtain ⟨b, hb⟩ : ∃ b : Kˣ, (d : K) = (b : K) ^ 2 :=
      ⟨Units.mk0 r hr0, by rw [hr, sq]; rfl⟩
    obtain ⟨hcompl, hpne, hnne, hpos, hneg⟩ := hsq b hb
    rcases hsign with hp | hn
    ·
      obtain ⟨-, hnd₁, hnd₂, e, he₁, he₂, -⟩ := hpos hp
      have hQ₁ : (Q.comp (positiveSquareKernel A (b : K)).subtype).polarBilin.Nondegenerate := by
        rw [QuadraticMap.polarBilin_comp]
        exact hnd₁
      have hQ₂ : (Q.comp (negativeSquareKernel A (b : K)).subtype).polarBilin.Nondegenerate := by
        rw [QuadraticMap.polarBilin_comp]
        exact hnd₂
      have hdim := Submodule.finrank_add_eq_of_isCompl hcompl
      refine liftedLitUnique_of_prod hf hK _ hQ₁ _ hQ₂ e _ ?_ ?_ (by omega)
      · intro x hx h2'
        rcases hx with hx | hx
        · exact Subtype.ext hx
        · exfalso
          obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnne
          have h3 := he₂ x ⟨y, hy⟩
          rw [h2', hx] at h3
          simp only [QuadraticMap.coe_negOrthogonal] at h3
          have h4 : (2 : K) • y = 0 := by
            have h5 : y = -y := by simpa using h3
            rw [two_smul]
            nth_rewrite 1 [h5]
            exact neg_add_cancel y
          rcases smul_eq_zero.mp h4 with h6 | h6
          · exact h2 h6
          · exact hy0 h6
      · intro x hx h1'
        rcases hx with hx | hx
        · exact Subtype.ext hx
        · exfalso
          obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
          have h3 := he₁ x ⟨y, hy⟩
          rw [h1', hx] at h3
          simp only [QuadraticMap.coe_negOrthogonal] at h3
          have h4 : (2 : K) • y = 0 := by
            have h5 : y = -y := by simpa using h3
            rw [two_smul]
            nth_rewrite 1 [h5]
            exact neg_add_cancel y
          rcases smul_eq_zero.mp h4 with h6 | h6
          · exact h2 h6
          · exact hy0 h6
    ·
      obtain ⟨-, -, -, -, hdimP, -, e, -⟩ := hneg hn
      refine (NoAFiveComp.of_mulEquiv (e.trans (CatalogueBAlternatingIsometry.basisMatrixEquiv
        (Module.finBasis K (positiveSquareKernel A (b : K))))) ?_).liftedLitUnique _
      intro L hL hA
      have hmodel := centralModel_GL_component_two_le Nat.prime_five (by norm_num) hf hK
        (by omega) (Or.inl (by omega)) hL
      obtain ⟨-, hm2, -⟩ := eq_psl_two_one_of_a5 (Or.inl rfl) hmodel.1 hmodel.2 hA
      omega
  ·
    have hs := CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A d hsquare
    letI := scalarField A.toLinearMap d hsqd hs
    letI := evaluationModule A.toLinearMap
    haveI := scalarAlgebra_finite_type A.toLinearMap d hsqd hs
    haveI := evaluationModule_finite A.toLinearMap
    have hE : Nat.card (scalarAlgebra A.toLinearMap) = (5 ^ f) ^ 2 := by
      rw [scalarAlgebra_card A.toLinearMap d hsqd hs, hK]
    have hdimE := evaluationModule_finrank A.toLinearMap d hsqd hs
    rcases hsign with hp | hn
    ·
      have hadj := positive_square_adjoint Q A d μ d.ne_zero hsquare hsim hp
      refine (NoAFiveComp.of_mulEquiv
        (actualPositiveCentralizerEquiv Q A.toLinearMap d d.ne_zero hsqd hs hadj h2) ?_
        ).liftedLitUnique _
      intro L hL hA
      have hmodel := orthogonal_component_models Nat.prime_five (by norm_num) (e := 2 * f)
        (by omega) (by rw [hE, ← pow_mul, mul_comm]) _
        (actualPositiveQuadratic_nondegenerate Q A.toLinearMap d d.ne_zero hsqd hs hadj hQ h2)
        (by omega) hL
      obtain ⟨-, he⟩ := le_four_of_modelIn_orthTuples hmodel hA
      omega
    ·
      have hadj := negative_square_adjoint Q A d μ d.ne_zero hsquare hsim hn
      have hsig : (conjugation A.toLinearMap d hsqd hs).toRingEquiv ^ 2 = 1 := by
        apply RingEquiv.ext
        intro z
        change conjugation A.toLinearMap d hsqd hs (conjugation A.toLinearMap d hsqd hs z) = z
        exact conjugation_involutive A.toLinearMap d hsqd hs z
      have hne : (conjugation A.toLinearMap d hsqd hs).toRingEquiv ≠ 1 := by
        intro heq
        apply conjugation_ne_one A.toLinearMap d hsqd hs h2
        apply AlgEquiv.ext
        intro z
        exact congrArg (fun s : scalarAlgebra A.toLinearMap ≃+* scalarAlgebra A.toLinearMap =>
          s z) heq
      have hpow : ∀ z, (conjugation A.toLinearMap d hsqd hs).toRingEquiv z = z ^ (5 ^ f) := by
        intro z
        rw [← hK]
        exact conjugation_eq_card_power A.toLinearMap d hsqd hs h2 z
      refine (NoAFiveComp.of_mulEquiv
        (actualNegativeCentralizerEquiv Q A.toLinearMap d d.ne_zero hsqd hs hadj h2) ?_
        ).liftedLitUnique _
      intro L hL hA
      have hmodel := centralModel_unitary_component Nat.prime_five (by norm_num) hf hE
        (by omega) _ (actualNegativeHermitian_isSymm Q A.toLinearMap d d.ne_zero hsqd hs hadj)
        (actualNegativeHermitian_nondegenerate Q A.toLinearMap d d.ne_zero hsqd hs hadj hQ)
        hsig hne hpow hL
      obtain ⟨h1, -, -⟩ := eq_psl_two_one_of_a5 (Or.inr (Or.inl rfl)) hmodel.1 hmodel.2 hA
      exact absurd h1 (by decide)

end CFSG.ComponentClassification.SolMax.FiveCat.TwoL5.Omega
