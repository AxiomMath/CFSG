module

public import CFSG.CharacterTheory.Wreathed.LinearLocalTwistMoment
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualSimpleLayerRegularBasis

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.TwoRankLowerBound.Helpers CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOuterQuotient CFSG.Semidihedral.SemilinearOddExtensions
  CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Wreathed CFSG.Open
  CFSG.Semidihedral.Principal CFSG.Wreathed.LinearLocalTwistMoment

theorem regular_basis_data {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (Ct : Subgroup G) (hCt : Ct = C t) (localBasis : FiniteIrreducibleCharacterBasis Ct) :
    ∃ (e : ℤ) (φ : Ct → ℂ), (p ^ f % 4 = 1 → e = 1) ∧ (p ^ f % 4 = 3 → e = -1) ∧
      (e = 1 ∨ e = -1) ∧ φ 1 = ((p ^ f : ℕ) : ℂ) ∧
      (∃ lφ ∈ principalCoefficientBlock localBasis ideal,
        ∀ y, (localBasis.representation lφ).character y = φ y) ∧
      (∀ c₀ c₁ : ℂ, (∀ y : Ct, Odd (orderOf y) → c₀ + c₁ * (1 + e * φ y) = 0) →
        c₀ = 0 ∧ c₁ = 0) ∧
      ∃ D : localBasis.index → Fin 2 → ℤ,
        (∀ χ ∈ principalCoefficientBlock localBasis ideal, ∀ y : Ct, Odd (orderOf y) →
          (localBasis.representation χ).character y = D χ 0 + D χ 1 * (1 + e * φ y)) ∧
        ∑ χ ∈ principalCoefficientBlock localBasis ideal, D χ 0 * D χ 0 = 8 ∧
        ∑ χ ∈ principalCoefficientBlock localBasis ideal, D χ 0 * D χ 1 = -4 ∧
        ∑ χ ∈ principalCoefficientBlock localBasis ideal, D χ 1 * D χ 1 = 2 ^ (n - 2) + 2 := by
  subst hCt
  obtain ⟨F, hfield, hfinite, ρ, hcard, hρ, hlayer, hD, hrest⟩ :=
    actual_simple_layer_centralizer_principal_regular_basis n hn S0 f0 hG t ht hnonab hcentral
      hnc p f hp hpodd hf hmodel ideal localBasis (principalCharacterLabel localBasis)
      (principalCharacterLabel_character localBasis)
  set φ : C t → ℂ := fun c =>
    (Nat.card {x : Omega F // ((ρ (kappa t c) : coordinateE F) :
      Equiv.Perm (Omega F)) x = x} : ℂ) - 1 with hφdef
  set e : ℤ := if Nat.card F % 4 = 1 then 1 else -1 with hedef
  set Bloc := coefficientBlock localBasis (localizedComplexIntegerRing ideal)
    (principalCharacterLabel localBasis) with hBloc
  obtain ⟨⟨lφ, hlφB, -, hlφchar, -, -⟩, -, hind, -, ⟨D, hDrows⟩, hgram⟩ := hrest
  have hlφchar' : (localBasis.representation lφ).character = φ := hlφchar
  have hind' : LinearIndependent ℤ
      ![oddRestriction (1 : C t → ℂ), oddRestriction (1 + (e : ℂ) • φ)] := hind
  have hDrows' : ∀ χ : Bloc, oddRestriction (localBasis.representation χ).character =
      D χ 0 • oddRestriction (1 : C t → ℂ) + D χ 1 • oddRestriction (1 + (e : ℂ) • φ) :=
    hDrows
  have hDD : D.transpose * D = !![8, -4; -4, ((2 ^ (n - 2) + 2 : ℕ) : ℤ)] := hgram D hDrows
  have he : (e : ℂ) ≠ 0 := by
    simp only [e]
    split_ifs <;> norm_num
  have hφ1 : φ 1 = Nat.card F := by
    let _ : Fintype F := Fintype.ofFinite F
    have hfix : Nat.card {x : Omega F // ((ρ (kappa t 1) : coordinateE F) :
        Equiv.Perm (Omega F)) x = x} = Nat.card (Omega F) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun x => by
        rw [map_one, map_one]
        rfl)
    simp only [φ]
    rw [hfix, card_omega]
    push_cast
    ring
  have hex : ∃ y : C t, Odd (orderOf y) ∧ φ y ≠ Nat.card F := by
    by_contra hne
    push Not at hne
    have h0 := (LinearIndependent.pair_iff.mp hind') (1 + e * (Nat.card F : ℤ)) (-1) (by
      funext y
      have hy := hne y.1 y.2
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply]
      simp only [oddRestriction, Pi.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        zsmul_eq_mul, hy]
      push_cast
      ring)
    exact absurd h0.2 (by norm_num)
  set d : localBasis.index → Fin 2 → ℤ := fun χ j => if h : χ ∈ Bloc then D ⟨χ, h⟩ j else 0
    with hd
  have hdχ : ∀ χ (hχ : χ ∈ Bloc) j, d χ j = D ⟨χ, hχ⟩ j := fun χ hχ j => by
    simp only [hd, hχ, ↓reduceDIte]
  have hgramd : ∀ j k, ∑ θ ∈ Bloc, d θ j * d θ k = (D.transpose * D) j k := by
    intro j k
    rw [Matrix.mul_apply, ← Finset.sum_coe_sort Bloc]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [hdχ θ θ.2, hdχ θ θ.2, Matrix.transpose_apply]
  rw [hDD] at hgramd
  refine ⟨e, φ, fun h => ?_, fun h => ?_, ?_, ?_, ⟨lφ, hlφB, fun y => by rw [hlφchar']⟩,
    fun c₀ c₁ hc => ?_, d, fun χ hχ y hy => ?_, ?_, ?_, ?_⟩
  · simp only [e, hcard, h, ↓reduceIte]
  · have h1 : p ^ f % 4 ≠ 1 := by omega
    simp only [e, hcard, h1, ↓reduceIte]
  · simp only [e]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [hφ1, hcard]
  · obtain ⟨y0, hy0, hy0ne⟩ := hex
    have h1 := hc 1 (by rw [orderOf_one]; exact odd_one)
    have h2 := hc y0 hy0
    rw [hφ1] at h1
    have hsub : φ y0 - Nat.card F ≠ 0 := sub_ne_zero.mpr hy0ne
    have hc1 : c₁ = 0 := by
      have h3 : c₁ * ((e : ℂ) * (φ y0 - Nat.card F)) = 0 := by linear_combination h2 - h1
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h (mul_ne_zero he hsub)
    refine ⟨?_, hc1⟩
    rw [hc1] at h1
    simpa using h1
  · have h := congrFun (hDrows' ⟨χ, hχ⟩) ⟨y, hy⟩
    simp only [Pi.add_apply, Pi.smul_apply] at h
    simp only [oddRestriction, Pi.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      zsmul_eq_mul] at h
    rw [hdχ χ hχ, hdχ χ hχ]
    linear_combination h
  · simpa using hgramd 0 0
  · simpa using hgramd 0 1
  · simpa using hgramd 1 1

end CFSG.Semidihedral.FieldFactorOne
