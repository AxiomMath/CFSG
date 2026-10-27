module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitChain
public import CFSG.LocalAnalysis.ComponentClassification.GSLitMaximalTriple

public section

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem isCyclic_sylow_of_eq_zpowers {G : Type*} [Group G] [Finite G] {K : Subgroup G} {b : G}
    (hb : zpowers b ≤ K) (hP : ∃ P : Sylow 2 ↥K, (P : Subgroup _) = (zpowers b).subgroupOf K)
    (P : Sylow 2 ↥K) : IsCyclic (P : Subgroup ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := hP
  have h₀ : IsCyclic (P₀ : Subgroup ↥K) := by
    rw [hP₀]
    exact (MulEquiv.isCyclic (subgroupOfEquivOfLe hb)).mpr (isCyclic_zpowers b)
  exact (MulEquiv.isCyclic (Sylow.equiv P₀ P)).mp h₀

theorem exists_maximal_component_of_small_types (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hB : TheoremBBoundedInput) (hH : HarrisInput)
    (hGF : GloballyFirstRankTwoInput)
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (hsmall : ¬ ∃ (x y : X) (L : Subgroup X), GSUnbalancingTriple x y L ∧
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) ∨
        Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2))
    (htriple : ∃ (a b : X) (J : Subgroup X), GSUnbalancingTriple a b J) :
    ∃ (x y : X) (L : Subgroup X), GSMaximalUnbalancingTriple x y L ∧ GSMaximalComponent L ∧
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) := by
  obtain ⟨a, x, J, hJ, hbound⟩ :=
    exists_maximal_unbalancing_triple_bounded hTB hSA hGF hnonab hK hz hU htriple
  have htype := unbalancing_component_type_of_small hTB hSA hnonab hK hz hU hsmall hJ.1
  refine ⟨a, x, J, hJ, ?_, htype⟩
  rcases hB X hnonab hK hz hU a x J hJ hbound (htype.imp id Or.inl) with
    ⟨-, b, L, ρ, e, hb, hLb, hL, hρ, hρ2, he, hLie, hbK, hP⟩ | ⟨hiso, hcentral⟩
  · refine absurd ⟨b, L, hb, hLb, hL, gsMaximalComponent_of_cyclic_kernel hb hLb hL hP,
      ⟨ρ, 2 * e, hρ, hρ2, by omega, ?_, hLie⟩, isCyclic_sylow_of_eq_zpowers hbK hP⟩
      (hH X hnonab hK hz hU)
    have h3 : 3 ≤ ρ := by have := hρ.two_le; omega
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ ρ ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ ρ ^ (2 * e) := Nat.pow_le_pow_right hρ.pos (by omega)
  · exact gsMaximalComponent_of_B2 hJ.1.1 hJ.1.2.2.2.1 hJ.1.2.2.2.2.1 hiso hcentral

theorem exists_maximal_component_of_inputs (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hGS : GriessSolomonInput) (hB : TheoremBBoundedInput)
    (hH : HarrisInput) (hGF : GloballyFirstRankTwoInput)
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (htriple : ∃ (a b : X) (J : Subgroup X), GSUnbalancingTriple a b J) :
    ∃ (x y : X) (L : Subgroup X), GSMaximalUnbalancingTriple x y L ∧ GSMaximalComponent L ∧
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) :=
  exists_maximal_component_of_small_types hTB hSA hB hH hGF X hnonab hK hz hU
    (hGS X hnonab hK hz hU) htriple

theorem cl_lit_gilman_solomon_of_inputs (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hGS : GriessSolomonInput) (hB : TheoremBBoundedInput)
    (hH : HarrisInput) (hGF : GloballyFirstRankTwoInput)
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (htriple : ∃ (a b : X) (J : Subgroup X), GSUnbalancingTriple a b J) :
    ∃ (x y : X) (L : Subgroup X), GSMaximalUnbalancingTriple x y L ∧ GSMaximalComponent L ∧
      ((Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
          ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
            Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) ∨
        (Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) ∨
          Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2)) := by
  obtain ⟨x, y, L, h1, h2, h3⟩ :=
    exists_maximal_component_of_inputs hTB hSA hGS hB hH hGF X hnonab hK hz hU htriple
  exact ⟨x, y, L, h1, h2, Or.inl h3⟩

end CFSG.ComponentClassification.GSLit
