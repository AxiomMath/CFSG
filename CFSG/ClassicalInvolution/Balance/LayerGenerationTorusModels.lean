module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationTorusElements
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShort
import CFSG.LieType.Steinberg.Classical.SpecialLinear
import CFSG.LieType.Steinberg.Classical.SpinOdd
import CFSG.LieType.Steinberg.Classical.SpinPlus
import CFSG.LieType.Steinberg.Classical.Symplectic

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg

section Models

variable {p : ℕ} [Fact p.Prime]

theorem exists_chevalleyExtras_model (t : StatedLieTag) (n f : ℕ)
    (hadm : StatedLieAdmissible t n p f)
    (ht : (t = .PSL ∧ 3 ≤ n) ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) :
    ∃ x C O, ChevalleyExtras (modelUniv t n p f Fact.out).D (GaloisField p f) x C O := by
  rcases ht with ⟨rfl, hn3⟩ | rfl | rfl | rfl | rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 2 ≤ m := by omega
    obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (SpecialLinear.rootDatum m (GaloisField p f)).isFiniteType rfl
    exact ⟨_, _, O, SL.chevalleyExtras hm O _ (SL.commutatorFormula O)⟩
  · have hn : 3 ≤ n := by have := hadm.2.2; omega
    show ∃ x C O, ChevalleyExtras
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus n p f Fact.out).D
      (GaloisField p f) x C O
    rw [CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn]
    obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Spin.plusDatum n (GaloisField p f) hn).isFiniteType rfl
    exact ⟨_, _, O, SpinPlus.chevalleyExtras hn O _ (SpinPlus.commutatorFormula hn O)⟩
  · obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Minuscule.e6Datum (GaloisField p f)).isFiniteType rfl
    obtain ⟨C, -, hC⟩ := Minuscule.e6Datum_commutatorFormula (GaloisField p f) _
      (Minuscule.roots_eq Minuscule.isFiniteType_cartan_E6) O
    exact ⟨_, C, O, Minuscule.e6_chevalleyExtras (GaloisField p f) O C hC⟩
  · obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Minuscule.e7Datum (GaloisField p f)).isFiniteType rfl
    obtain ⟨C, -, hC⟩ := Minuscule.e7Datum_commutatorFormula (GaloisField p f) _
      (Minuscule.roots_eq Minuscule.isFiniteType_cartan_E7) O
    exact ⟨_, C, O, Minuscule.e7_chevalleyExtras (GaloisField p f) O C hC⟩
  · obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Adjoint.e8Datum (GaloisField p f)).isFiniteType rfl
    obtain ⟨C, -, hC⟩ := Adjoint.e8_commutatorFormula (GaloisField p f) O
    exact ⟨_, C, O, Adjoint.e8_chevalleyExtras (GaloisField p f) O C hC⟩

theorem exists_chevalleyExtras_model_nonSimplyLaced (t : StatedLieTag) (n f : ℕ)
    (ht : (t = .PSp ∧ 2 ≤ n) ∨ (t = .POmegaOdd ∧ 2 ≤ n) ∨ t = .F4) :
    ∃ x C O, ChevalleyExtras (modelUniv t n p f Fact.out).D (GaloisField p f) x C O := by
  rcases ht with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | rfl
  · obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Symplectic.rootDatum n (GaloisField p f)).isFiniteType rfl
    exact ⟨_, _, O, Sp.chevalleyExtras hn O _ (Sp.commutatorFormula O)⟩
  · obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Spin.oddDatum n (GaloisField p f)).isFiniteType rfl
    exact ⟨_, _, O, SpinOdd.chevalleyExtras hn O _ (SpinOdd.commutatorFormula O)⟩
  · obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Adjoint.f4Datum (GaloisField p f)).isFiniteType rfl
    obtain ⟨C, -, hC⟩ := Adjoint.f4_commutatorFormula (GaloisField p f) O
    exact ⟨_, C, O, Adjoint.f4_chevalleyExtras (GaloisField p f) O C hC⟩

end Models

section Provider

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

theorem componentHom_ker_le_center (hΩ : InClass p f Ω) {a : G} (D : LocalLieSystemAt p f Ω a)
    (j : Fin D.card) : (componentHom hΩ D j).ker ≤ Subgroup.center (compModel D j).K := by
  intro y hy
  have h1 : D.hom j y = 1 := by
    have : layerQuotientHom hΩ.conjInvariant a (D.hom j y) = 1 := hy
    exact (map_eq_one_iff _ (layerQuotientHom_injective hΩ.conjInvariant)).mp this
  exact D.ker_le_center j h1

theorem LayerGenerationLie.of_diagonalSimpleRoots_simplyLaced (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hE2 : ∀ x ∈ E, x * x = 1) {a : G} (ha : a ∈ E)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (htor : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) (F₀ : Subgroup G),
      IsFaithfulFourGroupAt E a (componentHom hΩ D j).range F₀ →
        (D.tag j = .PSL ∨ D.tag j = .POmegaPlus ∨ D.tag j = .E6 ∨ D.tag j = .E7 ∨
          D.tag j = .E8) ∧
        ∃ (x : (Fin (compModel D j).D.rank → ℤ) → GaloisField p (D.exp j) → (compModel D j).K)
          (C : (Fin (compModel D j).D.rank → ℤ) → (Fin (compModel D j).D.rank → ℤ) →
            ℕ × ℕ → ℤ)
          (O : CommOrder (RootSystem.ofCartan (compModel D j).D.isFiniteType
            (compModel D j).D.divisible))
          (_ : ChevalleyExtras (compModel D j).D (GaloisField p (D.exp j)) x C O)
          (g : (compModel D j).K),
          ∀ e ∈ modOdd a F₀, ∀ i : Fin (compModel D j).D.rank, ∃ b : (GaloisField p (D.exp j))ˣ,
            ActsDiagonallyOnSimple x (componentHom hΩ D j) g i e b) :
    LayerGenerationLie Ω E a := by
  refine LayerGenerationLie.of_toralSimpleRoots_simplyLaced hp2 h0 hA1 hq hΩ hIH hE2 ha hnc ?_
  intro D j F₀ hF
  obtain ⟨hsl, x, C, O, hX, g, hdiag⟩ := htor D j F₀ hF
  refine ⟨hsl, g, fun i => ?_⟩
  exact indexTwoCentralizes_rankOneImage_simple hX (componentHom_ker_le_center hΩ D j) g i
    (modOdd_sq_eq_one hE2 hF.1) fun e he => hdiag e he i

theorem LayerGenerationLie.of_innerTorus_simplyLaced (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hE2 : ∀ x ∈ E, x * x = 1) {a : G} (ha : a ∈ E)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (htor : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) (F₀ : Subgroup G),
      IsFaithfulFourGroupAt E a (componentHom hΩ D j).range F₀ →
        (D.tag j = .PSL ∨ D.tag j = .POmegaPlus ∨ D.tag j = .E6 ∨ D.tag j = .E7 ∨
          D.tag j = .E8) ∧
        ∃ (x : (Fin (compModel D j).D.rank → ℤ) → GaloisField p (D.exp j) → (compModel D j).K)
          (C : (Fin (compModel D j).D.rank → ℤ) → (Fin (compModel D j).D.rank → ℤ) →
            ℕ × ℕ → ℤ)
          (O : CommOrder (RootSystem.ofCartan (compModel D j).D.isFiniteType
            (compModel D j).D.divisible))
          (_ : ChevalleyExtras (compModel D j).D (GaloisField p (D.exp j)) x C O)
          (g : (compModel D j).K),
          ∀ e ∈ modOdd a F₀, ∃ t ∈ torusOf x, ∀ y : (compModel D j).K,
            e * componentHom hΩ D j y * e⁻¹ =
              componentHom hΩ D j (g * t * g⁻¹ * y * (g * t * g⁻¹)⁻¹)) :
    LayerGenerationLie Ω E a := by
  refine LayerGenerationLie.of_diagonalSimpleRoots_simplyLaced hp2 h0 hA1 hq hΩ hIH hE2 ha hnc ?_
  intro D j F₀ hF
  obtain ⟨hsl, x, C, O, hX, g, h⟩ := htor D j F₀ hF
  refine ⟨hsl, x, C, O, hX, g, fun e he i => ?_⟩
  obtain ⟨t, ht, hconj⟩ := h e he
  exact exists_actsDiagonallyOnSimple_of_actsAsTorus hX _ g e ht hconj i

theorem LayerGenerationLie.of_diagonalSimpleRoots_components (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hE2 : ∀ x ∈ E, x * x = 1) {a : G} (ha : a ∈ E)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (htor : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) (F₀ : Subgroup G),
      CFSG.IsComponent (componentHom hΩ D j).range →
      IsFaithfulFourGroupAt E a (componentHom hΩ D j).range F₀ →
        ∃ (x : (Fin (compModel D j).D.rank → ℤ) → GaloisField p (D.exp j) → (compModel D j).K)
          (C : (Fin (compModel D j).D.rank → ℤ) → (Fin (compModel D j).D.rank → ℤ) →
            ℕ × ℕ → ℤ)
          (O : CommOrder (RootSystem.ofCartan (compModel D j).D.isFiniteType
            (compModel D j).D.divisible))
          (_ : ChevalleyExtras (compModel D j).D (GaloisField p (D.exp j)) x C O)
          (g : (compModel D j).K),
          (∀ e ∈ modOdd a F₀, ∀ i : Fin (compModel D j).D.rank, ∃ b : (GaloisField p (D.exp j))ˣ,
            ActsDiagonallyOnSimple x (componentHom hΩ D j) g i e b) ∧
          ∀ i : Fin (compModel D j).D.rank, ¬ IsInvolutionMember
              (rankOneImage (compModel D j).D (componentHom hΩ D j) g (Pi.single i 1)) →
            ∃ f ∈ modOdd a F₀, f ≠ 1 ∧
              InComponentOfCentralizer (componentHom hΩ D j).range
                (rankOneImage (compModel D j).D (componentHom hΩ D j) g (Pi.single i 1)) f) :
    LayerGenerationLie Ω E a := by
  refine LayerGenerationLie.of_toralSimpleRoots_components hp2 h0 hA1 hq hΩ hIH hE2 ha hnc ?_
  intro D j F₀ hL hF
  obtain ⟨x, C, O, hX, g, hdiag, hS⟩ := htor D j F₀ hL hF
  exact ⟨g, fun i => indexTwoCentralizes_rankOneImage_simple hX
    (componentHom_ker_le_center hΩ D j) g i (modOdd_sq_eq_one hE2 hF.1)
    fun e he => hdiag e he i, hS⟩

end Provider

end CFSG.ClassicalInvolution.Balance
