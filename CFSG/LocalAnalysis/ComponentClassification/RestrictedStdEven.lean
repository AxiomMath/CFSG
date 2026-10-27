module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISpSocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear

public section

namespace CFSG.ComponentClassification.RestrictedStd

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB

theorem statedClassicalModel_of_lieModel_PSL {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .PSL n p f) : StatedClassicalModel X .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem statedClassicalModel_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (h : LieModel X t n p f) : StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

theorem exists_coordinateG_of_statedClassicalModel' {X : Type} [Group X] {ℓ e : ℕ}
    (h : StatedClassicalModel X .PSL 2 ℓ e) :
    ℓ.Prime ∧ 1 ≤ e ∧ 4 ≤ ℓ ^ e ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = ℓ ^ e ∧
        Nonempty (X ≃* CatalogueSchreierLinearTwo.coordinateG K) := by
  obtain ⟨⟨hℓ, he, -, h22, h23⟩, K, hK, hKfin, hcard, ⟨φ⟩⟩ := h
  have h2 : 2 ≤ ℓ ^ e := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have hne2 : ℓ ^ e ≠ 2 := fun h => h22 (by rw [h])
  have hne3 : ℓ ^ e ≠ 3 := fun h => h23 (by rw [h])
  refine ⟨hℓ, he, by omega, K, hK, hKfin, hcard, ⟨φ.trans ?_⟩⟩
  exact (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    (CatalogueSchreierLinearTwo.pslEquivCoordinateG K)

theorem exists_selector_source {A : Type} [Group A] {L : Subgroup A} (hs : SmallSource L) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
        Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
        StatedClassicalModel (L ⧸ center L) .PSL 3 2 2) := by
  rcases hs with ⟨p, f, hp, hp2, hf, -, hm, -⟩ | ⟨h7, -⟩ | h34
  · exact ⟨p, f, hp, hp2, hf, Or.inl (statedClassicalModel_of_lieModel_PSL hm)⟩
  · exact ⟨3, 1, Nat.prime_three, by decide, le_rfl, Or.inr (Or.inl h7)⟩
  · exact ⟨3, 1, Nat.prime_three, by decide, le_rfl,
      Or.inr (Or.inr (statedClassicalModel_of_lieModel_PSL h34))⟩

variable {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
  (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
  (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
  (hLW : L ≤ W) (hL : Assembly.IsComponentOf L (centralizer ({a} : Set A)))
  (hs : SmallSource L)

include hWs hWnab hCW ha hLW hL hs

theorem gsRestricted_even_psl_two {e : ℕ} (hm : LieModel W .PSL 2 2 e) : GSRestricted W := by
  obtain ⟨hℓ, he, hK4, K, _, _, hK, ⟨φ⟩⟩ :=
    exists_coordinateG_of_statedClassicalModel' (statedClassicalModel_of_lieModel_PSL hm)
  have := Fact.mk hℓ
  obtain ⟨hev, -, σ, -, -, -, ρK, -, -, -, -, c, -, -, -, -, -, -, -, -, -, -, -, -, hL0c, hL0m,
    -⟩ :=
    SymmetricLocal.faithful_projective_linear_two_socle_involution_component_model hWs hWnab hCW
      ha hLW hL he hK hK4 φ
  let eZ : L ≃* L ⧸ center L := MulEquiv.ofBijective (QuotientGroup.mk' (center L))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk']; exact hL0c),
      QuotientGroup.mk'_surjective _⟩
  have hm' : StatedClassicalModel (L ⧸ center L) .PSL 2 2 (e / 2) :=
    SectionRank.statedClassicalModel_of_mulEquiv eZ.symm hL0m
  obtain ⟨hpar, h7, h34⟩ :=
    UnbalancingLocal.small_standard_source_projective_linear_two_field_parameters_stated hm'
  have he2 : e / 2 = 2 := by
    rcases hs with ⟨p, f, -, hp2, -, -, hpm, -⟩ | ⟨h7', -⟩ | h34'
    · rcases hpar p f hp2 (statedClassicalModel_of_lieModel_PSL hpm) with
        ⟨⟨hodd, -⟩, -⟩ | ⟨⟨-, hg, -⟩, -⟩
      · exact absurd hodd (by decide)
      · exact hg
    · exact (h7.false h7'.some).elim
    · exact (h34 (statedClassicalModel_of_lieModel_PSL h34')).elim
  have he4 : e = 4 := by
    obtain ⟨k, rfl⟩ := hev
    omega
  subst he4
  exact gsRestricted_psl_two_sixteen hm

theorem gsRestricted_even_psl {n e : ℕ} (hn : 3 ≤ n) (he : 1 ≤ e) (hm : LieModel W .PSL n 2 e)
    (hWalt : ∀ m : ℕ, 5 ≤ m → IsEmpty (W ≃* alternatingGroup (Fin m))) : GSRestricted W := by
  obtain ⟨p, f, hp, hp2, hf, hsrc⟩ := exists_selector_source hs
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := statedClassicalModel_of_lieModel_PSL hm
  obtain ⟨ρ₀, -, -, -, -, -, -, c₀, hrows⟩ :=
    OutcomeLocal.faithful_even_higher_linear_socle_small_source_involution_selector hWs hWnab hCW
      ha hLW hL hp hp2 hf hsrc hWalt hn he hK
      (φ.trans (SymmetricLocal.statedProjEquivProjectiveSL n K))
  rcases hrows with ⟨σ, hF, -⟩ | hG
  · rcases hF with ⟨hn3, he2, -⟩ | ⟨hn3, he4, -⟩
    · subst hn3 he2
      exact gsRestricted_psl_three_four hm
    · subst hn3 he4
      exact gsRestricted_psl_three_sixteen hm
  · obtain ⟨-, -, -, -, -, -, hG59⟩ := hG
    rcases hG59 with ⟨hn3, he2, -⟩ | ⟨hn5, he1, -⟩
    · subst hn3 he2
      exact gsRestricted_psl_three_four hm
    · subst hn5 he1
      exact gsRestricted_psl_five_two hm

theorem gsRestricted_even_psp {r e : ℕ} (hm : LieModel W .PSp r 2 e) : GSRestricted W := by
  obtain ⟨p, f, hp, hp2, hf, hsrc⟩ := exists_selector_source hs
  obtain ⟨⟨-, he, hr, hne⟩, K, _, _, hK, ⟨φ⟩⟩ :=
    statedClassicalModel_of_lieModel (by decide) hm
  have := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
    he hK
  have hre : ¬ (r = 2 ∧ e = 1) := fun ⟨hr2, he1⟩ => hne (by rw [hr2, he1]; rfl)
  obtain ⟨-, -, -, -, hr2, he2, -⟩ :=
    OutcomeLocal.faithful_even_symplectic_socle_small_source_involution_selector hWs hWnab hCW
      ha hLW hL hp hp2 hf hsrc hr he hre hK φ
  subst hr2 he2
  exact gsRestricted_psp_four_four hm

end CFSG.ComponentClassification.RestrictedStd
