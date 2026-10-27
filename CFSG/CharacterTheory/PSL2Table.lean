module

public import CFSG.CharacterTheory.PSL2Table.Classes
public import CFSG.CharacterTheory.PSL2Table.Halves

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
theorem card_mod_four (hF : ringChar F ≠ 2) :
    Fintype.card F % 4 = 1 ∨ Fintype.card F % 4 = 3 := by
  have := FiniteField.odd_card_of_char_ne_two hF
  omega

omit [DecidableEq F] in
theorem isSquare_neg_one_iff_mod_four (hF : ringChar F ≠ 2) :
    IsSquare (-1 : F) ↔ Fintype.card F % 4 = 1 := by
  rw [FiniteField.isSquare_neg_one_iff]
  have := card_mod_four hF
  omega

theorem psl2_conjugacy_classes (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) :
    Nat.card PSL(2, F) * 2 = Fintype.card F * (Fintype.card F ^ 2 - 1) ∧
    Nat.card (unipotent F) = Fintype.card F ∧
    Nat.card (splitTorus F) * 2 = Fintype.card F - 1 ∧
    Nat.card (nonsplitTorus ν) * 2 = Fintype.card F + 1 ∧
    IsCyclic (splitTorus F) ∧
    (∀ g : PSL(2, F), g = 1 ∨ IsConj g (mk (unip 1)) ∨ IsConj g (mk (unip ν)) ∨
      (∃ x ∈ splitTorus F, x ≠ 1 ∧ IsConj g x) ∨
      (∃ x ∈ nonsplitTorus ν, x ≠ 1 ∧ IsConj g x)) ∧
    ¬ IsConj (mk (unip (1 : F))) (mk (unip ν)) ∧
    (∀ s t : F, s ≠ 0 → t ≠ 0 → (IsConj (mk (unip s)) (mk (unip t)) ↔ IsSquare (s * t))) ∧
    (∀ u ∈ unipotent F, u ≠ 1 → ∀ x ∈ splitTorus F, x ≠ 1 → ¬ IsConj u x) ∧
    (∀ u ∈ unipotent F, u ≠ 1 → ∀ x ∈ nonsplitTorus ν, x ≠ 1 → ¬ IsConj u x) ∧
    (∀ x ∈ splitTorus F, x ≠ 1 → ∀ y ∈ nonsplitTorus ν, y ≠ 1 → ¬ IsConj x y) ∧
    (∀ x ∈ splitTorus F, x ≠ 1 → ∀ y ∈ splitTorus F, (IsConj x y ↔ y = x ∨ y = x⁻¹)) ∧
    (∀ x ∈ nonsplitTorus ν, x ≠ 1 → ∀ y ∈ nonsplitTorus ν, (IsConj x y ↔ y = x ∨ y = x⁻¹)) ∧
    (∀ t : F, t ≠ 0 → Subgroup.centralizer {mk (unip t)} = unipotent F) ∧
    (∀ x ∈ splitTorus F, x ≠ 1 → Nat.card (Subgroup.centralizer {x} : Subgroup PSL(2, F)) =
      if x ^ 2 = 1 then 2 * Nat.card (splitTorus F) else Nat.card (splitTorus F)) ∧
    (∀ x ∈ nonsplitTorus ν, x ≠ 1 → Nat.card (Subgroup.centralizer {x} : Subgroup PSL(2, F)) =
      if x ^ 2 = 1 then 2 * Nat.card (nonsplitTorus ν) else Nat.card (nonsplitTorus ν)) ∧
    ((∃ x ∈ splitTorus F, orderOf x = 2) ↔ Fintype.card F % 4 = 1) ∧
    ((∃ x ∈ nonsplitTorus ν, orderOf x = 2) ↔ Fintype.card F % 4 = 3) ∧
    (∀ g : PSL(2, F), orderOf g = 2 →
      (Fintype.card F % 4 = 1 → ∃ x ∈ splitTorus F, IsConj g x) ∧
      (Fintype.card F % 4 = 3 → ∃ x ∈ nonsplitTorus ν, IsConj g x)) := by
  have h2 := Ring.two_ne_zero hF
  have hsq := isSquare_neg_one_iff_mod_four hF
  have h4 := card_mod_four hF
  obtain ⟨hPT, hPS, hTS⟩ := not_isConj_families hF hν
  refine ⟨card_PSL h2, card_unipotent h2, card_splitTorus h2, card_nonsplitTorus hF hν,
    splitTorus_isCyclic, conj_cases hF hq hν, not_isConj_unip_one_unip_nu hF hν,
    fun s t hs ht => isConj_unip_iff h2 hs ht, hPT, hPS, hTS,
    fun x hx hx1 y hy => isConj_splitTorus_iff hx hx1 hy,
    fun x hx hx1 y hy => isConj_nonsplitTorus_iff hF hν hx hx1 hy,
    fun t ht => centralizer_mk_unip h2 ht,
    fun x hx hx1 => card_centralizer_splitTorus hF hq hx hx1,
    fun x hx hx1 => card_centralizer_nonsplitTorus hF hq hν hx hx1, ?_, ?_, ?_⟩
  · rw [exists_involution_splitTorus_iff hF, hsq]
  · rw [exists_involution_nonsplitTorus_iff hF hν, hsq]
    omega
  · intro g hg
    obtain ⟨h1, h3⟩ := involution_conj_torus hF hq hν hg
    exact ⟨fun h => h1 (hsq.mpr h), fun h => h3 (fun h' => by have := hsq.mp h'; omega)⟩

theorem psl2_character_table (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    BlocksIrr PSL(2, F) = {χ | χ = 1 ∨ χ = steinberg F ∨
      (∃ α : splitTorus F →* ℂˣ, α ^ 2 ≠ 1 ∧ χ = principal α) ∨
      (∃ β : nonsplitTorus ν →* ℂˣ, β ^ 2 ≠ 1 ∧ χ = discrete β) ∨
      χ = halfPlus hF ψ ν ∨ χ = halfMinus hF ψ ν} ∧
    steinberg F ∈ BlocksIrr PSL(2, F) ∧
    (∀ α : splitTorus F →* ℂˣ, α ^ 2 ≠ 1 → principal α ∈ BlocksIrr PSL(2, F)) ∧
    (∀ β : nonsplitTorus ν →* ℂˣ, β ^ 2 ≠ 1 → discrete β ∈ BlocksIrr PSL(2, F)) ∧
    halfPlus hF ψ ν ∈ BlocksIrr PSL(2, F) ∧ halfMinus hF ψ ν ∈ BlocksIrr PSL(2, F) ∧
    halfPlus hF ψ ν ≠ halfMinus hF ψ ν ∧
    (∀ α α' : splitTorus F →* ℂˣ, α ^ 2 ≠ 1 →
      (principal α' = principal α ↔ α' = α ∨ α' = α⁻¹)) ∧
    (∀ β β' : nonsplitTorus ν →* ℂˣ, β ^ 2 ≠ 1 →
      (discrete β' = discrete β ↔ β' = β ∨ β' = β⁻¹)) ∧
    (principalSet F).card * 2 =
      Nat.card (splitTorus F) - (if Fintype.card F % 4 = 1 then 2 else 1) ∧
    (discreteSet ν).card * 2 =
      Nat.card (nonsplitTorus ν) - (if Fintype.card F % 4 = 1 then 1 else 2) := by
  have hsq := isSquare_neg_one_iff_mod_four hF
  obtain ⟨hIrr, hp, hm, hne, -, -, -, -⟩ := blocksIrr_eq hF hq hν hψ
  refine ⟨?_, steinberg_mem_blocksIrr hF hq hν, fun α hα => principal_mem_blocksIrr hF hq hν hα,
    fun β hβ => discrete_mem_blocksIrr hF hq hν hβ, hp, hm, hne,
    fun α α' hα => principal_eq_iff hF hq hν hα α', fun β β' hβ => discrete_eq_iff hF hq hν hβ β',
    ?_, ?_⟩
  · rw [hIrr]
    ext χ
    simp only [Set.mem_union, Finset.mem_coe, knownSet, Finset.mem_insert, Finset.mem_union,
      mem_principalSet_iff, mem_discreteSet_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_ofPred_eq]
    constructor
    · rintro ((h | h | ⟨α, hα, rfl⟩ | ⟨β, hβ, rfl⟩) | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨α, hα, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨β, hβ, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · rintro (h | h | ⟨α, hα, rfl⟩ | ⟨β, hβ, rfl⟩ | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨α, hα, rfl⟩)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨β, hβ, rfl⟩)))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · rw [card_principalSet hF hq hν]
    simp only [hsq]
  · rw [card_discreteSet hF hq hν]
    simp only [hsq]

theorem psl2_character_values (hF : ringChar F ≠ 2) {ν : F}
    (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    (steinberg F 1 = Fintype.card F ∧
      (∀ x ∈ unipotent F, x ≠ 1 → steinberg F x = 0) ∧
      (∀ x ∈ splitTorus F, x ≠ 1 → steinberg F x = 1) ∧
      (∀ x ∈ nonsplitTorus ν, x ≠ 1 → steinberg F x = -1)) ∧
    (∀ α : splitTorus F →* ℂˣ, principal α 1 = Fintype.card F + 1 ∧
      (∀ x ∈ unipotent F, x ≠ 1 → principal α x = 1) ∧
      (∀ (x : PSL(2, F)) (hx : x ∈ splitTorus F), x ≠ 1 →
        principal α x = (α ⟨x, hx⟩ : ℂ) + (α ⟨x, hx⟩⁻¹ : ℂ)) ∧
      (∀ x ∈ nonsplitTorus ν, x ≠ 1 → principal α x = 0)) ∧
    (∀ β : nonsplitTorus ν →* ℂˣ, discrete β 1 = Fintype.card F - 1 ∧
      (∀ x ∈ unipotent F, x ≠ 1 → discrete β x = -1) ∧
      (∀ x ∈ splitTorus F, x ≠ 1 → discrete β x = 0) ∧
      (∀ (x : PSL(2, F)) (hx : x ∈ nonsplitTorus ν), x ≠ 1 →
        discrete β x = -((β ⟨x, hx⟩ : ℂ) + (β ⟨x, hx⟩⁻¹ : ℂ)))) ∧
    (epsSign F = if Fintype.card F % 4 = 1 then 1 else -1) ∧
    quadGauss ψ ^ 2 = epsSign F * Fintype.card F ∧
    halfPlus hF ψ ν 1 = (Fintype.card F + epsSign F) / 2 ∧
    halfMinus hF ψ ν 1 = (Fintype.card F + epsSign F) / 2 ∧
    (∀ t : F, t ≠ 0 →
      halfPlus hF ψ ν (mk (unip t)) = (epsSign F + quadChar F t * quadGauss ψ) / 2 ∧
      halfMinus hF ψ ν (mk (unip t)) = (epsSign F - quadChar F t * quadGauss ψ) / 2) ∧
    (∀ (x : PSL(2, F)) (hx : x ∈ splitTorus F), x ≠ 1 →
      halfPlus hF ψ ν x = (if Fintype.card F % 4 = 1 then (splitQuadChar F ⟨x, hx⟩ : ℂ) else 0) ∧
      halfMinus hF ψ ν x = (if Fintype.card F % 4 = 1 then (splitQuadChar F ⟨x, hx⟩ : ℂ) else 0)) ∧
    (∀ (x : PSL(2, F)) (hx : x ∈ nonsplitTorus ν), x ≠ 1 →
      halfPlus hF ψ ν x =
          (if Fintype.card F % 4 = 1 then 0 else -(nonsplitQuadChar ν ⟨x, hx⟩ : ℂ)) ∧
      halfMinus hF ψ ν x =
          (if Fintype.card F % 4 = 1 then 0 else -(nonsplitQuadChar ν ⟨x, hx⟩ : ℂ))) ∧
    (Fintype.card F % 4 = 1 → splitQuadChar F ≠ 1 ∧ splitQuadChar F ^ 2 = 1) ∧
    (Fintype.card F % 4 = 3 → nonsplitQuadChar ν ≠ 1 ∧ nonsplitQuadChar ν ^ 2 = 1) := by
  have hsq := isSquare_neg_one_iff_mod_four hF
  have h4 := card_mod_four hF
  have heps : epsSign F = if Fintype.card F % 4 = 1 then 1 else -1 := by
    rw [epsSign]
    simp only [hsq]
  have hdeg : (normTwoDegree F : ℂ) = Fintype.card F + epsSign F := by
    rw [normTwoDegree, epsSign]
    split_ifs
    · push_cast
      ring
    · rw [Nat.cast_sub Fintype.card_pos]
      push_cast
      ring
  refine ⟨⟨steinberg_one, fun x hx hx1 => steinberg_of_mem_unipotent hF hx hx1,
      fun x hx hx1 => steinberg_of_mem_splitTorus hx hx1,
      fun x hx hx1 => steinberg_of_mem_nonsplitTorus hν hx hx1⟩,
    fun α => ⟨principal_one hF α, fun x hx hx1 => principal_of_mem_unipotent hF α hx hx1,
      fun x hx hx1 => principal_of_mem_splitTorus α hx hx1,
      fun x hx hx1 => principal_of_mem_nonsplitTorus hF hν α hx hx1⟩,
    fun β => ⟨discrete_one hF hν β, fun x hx hx1 => discrete_of_mem_unipotent hF hν β hx hx1,
      fun x hx hx1 => discrete_of_mem_splitTorus hF hν β hx hx1,
      fun x hx hx1 => discrete_of_mem_nonsplitTorus hF hν β hx hx1⟩,
    heps, quadGauss_sq_eps hF hψ, ?_, ?_,
    fun t ht => ⟨halfPlus_unip hF hψ hν ht, halfMinus_unip hF hψ hν ht⟩, ?_, ?_, ?_, ?_⟩
  · rw [halfPlus_one hF ψ hν, hdeg]
  · rw [halfMinus_one hF ψ hν, hdeg]
  · intro x hx hx1
    rw [halfPlus_of_mem_splitTorus hF ψ hν hx hx1, halfMinus_of_mem_splitTorus hF ψ hν hx hx1]
    simp only [hsq, and_self]
  · intro x hx hx1
    rw [halfPlus_of_mem_nonsplitTorus hF ψ hν hx hx1,
      halfMinus_of_mem_nonsplitTorus hF ψ hν hx hx1]
    simp only [hsq, and_self]
  · intro h
    exact splitQuadChar_spec hF (hsq.mpr h)
  · intro h
    exact nonsplitQuadChar_spec hF hν (fun h' => by have := hsq.mp h'; omega)

theorem galoisField_hypotheses (p f : ℕ) [Fact p.Prime] [Fintype (GaloisField p f)]
    (hp : p ≠ 2) (hf : f ≠ 0) (hq : 5 ≤ p ^ f) :
    ringChar (GaloisField p f) ≠ 2 ∧ Fintype.card (GaloisField p f) = p ^ f ∧
      5 ≤ Fintype.card (GaloisField p f) ∧ ∃ ν : GaloisField p f, ¬ IsSquare ν := by
  have hchar : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp
  have hcard : Fintype.card (GaloisField p f) = p ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p f hf]
  exact ⟨hchar, hcard, hcard ▸ hq, FiniteField.exists_nonsquare hchar⟩

end CFSG.PSL2Table
