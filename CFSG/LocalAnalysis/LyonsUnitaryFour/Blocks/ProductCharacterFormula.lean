module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasisDegreeSum
public import CFSG.CharacterTheory.Wreathed.WeightedCentralInvolutionSum

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed
open scoped BigOperators

@[expose] def productCount {G : Type*} [Group G] [DecidableEq G] (A B : Finset G) (x : G) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1 * p.2 = x)).card

@[expose] def ConjInvariant {G : Type*} [Group G] (A : Finset G) : Prop :=
  ∀ conjugator element : G, element ∈ A ↔ conjugator * element * conjugator⁻¹ ∈ A

theorem irreducible_invariant_sum_eq_smul {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (hirr : data.IsIrreducible) (A : Finset G)
    (hA : ConjInvariant A) :
    (∑ a ∈ A, data.representation a) =
      ((∑ a ∈ A, data.character a) / data.character 1) • (1 : Module.End ℂ data.vector) := by
  let : data.representation.IsIrreducible := hirr
  obtain ⟨c, hc⟩ := irreducible_invariant_sum_is_scalar data.representation A hA
  have hdeg := irreducible_character_degree_ne_zero data hirr
  have htrace := congrArg (LinearMap.trace ℂ data.vector) hc
  rw [map_sum, map_smul, LinearMap.trace_one] at htrace
  have hdim : (Module.finrank ℂ data.vector : ℂ) = data.character 1 := by
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  rw [hdim, smul_eq_mul] at htrace
  have hc' : c = (∑ a ∈ A, data.character a) / data.character 1 := by
    rw [eq_div_iff hdeg]
    exact htrace.symm
  rw [hc, hc']

theorem irreducible_character_product_sum {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (hirr : data.IsIrreducible) (A B : Finset G)
    (hA : ConjInvariant A) (hB : ConjInvariant B) (y : G) :
    (∑ a ∈ A, ∑ b ∈ B, data.character (a * b * y)) =
      (∑ a ∈ A, data.character a) * (∑ b ∈ B, data.character b) * data.character y /
        data.character 1 ^ 2 := by
  have hdeg := irreducible_character_degree_ne_zero data hirr
  have hprod : (∑ a ∈ A, ∑ b ∈ B, data.character (a * b * y)) =
      LinearMap.trace ℂ data.vector ((∑ a ∈ A, data.representation a) *
        (∑ b ∈ B, data.representation b) * data.representation y) := by
    rw [Finset.sum_mul, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [← map_mul, ← map_mul]
    rfl
  rw [hprod, irreducible_invariant_sum_eq_smul data hirr A hA,
    irreducible_invariant_sum_eq_smul data hirr B hB, smul_mul_smul, one_mul, smul_mul_assoc,
    one_mul, map_smul, smul_eq_mul]
  change (∑ a ∈ A, data.character a) / data.character 1 *
      ((∑ b ∈ B, data.character b) / data.character 1) * data.character y = _
  field_simp

theorem regular_character_sum {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (basis : FiniteIrreducibleCharacterBasis G) (g : G) :
    (∑ label, (basis.representation label).character 1 *
      (basis.representation label).character g) = if g = 1 then (Nat.card G : ℂ) else 0 := by
  by_cases hg : g = 1
  · subst hg
    rw [ite_eq_left rfl, ← finiteIrreducibleCharacterBasis_sum_degree_sq basis]
    apply Finset.sum_congr rfl
    intro label _
    ring
  · rw [ite_eq_right hg]
    exact complete_regular_character_sum basis g hg

theorem conjugacy_invariant_product_character_formula {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (basis : FiniteIrreducibleCharacterBasis G) (A B : Finset G)
    (hA : ConjInvariant A) (hB : ConjInvariant B) (x : G) :
    (productCount A B x : ℂ) = (Nat.card G : ℂ)⁻¹ * ∑ label,
      (∑ a ∈ A, (basis.representation label).character a) *
        (∑ b ∈ B, (basis.representation label).character b) *
          (basis.representation label).character x⁻¹ /
            (basis.representation label).character 1 := by
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcount : (Nat.card G : ℂ) * (productCount A B x : ℂ) =
      ∑ a ∈ A, ∑ b ∈ B, ∑ label, (basis.representation label).character 1 *
        (basis.representation label).character (a * b * x⁻¹) := by
    simp_rw [regular_character_sum basis]
    unfold productCount
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a * b = x
    · have h1 : a * b * x⁻¹ = 1 := by rw [hab, mul_inv_cancel]
      rw [ite_eq_left hab, ite_eq_left h1]
      simp
    · have h1 : a * b * x⁻¹ ≠ 1 := fun h => hab (mul_inv_eq_one.mp h)
      rw [ite_eq_right hab, ite_eq_right h1]
      simp
  have hswap : (∑ a ∈ A, ∑ b ∈ B, ∑ label, (basis.representation label).character 1 *
        (basis.representation label).character (a * b * x⁻¹)) =
      ∑ label, (basis.representation label).character 1 *
        ((∑ a ∈ A, (basis.representation label).character a) *
          (∑ b ∈ B, (basis.representation label).character b) *
            (basis.representation label).character x⁻¹ /
              (basis.representation label).character 1 ^ 2) := by
    calc (∑ a ∈ A, ∑ b ∈ B, ∑ label, (basis.representation label).character 1 *
          (basis.representation label).character (a * b * x⁻¹)) =
        ∑ a ∈ A, ∑ label, ∑ b ∈ B, (basis.representation label).character 1 *
          (basis.representation label).character (a * b * x⁻¹) := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
      _ = ∑ label, ∑ a ∈ A, ∑ b ∈ B, (basis.representation label).character 1 *
          (basis.representation label).character (a * b * x⁻¹) := Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro label _
          rw [← irreducible_character_product_sum (basis.representation label)
            (basis.irreducible label) A B hA hB x⁻¹, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
  rw [hswap] at hcount
  rw [eq_inv_mul_iff_mul_eq₀ hG, hcount]
  apply Finset.sum_congr rfl
  intro label _
  have hdeg := irreducible_character_degree_ne_zero (basis.representation label)
    (basis.irreducible label)
  field_simp

theorem productCount_inv_of_involutions {G : Type*} [Group G] [DecidableEq G] (A B : Finset G)
    (hA : ConjInvariant A) (hAinv : ∀ a ∈ A, a * a = 1) (hBinv : ∀ b ∈ B, b * b = 1) (x : G) :
    productCount A B x = productCount A B x⁻¹ := by
  unfold productCount
  apply Finset.card_nbij' (fun p => (p.2 * p.1 * p.2, p.2)) (fun p => (p.2 * p.1 * p.2, p.2))
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    have hbinv : p.2⁻¹ = p.2 := inv_eq_of_mul_eq_one_left (hBinv _ hb)
    have hainv : p.1⁻¹ = p.1 := inv_eq_of_mul_eq_one_left (hAinv _ ha)
    refine ⟨⟨?_, hb⟩, ?_⟩
    · have := (hA p.2 p.1).mp ha
      rwa [hbinv] at this
    · rw [← hab, mul_inv_rev, hbinv, hainv, mul_assoc, hBinv _ hb, mul_one]
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    have hbinv : p.2⁻¹ = p.2 := inv_eq_of_mul_eq_one_left (hBinv _ hb)
    have hainv : p.1⁻¹ = p.1 := inv_eq_of_mul_eq_one_left (hAinv _ ha)
    refine ⟨⟨?_, hb⟩, ?_⟩
    · have := (hA p.2 p.1).mp ha
      rwa [hbinv] at this
    · rw [mul_assoc, hBinv _ hb, mul_one]
      have hx : x = (p.1 * p.2)⁻¹ := by rw [hab, inv_inv]
      rw [hx, mul_inv_rev, hbinv, hainv]
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hp
    obtain ⟨⟨_, hb⟩, _⟩ := hp
    ext
    · simp only
      rw [← mul_assoc, ← mul_assoc, hBinv _ hb, one_mul, mul_assoc, hBinv _ hb, mul_one]
    · rfl
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hp
    obtain ⟨⟨_, hb⟩, _⟩ := hp
    ext
    · simp only
      rw [← mul_assoc, ← mul_assoc, hBinv _ hb, one_mul, mul_assoc, hBinv _ hb, mul_one]
    · rfl

theorem conjugacy_invariant_product_character_formula_involutions {G : Type*} [Group G]
    [Fintype G] [DecidableEq G] (basis : FiniteIrreducibleCharacterBasis G) (A B : Finset G)
    (hA : ConjInvariant A) (hB : ConjInvariant B) (hAinv : ∀ a ∈ A, a * a = 1)
    (hBinv : ∀ b ∈ B, b * b = 1) (x : G) :
    productCount A B x = productCount A B x⁻¹ ∧
    (productCount A B x : ℂ) = (Nat.card G : ℂ)⁻¹ * ∑ label,
      (∑ a ∈ A, (basis.representation label).character a) *
        (∑ b ∈ B, (basis.representation label).character b) *
          (basis.representation label).character x / (basis.representation label).character 1 := by
  have hinv := productCount_inv_of_involutions A B hA hAinv hBinv x
  refine ⟨hinv, ?_⟩
  rw [hinv, conjugacy_invariant_product_character_formula basis A B hA hB x⁻¹, inv_inv]

@[expose] noncomputable def conjClassFinset {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (a : G) : Finset G :=
  Finset.univ.filter (IsConj a)

theorem conjClassFinset_invariant {G : Type*} [Group G] [Fintype G] [DecidableEq G] (a : G) :
    ConjInvariant (conjClassFinset a) := by
  intro conjugator element
  simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact h.trans (isConj_iff.mpr ⟨conjugator, rfl⟩)
  · intro h
    exact h.trans (isConj_iff.mpr ⟨conjugator, rfl⟩).symm

theorem card_conjClassFinset_mul {G : Type*} [Group G] [Fintype G] [DecidableEq G] (a : G) :
    ((conjClassFinset a).card : ℂ) * (Nat.card (Subgroup.centralizer {a}) : ℂ) = Nat.card G := by
  have hsum : (∑ g : G, conjugatorCount a g) = (Nat.card G : ℂ) := by
    unfold conjugatorCount
    rw [Finset.sum_comm]
    trans ∑ _c : G, (1 : ℂ)
    · apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_eq_single (c * a * c⁻¹)]
      · exact ite_eq_left rfl
      · intro g _ hg
        exact ite_eq_right (Ne.symm hg)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp [Nat.card_eq_fintype_card]
  have hval : ∀ g : G, conjugatorCount a g =
      if g ∈ conjClassFinset a then (Nat.card (Subgroup.centralizer {a}) : ℂ) else 0 := by
    intro g
    by_cases hg : g ∈ conjClassFinset a
    · rw [ite_eq_left hg]
      simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      obtain ⟨c, rfl⟩ := isConj_iff.mp hg
      rw [conjugatorCount_conjugation, conjugatorCount_self]
    · rw [ite_eq_right hg]
      unfold conjugatorCount
      apply Finset.sum_eq_zero
      intro c _
      apply ite_eq_right
      intro h
      apply hg
      simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact isConj_iff.mpr ⟨c, h⟩
  simp_rw [hval] at hsum
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul] at hsum
  exact hsum

theorem character_conjClassFinset_sum {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (data : FiniteComplexRepresentation G) (a : G) :
    (∑ g ∈ conjClassFinset a, data.character g) =
      ((conjClassFinset a).card : ℂ) * data.character a := by
  rw [Finset.sum_congr rfl (fun g hg => ?_), Finset.sum_const, nsmul_eq_mul]
  simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hg
  obtain ⟨c, rfl⟩ := isConj_iff.mp hg
  exact Representation.char_conj _ a c

theorem involution_classes_product_character_formula {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (basis : FiniteIrreducibleCharacterBasis G) (a b : G) (ha : a * a = 1)
    (hb : b * b = 1) (x : G) :
    (Nat.card (Subgroup.centralizer {a}) : ℂ) * (Nat.card (Subgroup.centralizer {b}) : ℂ) *
        (productCount (conjClassFinset a) (conjClassFinset b) x : ℂ) =
      (Nat.card G : ℂ) * ∑ label, (basis.representation label).character a *
        (basis.representation label).character b * (basis.representation label).character x /
          (basis.representation label).character 1 := by
  have hinvol : ∀ c : G, c * c = 1 → ∀ g ∈ conjClassFinset c, g * g = 1 := by
    intro c hc g hg
    simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨d, rfl⟩ := isConj_iff.mp hg
    calc d * c * d⁻¹ * (d * c * d⁻¹) = d * (c * c) * d⁻¹ := by group
      _ = 1 := by rw [hc]; group
  obtain ⟨-, hformula⟩ := conjugacy_invariant_product_character_formula_involutions basis
    (conjClassFinset a) (conjClassFinset b) (conjClassFinset_invariant a)
    (conjClassFinset_invariant b) (hinvol a ha) (hinvol b hb) x
  rw [hformula]
  simp_rw [character_conjClassFinset_sum]
  have hA := card_conjClassFinset_mul a
  have hB := card_conjClassFinset_mul b
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro label _
  have hrearrange : (Nat.card (Subgroup.centralizer {a}) : ℂ) *
      (Nat.card (Subgroup.centralizer {b}) : ℂ) * ((Nat.card G : ℂ)⁻¹ *
        (((conjClassFinset a).card : ℂ) * (basis.representation label).character a *
          (((conjClassFinset b).card : ℂ) * (basis.representation label).character b) *
            (basis.representation label).character x / (basis.representation label).character 1)) =
      (((conjClassFinset a).card : ℂ) * (Nat.card (Subgroup.centralizer {a}) : ℂ)) *
        (((conjClassFinset b).card : ℂ) * (Nat.card (Subgroup.centralizer {b}) : ℂ)) *
          (Nat.card G : ℂ)⁻¹ * ((basis.representation label).character a *
            (basis.representation label).character b * (basis.representation label).character x /
              (basis.representation label).character 1) := by
    ring
  rw [hrearrange, hA, hB]
  field_simp

end CFSG.LyonsUnitaryFour
