module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.IrreducibleCount
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionIntegralColumns
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionPrincipalTransport
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasisDegreeSum
public import CFSG.CharacterTheory.Semidihedral.Principal.GL2ColumnsSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.BlockSectionOrthogonality.Helpers
  CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.GL2Columns

theorem card_sylow_two_of_card_eq_5616 {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 5616) (S : Sylow 2 G) : Nat.card S = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Nat.factorization 5616 2 = 4 := by
    have h' : (5616 : ℕ) = 2 ^ 4 * 351 := by norm_num
    rw [h', Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [S.card_eq_multiplicity, hG, h]
  norm_num

theorem label_character_one {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (l : basis.index) :
    (basis.representation l).character 1 = (Module.finrank ℂ (basis.representation l).vector : ℂ) :=
  by simp [FiniteComplexRepresentation.character, Representation.char_one]

theorem card_dvd_degree_of_vanishing {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (l : basis.index) (S : Subgroup G)
    (hvan : ∀ s ∈ S, s ≠ 1 → (basis.representation l).character s = 0) :
    ∃ m : ℕ, Module.finrank ℂ (basis.representation l).vector = Nat.card S * m := by
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := S)
  obtain ⟨θ, hθ⟩ := finiteIrreducibleCharacterBasis_exists_principal_label localBasis
  obtain ⟨m, hm⟩ := restriction_pairing_nat basis localBasis l θ
  refine ⟨m, ?_⟩
  rw [characterPairing, hθ] at hm
  have hsum : ∑ h : S, (basis.representation l).character (h : G) * (1 : S → ℂ) h⁻¹ =
      (basis.representation l).character 1 := by
    rw [Finset.sum_eq_single (1 : S)]
    · simp
    · intro h _ hh
      rw [hvan h h.2 (fun h1 => hh (Subtype.ext h1)), zero_mul]
    · simp
  rw [hsum, label_character_one] at hm
  have hcard : (Nat.card S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hc : (Module.finrank ℂ (basis.representation l).vector : ℂ) = (Nat.card S * m : ℕ) := by
    push_cast
    rw [← hm]
    field_simp
  exact_mod_cast hc

theorem irreducibles_toFinset_eq_image {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) :
    (irreducibles_finite G).toFinset =
      Finset.univ.image fun l => (basis.representation l).character := by
  ext χ
  rw [Set.Finite.mem_toFinset, Finset.mem_image]
  constructor
  · intro hχ
    obtain ⟨l, hl⟩ := exists_label_of_mem_blocksIrr basis hχ
    exact ⟨l, Finset.mem_univ _, hl⟩
  · rintro ⟨l, -, rfl⟩
    exact label_mem_blocksIrr basis l

theorem seven_character_sylow_support_degree_profile {G : Type} [Group G] [Fintype G]
    (hG : Nat.card G = 5616) (S : Sylow 2 G)
    (χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : CFSG.BlocksIrr G) (hnd : [χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇].Nodup)
    (h1 : (χ₁ : G → ℂ) ≠ 1) (h2 : (χ₂ : G → ℂ) ≠ 1) (h3 : (χ₃ : G → ℂ) ≠ 1)
    (h4 : (χ₄ : G → ℂ) ≠ 1) (h5 : (χ₅ : G → ℂ) ≠ 1) (h6 : (χ₆ : G → ℂ) ≠ 1)
    (h7 : (χ₇ : G → ℂ) ≠ 1)
    (hdeg : ![(χ₁ : G → ℂ) 1, (χ₂ : G → ℂ) 1, (χ₃ : G → ℂ) 1, (χ₄ : G → ℂ) 1,
      (χ₅ : G → ℂ) 1, (χ₆ : G → ℂ) 1, (χ₇ : G → ℂ) 1] = ![26, 27, 26, 26, 39, 12, 13])
    (hvan : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ (χ₁ : G → ℂ) → ψ ≠ (χ₂ : G → ℂ) →
      ψ ≠ (χ₃ : G → ℂ) → ψ ≠ (χ₄ : G → ℂ) → ψ ≠ (χ₅ : G → ℂ) → ψ ≠ (χ₆ : G → ℂ) →
      ψ ≠ (χ₇ : G → ℂ) → ∀ s ∈ (S : Subgroup G), s ≠ 1 → ψ s = 0) :
    commutator G = ⊤ ∧ Nat.card (ConjClasses G) = 12 ∧
    (irreducibles_finite G).toFinset.val.map (fun ψ => ψ 1) =
      ({1, 12, 13, 16, 16, 16, 16, 26, 26, 26, 27, 39} : Multiset ℂ) ∧
    (∀ ψ ∈ CFSG.BlocksIrr G, ψ 1 = 12 → ψ = χ₆) ∧
    ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ (χ₆ : G → ℂ) → ∃ d : ℕ, 12 < d ∧ ψ 1 = d := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  let c : Fin 8 → G → ℂ := ![1, χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇]
  have hcinj : Function.Injective c := injective_of_nodup hnd h1 h2 h3 h4 h5 h6 h7
  have hcirr : ∀ k, c k ∈ CFSG.BlocksIrr G := by
    intro k
    fin_cases k
    exacts [principal_mem_blocksIrr G, χ₁.2, χ₂.2, χ₃.2, χ₄.2, χ₅.2, χ₆.2, χ₇.2]
  choose lab hlab using fun k => exists_label_of_mem_blocksIrr basis (hcirr k)
  have hlabinj : Function.Injective lab := fun i j h => hcinj (by rw [← hlab i, ← hlab j, h])
  let d : Fin 8 → ℕ := ![1, 26, 27, 26, 26, 39, 12, 13]
  have hcdeg : ∀ k, c k 1 = d k := by
    intro k
    fin_cases k
    · simp [c, d]
    all_goals
      first
      | exact (congrFun hdeg 0).trans (by simp [d])
      | exact (congrFun hdeg 1).trans (by simp [d])
      | exact (congrFun hdeg 2).trans (by simp [d])
      | exact (congrFun hdeg 3).trans (by simp [d])
      | exact (congrFun hdeg 4).trans (by simp [d])
      | exact (congrFun hdeg 5).trans (by simp [d])
      | exact (congrFun hdeg 6).trans (by simp [d])
  have hlabdeg : ∀ k, Module.finrank ℂ (basis.representation (lab k)).vector = d k := by
    intro k
    have h := hcdeg k
    rw [← hlab k, label_character_one] at h
    exact_mod_cast h
  let T : Finset basis.index := Finset.univ.map ⟨lab, hlabinj⟩
  let R : Finset basis.index := Finset.univ \ T
  have hmemT : ∀ l, l ∈ T ↔ ∃ k, lab k = l := fun l => by simp [T]
  have hRvan : ∀ l ∈ R, ∀ s ∈ (S : Subgroup G), s ≠ 1 →
      (basis.representation l).character s = 0 := by
    intro l hl s hs hs1
    have hlT : ∀ k, (basis.representation l).character ≠ c k := fun k h =>
      (Finset.mem_sdiff.mp hl).2 ((hmemT l).mpr ⟨k, basis.distinct ((hlab k).trans h.symm)⟩)
    exact hvan _ (label_mem_blocksIrr basis l) (hlT 0) (hlT 1) (hlT 2) (hlT 3) (hlT 4)
      (hlT 5) (hlT 6) (hlT 7) s hs hs1
  have hS16 : Nat.card (S : Subgroup G) = 16 := card_sylow_two_of_card_eq_5616 hG S
  choose! m hm using fun l (hl : l ∈ R) =>
    card_dvd_degree_of_vanishing basis l (S : Subgroup G) (hRvan l hl)
  have hsq := finiteIrreducibleCharacterBasis_sum_finrank_sq basis
  rw [hG, ← Finset.sum_sdiff (Finset.subset_univ T)] at hsq
  have hTsum : ∑ l ∈ T, Module.finrank ℂ (basis.representation l).vector ^ 2 = 4592 := by
    rw [Finset.sum_map, Fin.sum_univ_eight]
    simp only [Function.Embedding.coeFn_mk, hlabdeg]
    simp [d]
  have hRsum : ∑ l ∈ R, Module.finrank ℂ (basis.representation l).vector ^ 2 = 1024 := by
    change ∑ l ∈ Finset.univ \ T, _ = _
    omega
  have hR16 : ∀ l ∈ R, Module.finrank ℂ (basis.representation l).vector = 16 := by
    intro l hl
    have hle : Module.finrank ℂ (basis.representation l).vector ^ 2 ≤ 1024 := by
      rw [← hRsum]
      exact Finset.single_le_sum (f := fun l => Module.finrank ℂ
        (basis.representation l).vector ^ 2) (fun _ _ => Nat.zero_le _) hl
    have hdvd : Module.finrank ℂ (basis.representation l).vector ∣ 5616 := by
      rw [← hG]
      have : (basis.representation l).representation.IsIrreducible := basis.irreducible l
      exact CFSG.Theory.Character.irreducible_dimension_dvd_group_order
        (basis.representation l).representation
    have hpos : 0 < Module.finrank ℂ (basis.representation l).vector := by
      rcases Nat.eq_zero_or_pos (Module.finrank ℂ (basis.representation l).vector) with h0 | h0
      · exfalso
        have h := hdvd
        rw [h0] at h
        norm_num at h
      · exact h0
    have hml := hm l hl
    rw [hS16] at hml
    have hm2 : m l ≤ 2 := by nlinarith
    interval_cases hmv : m l
    · omega
    · omega
    · exfalso
      rw [hml] at hdvd
      norm_num at hdvd
  have hRcard : R.card = 4 := by
    have h := hRsum
    rw [Finset.sum_congr rfl fun l hl => by rw [hR16 l hl]] at h
    simp only [Finset.sum_const, smul_eq_mul] at h
    omega
  have hTcard : T.card = 8 := by simp [T]
  have hcardidx : Fintype.card basis.index = 12 := by
    rw [← Finset.card_univ, ← Finset.card_sdiff_add_card_inter Finset.univ T,
      Finset.univ_inter, hTcard]
    change R.card + 8 = 12
    omega
  have hclasses : Nat.card (ConjClasses G) = 12 := by
    rw [← card_irreducibles_eq_card_conjClasses, irreducibles_toFinset_eq_image basis,
      Finset.card_image_of_injective _ basis.distinct, Finset.card_univ, hcardidx]
  have hlabelcases : ∀ l, (∃ k, lab k = l) ∨ l ∈ R := by
    intro l
    by_cases hl : l ∈ T
    · exact Or.inl ((hmemT l).mp hl)
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hl⟩)
  have hdegcases : ∀ ψ ∈ CFSG.BlocksIrr G, (∃ k, ψ = c k) ∨ ψ 1 = 16 := by
    intro ψ hψ
    obtain ⟨l, rfl⟩ := exists_label_of_mem_blocksIrr basis hψ
    rcases hlabelcases l with ⟨k, rfl⟩ | hl
    · exact Or.inl ⟨k, hlab k⟩
    · right
      rw [label_character_one, hR16 l hl]
      norm_num
  refine ⟨?_, hclasses, ?_, ?_, ?_⟩
  ·
    refine commutator_eq_top_of_linear_eq_one basis fun l hl => ?_
    rcases hdegcases _ (label_mem_blocksIrr basis l) with ⟨k, hk⟩ | h16
    · rw [hk] at hl ⊢
      rw [hcdeg k] at hl
      fin_cases k
      · rfl
      all_goals (exfalso; norm_num [d] at hl)
    · rw [h16] at hl
      norm_num at hl
  ·
    rw [irreducibles_toFinset_eq_image basis, Finset.image_val_of_injOn
      (fun x _ y _ h => basis.distinct h), Multiset.map_map]
    have huniv : (Finset.univ : Finset basis.index) = T.disjUnion R
        (Finset.disjoint_sdiff) := by
      rw [Finset.disjUnion_eq_union, Finset.union_sdiff_of_subset (Finset.subset_univ T)]
    rw [huniv, Finset.disjUnion_val, Multiset.map_add]
    have hTval : Multiset.map ((fun ψ : G → ℂ => ψ 1) ∘ fun l => (basis.representation l).character)
        T.val = ((({1, 26, 27, 26, 26, 39, 12, 13} : Multiset ℕ)).map (Nat.cast : ℕ → ℂ)) := by
      rw [Finset.map_val, Multiset.map_map, Fin.univ_val_map]
      have hfun : ((fun ψ : G → ℂ => ψ 1) ∘ fun l => (basis.representation l).character) ∘
          (⟨lab, hlabinj⟩ : Fin 8 ↪ basis.index) = fun k => ((d k : ℕ) : ℂ) := by
        funext k
        simp only [Function.comp_apply, Function.Embedding.coeFn_mk]
        rw [hlab k, hcdeg k]
      rw [hfun]
      simp [d, List.ofFn_succ]
      rfl
    have hRval : Multiset.map ((fun ψ : G → ℂ => ψ 1) ∘ fun l => (basis.representation l).character)
        R.val = ((Multiset.replicate 4 16 : Multiset ℕ).map (Nat.cast : ℕ → ℂ)) := by
      rw [Multiset.map_replicate]
      have hc : ∀ l ∈ R.val, ((fun ψ : G → ℂ => ψ 1) ∘ fun l =>
          (basis.representation l).character) l = ((16 : ℕ) : ℂ) := by
        intro l hl
        simp only [Function.comp_apply]
        rw [label_character_one, hR16 l hl]
      rw [Multiset.map_congr rfl hc, Multiset.map_const', Finset.card_val, hRcard]
    rw [hTval, hRval, ← Multiset.map_add]
    have hnat : ({1, 26, 27, 26, 26, 39, 12, 13} : Multiset ℕ) + Multiset.replicate 4 16 =
        {1, 12, 13, 16, 16, 16, 16, 26, 26, 26, 27, 39} := by decide
    rw [hnat]
    simp
  ·
    intro ψ hψ h12
    rcases hdegcases ψ hψ with ⟨k, rfl⟩ | h16
    · rw [hcdeg k] at h12
      fin_cases k
      all_goals first
        | rfl
        | (exfalso; norm_num [d] at h12)
    · rw [h16] at h12
      norm_num at h12
  ·
    intro ψ hψ hψ1 hψ6
    rcases hdegcases ψ hψ with ⟨k, rfl⟩ | h16
    · rw [hcdeg k]
      fin_cases k
      · exact absurd rfl hψ1
      · exact ⟨26, by norm_num, rfl⟩
      · exact ⟨27, by norm_num, rfl⟩
      · exact ⟨26, by norm_num, rfl⟩
      · exact ⟨26, by norm_num, rfl⟩
      · exact ⟨39, by norm_num, rfl⟩
      · exact absurd rfl hψ6
      · exact ⟨13, by norm_num, rfl⟩
    · exact ⟨16, by norm_num, by rw [h16]; norm_num⟩

end CFSG.Semidihedral.GL2Recognition
