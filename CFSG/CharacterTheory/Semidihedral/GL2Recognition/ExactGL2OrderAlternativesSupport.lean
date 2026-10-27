module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.SevenCharacterSylowSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.BlockSectionOrthogonality.Helpers
  CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.GL2Columns

theorem card_sylow_two_of_card_eq_7920 {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 7920) (S : Sylow 2 G) : Nat.card S = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Nat.factorization 7920 2 = 4 := by
    have h' : (7920 : ℕ) = 2 ^ 4 * 495 := by norm_num
    rw [h', Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [S.card_eq_multiplicity, hG, h]
  norm_num

theorem seven_character_sylow_support_degree_profile_7920 {G : Type} [Group G] [Fintype G]
    (hG : Nat.card G = 7920) (S : Sylow 2 G)
    (χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : CFSG.BlocksIrr G) (hnd : [χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇].Nodup)
    (h1 : (χ₁ : G → ℂ) ≠ 1) (h2 : (χ₂ : G → ℂ) ≠ 1) (h3 : (χ₃ : G → ℂ) ≠ 1)
    (h4 : (χ₄ : G → ℂ) ≠ 1) (h5 : (χ₅ : G → ℂ) ≠ 1) (h6 : (χ₆ : G → ℂ) ≠ 1)
    (h7 : (χ₇ : G → ℂ) ≠ 1)
    (hdeg : ![(χ₁ : G → ℂ) 1, (χ₂ : G → ℂ) 1, (χ₃ : G → ℂ) 1, (χ₄ : G → ℂ) 1,
      (χ₅ : G → ℂ) 1, (χ₆ : G → ℂ) 1, (χ₇ : G → ℂ) 1] = ![10, 11, 10, 10, 55, 44, 45])
    (hvan : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ (χ₁ : G → ℂ) → ψ ≠ (χ₂ : G → ℂ) →
      ψ ≠ (χ₃ : G → ℂ) → ψ ≠ (χ₄ : G → ℂ) → ψ ≠ (χ₅ : G → ℂ) → ψ ≠ (χ₆ : G → ℂ) →
      ψ ≠ (χ₇ : G → ℂ) → ∀ s ∈ (S : Subgroup G), s ≠ 1 → ψ s = 0) :
    commutator G = ⊤ ∧ Nat.card (ConjClasses G) = 10 ∧
    (irreducibles_finite G).toFinset.val.map (fun ψ => ψ 1) =
      ({1, 10, 10, 10, 11, 16, 16, 44, 45, 55} : Multiset ℂ) ∧
    ∃ ψ₁ ∈ CFSG.BlocksIrr G, ∃ ψ₂ ∈ CFSG.BlocksIrr G, ψ₁ ≠ ψ₂ ∧ ψ₁ 1 = 16 ∧ ψ₂ 1 = 16 ∧
      ∀ ψ ∈ CFSG.BlocksIrr G, ψ = 1 ∨ ψ = (χ₁ : G → ℂ) ∨ ψ = (χ₂ : G → ℂ) ∨
        ψ = (χ₃ : G → ℂ) ∨ ψ = (χ₄ : G → ℂ) ∨ ψ = (χ₅ : G → ℂ) ∨ ψ = (χ₆ : G → ℂ) ∨
        ψ = (χ₇ : G → ℂ) ∨ ψ = ψ₁ ∨ ψ = ψ₂ := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  let c : Fin 8 → G → ℂ := ![1, χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇]
  have hcinj : Function.Injective c := injective_of_nodup hnd h1 h2 h3 h4 h5 h6 h7
  have hcirr : ∀ k, c k ∈ CFSG.BlocksIrr G := by
    intro k
    fin_cases k
    exacts [principal_mem_blocksIrr G, χ₁.2, χ₂.2, χ₃.2, χ₄.2, χ₅.2, χ₆.2, χ₇.2]
  choose lab hlab using fun k => exists_label_of_mem_blocksIrr basis (hcirr k)
  have hlabinj : Function.Injective lab := fun i j h => hcinj (by rw [← hlab i, ← hlab j, h])
  let d : Fin 8 → ℕ := ![1, 10, 11, 10, 10, 55, 44, 45]
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
  have hS16 : Nat.card (S : Subgroup G) = 16 := card_sylow_two_of_card_eq_7920 hG S
  choose! m hm using fun l (hl : l ∈ R) =>
    card_dvd_degree_of_vanishing basis l (S : Subgroup G) (hRvan l hl)
  have hsq := finiteIrreducibleCharacterBasis_sum_finrank_sq basis
  rw [hG, ← Finset.sum_sdiff (Finset.subset_univ T)] at hsq
  have hTsum : ∑ l ∈ T, Module.finrank ℂ (basis.representation l).vector ^ 2 = 7408 := by
    rw [Finset.sum_map, Fin.sum_univ_eight]
    simp only [Function.Embedding.coeFn_mk, hlabdeg]
    simp [d]
  have hRsum : ∑ l ∈ R, Module.finrank ℂ (basis.representation l).vector ^ 2 = 512 := by
    change ∑ l ∈ Finset.univ \ T, _ = _
    omega
  have hR16 : ∀ l ∈ R, Module.finrank ℂ (basis.representation l).vector = 16 := by
    intro l hl
    have hle : Module.finrank ℂ (basis.representation l).vector ^ 2 ≤ 512 := by
      rw [← hRsum]
      exact Finset.single_le_sum (f := fun l => Module.finrank ℂ
        (basis.representation l).vector ^ 2) (fun _ _ => Nat.zero_le _) hl
    have hpos : 0 < Module.finrank ℂ (basis.representation l).vector := by
      have h := irreducible_character_degree_ne_zero (basis.representation l)
        (basis.irreducible l)
      rw [label_character_one] at h
      exact Nat.pos_of_ne_zero (by exact_mod_cast h)
    have hml := hm l hl
    rw [hS16] at hml
    have hm1 : m l ≤ 1 := by nlinarith
    interval_cases hmv : m l
    · omega
    · omega
  have hRcard : R.card = 2 := by
    have h := hRsum
    rw [Finset.sum_congr rfl fun l hl => by rw [hR16 l hl]] at h
    simp only [Finset.sum_const, smul_eq_mul] at h
    omega
  have hTcard : T.card = 8 := by simp [T]
  have hcardidx : Fintype.card basis.index = 10 := by
    rw [← Finset.card_univ, ← Finset.card_sdiff_add_card_inter Finset.univ T,
      Finset.univ_inter, hTcard]
    change R.card + 8 = 10
    omega
  have hclasses : Nat.card (ConjClasses G) = 10 := by
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
  obtain ⟨l₁, l₂, hl12, hR12⟩ := Finset.card_eq_two.mp hRcard
  have hl₁R : l₁ ∈ R := by rw [hR12]; simp
  have hl₂R : l₂ ∈ R := by rw [hR12]; simp
  refine ⟨?_, hclasses, ?_, (basis.representation l₁).character, label_mem_blocksIrr basis l₁,
    (basis.representation l₂).character, label_mem_blocksIrr basis l₂,
    fun h => hl12 (basis.distinct h), by rw [label_character_one, hR16 l₁ hl₁R]; norm_num,
    by rw [label_character_one, hR16 l₂ hl₂R]; norm_num, ?_⟩
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
        T.val = ((({1, 10, 11, 10, 10, 55, 44, 45} : Multiset ℕ)).map (Nat.cast : ℕ → ℂ)) := by
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
        R.val = ((Multiset.replicate 2 16 : Multiset ℕ).map (Nat.cast : ℕ → ℂ)) := by
      rw [Multiset.map_replicate]
      have hc : ∀ l ∈ R.val, ((fun ψ : G → ℂ => ψ 1) ∘ fun l =>
          (basis.representation l).character) l = ((16 : ℕ) : ℂ) := by
        intro l hl
        simp only [Function.comp_apply]
        rw [label_character_one, hR16 l hl]
      rw [Multiset.map_congr rfl hc, Multiset.map_const', Finset.card_val, hRcard]
    rw [hTval, hRval, ← Multiset.map_add]
    have hnat : ({1, 10, 11, 10, 10, 55, 44, 45} : Multiset ℕ) + Multiset.replicate 2 16 =
        {1, 10, 10, 10, 11, 16, 16, 44, 45, 55} := by decide
    rw [hnat]
    simp
  ·
    intro ψ hψ
    obtain ⟨l, rfl⟩ := exists_label_of_mem_blocksIrr basis hψ
    rcases hlabelcases l with ⟨k, rfl⟩ | hl
    · rw [hlab k]
      fin_cases k
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    · rw [hR12] at hl
      rcases Finset.mem_insert.mp hl with rfl | hl'
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl rfl))))))))
      · rw [Finset.mem_singleton.mp hl']
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr rfl))))))))

end CFSG.Semidihedral.GL2Recognition
