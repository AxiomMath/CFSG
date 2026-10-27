module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSource

public section

namespace CFSG.ComponentClassification.UnbalancingLocal

open CFSG.Assembly.LowTwoRank

theorem small_standard_source_projective_linear_two_field_parameters_stated {X : Type} [Group X]
    {l g : ℕ} (hX : StatedClassicalModel X .PSL 2 l g) :
    (∀ p f : ℕ, p ≠ 2 → StatedClassicalModel X .PSL 2 p f →
      Xor (Odd l ∧ l = p ∧ g = f) (l = 2 ∧ g = 2 ∧ p = 5 ∧ f = 1)) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧ ¬ StatedClassicalModel X .PSL 3 2 2 := by
  obtain ⟨⟨hl, hg, -, h22, -⟩, K, _, _, hK, ⟨φ⟩⟩ := hX
  have hr1 : 1 ≤ Nat.card K := Nat.card_pos
  have hXK : Nat.card X = Nat.card (StatedProj (StatedSL 2 K)) := Nat.card_congr φ.toEquiv
  have hpar : (l = 2 ∧ Nat.card X = Nat.card K * (Nat.card K ^ 2 - 1)) ∨
      (l ≠ 2 ∧ Odd (Nat.card K) ∧ Nat.card X * 2 = Nat.card K * (Nat.card K ^ 2 - 1)) := by
    by_cases hl2 : l = 2
    · left
      refine ⟨hl2, ?_⟩
      rw [hXK]
      refine card_psl_two_of_even K ?_
      rw [hK, hl2]
      exact (Nat.even_pow' (by omega)).mpr even_two
    · right
      have hodd : Odd (Nat.card K) := by
        rw [hK]
        exact (hl.odd_of_ne_two hl2).pow
      exact ⟨hl2, hodd, by rw [hXK]; exact two_mul_card_psl_two_of_odd K hodd⟩
  refine ⟨fun p f hp2 hY => ?_, ⟨fun e => ?_⟩, fun hZ => ?_⟩
  · obtain ⟨⟨hp, hf, -⟩, K₀, _, _, hK₀, ⟨ψ⟩⟩ := hY
    have hq : Odd (Nat.card K₀) := by
      rw [hK₀]
      exact (hp.odd_of_ne_two hp2).pow
    have hq1 : 1 ≤ Nat.card K₀ := Nat.card_pos
    have hXq : Nat.card X * 2 = Nat.card K₀ * (Nat.card K₀ ^ 2 - 1) := by
      rw [Nat.card_congr ψ.toEquiv]
      exact two_mul_card_psl_two_of_odd K₀ hq
    rcases hpar with ⟨hl2, hXr⟩ | ⟨hl2, -, hXr⟩
    ·
      subst hl2
      have := Fintype.ofFinite K
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
      obtain ⟨E, hE, hEcard⟩ := exists_elementary_psl_two_even K
      have : IsElementaryAbelian 2 (E.map φ.symm.toMonoidHom) := IsElementaryAbelian.map _
      have h4 := card_le_four_of_odd_psl_two hq ψ (E.map φ.symm.toMonoidHom)
      rw [Subgroup.card_map_of_injective φ.symm.injective, hEcard, hK] at h4
      have hg2 : g = 2 := by
        have hle : g ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
          (by simpa using h4)
        have hne : g ≠ 1 := fun h => h22 (by rw [h, pow_one])
        omega
      have h60 : Nat.card K₀ * (Nat.card K₀ ^ 2 - 1) = 5 * (5 ^ 2 - 1) := by
        rw [← hXq, hXr, hK, hg2]
        norm_num
      have hq5 := eq_of_cubeSub_eq hq1 (by norm_num) h60
      rw [hK₀] at hq5
      obtain ⟨hp5, hf1⟩ := prime_pow_inj hp Nat.prime_five hf (le_refl 1)
        (hq5.trans (pow_one 5).symm)
      exact Or.inr ⟨⟨rfl, hg2, hp5, hf1⟩, fun h => Nat.not_odd_iff_even.mpr even_two h.1⟩
    ·
      have hrq := eq_of_cubeSub_eq hr1 hq1 (hXr.symm.trans hXq)
      rw [hK, hK₀] at hrq
      obtain ⟨hlp, hgf⟩ := prime_pow_inj hl hp hg hf hrq
      exact Or.inl ⟨⟨hl.odd_of_ne_two hl2, hlp, hgf⟩, fun h => hl2 h.1⟩
  ·
    have hX7 : Nat.card X = 2520 := (Nat.card_congr e.toEquiv).trans card_alternating_seven
    rcases hpar with ⟨-, hXr⟩ | ⟨-, -, hXr⟩
    · exact cubeSub_ne_of_between (a := 13) (by norm_num) (by norm_num) (by norm_num)
        (Nat.card K) (hXr.symm.trans hX7)
    · exact cubeSub_ne_of_between (a := 17) (N := 5040) (by norm_num) (by norm_num)
        (by norm_num) (Nat.card K) (by rw [← hXr, hX7])
  ·
    obtain ⟨-, K₃, _, _, hK₃, ⟨χ⟩⟩ := hZ
    have hX3 : Nat.card X = 20160 :=
      (Nat.card_congr χ.toEquiv).trans (card_psl_three_four K₃ (by rw [hK₃]; norm_num))
    rcases hpar with ⟨-, hXr⟩ | ⟨-, -, hXr⟩
    · exact cubeSub_ne_of_between (a := 27) (by norm_num) (by norm_num) (by norm_num)
        (Nat.card K) (hXr.symm.trans hX3)
    · exact cubeSub_ne_of_between (a := 34) (N := 40320) (by norm_num) (by norm_num)
        (by norm_num) (Nat.card K) (by rw [← hXr, hX3])

theorem small_standard_source_projective_linear_two_field_parameters {X : Type} [Group X]
    {l g : ℕ} [Fact l.Prime] (hX : Assembly.ComponentType.ClassicalModel X .PSL 2 l g) :
    (∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → Assembly.ComponentType.ClassicalModel X .PSL 2 p f →
      Xor (Odd l ∧ l = p ∧ g = f) (l = 2 ∧ g = 2 ∧ p = 5 ∧ f = 1)) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧
      ¬ Assembly.ComponentType.ClassicalModel X .PSL 3 2 2 := by
  obtain ⟨h1, h2, h3⟩ := small_standard_source_projective_linear_two_field_parameters_stated
    (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 2 l g hX)
  exact ⟨fun p f _ hp2 hY => h1 p f hp2
      (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 2 p f hY), h2,
    fun hZ => h3 (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 3 2 2 hZ)⟩

end CFSG.ComponentClassification.UnbalancingLocal
