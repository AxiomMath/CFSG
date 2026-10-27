module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteCore
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsRank

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup

theorem footeRankThree :
    ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f → p ^ f ≠ 9 →
      Blueprint.LieModel S .PSL 2 p f → ∀ E : Subgroup (MulAut S), (∀ e ∈ E, e * e = 1) →
        8 ≤ Nat.card E →
          ∃ e ∈ E, e ≠ 1 ∧
            ¬ Group.IsSolvable ↥(MonoidHom.eqLocus e.toMonoidHom (MonoidHom.id S)) := by
  intro S _ _ p f hp hp2 hf h9 hS E hE2 hE8
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hS
  have hodd := isOddPrimePower_of hp hp2 hf hF
  set E' := E.map (autEquiv e).toMonoidHom
  have hE'2 : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    change autEquiv e y * autEquiv e y = 1
    rw [← map_mul, hE2 y hy, map_one]
  have hE'8 : 8 ≤ Nat.card E' := by
    rw [Subgroup.card_map_of_injective (autEquiv e).injective]
    exact hE8
  have hlin : Nat.card (linearPart E') ≤ 4 :=
    pgl2_card_le_four_of_sq hodd _ fun g hg => SemidirectProduct.inl_injective (by
      rw [map_mul, map_one]; exact hE'2 _ hg)
  obtain ⟨y, hyE, hyr⟩ : ∃ y ∈ E', y.right ≠ 1 := by
    by_contra h
    push Not at h
    have hpi : Nat.card (E'.map (fieldProj F)) ≤ 1 := by
      apply Finite.card_le_one_iff_subsingleton.mpr
      constructor
      rintro ⟨_, ⟨a, ha, rfl⟩⟩ ⟨_, ⟨b, hb, rfl⟩⟩
      apply Subtype.ext
      change a.right = b.right
      rw [h a ha, h b hb]
    have := card_eq_linearPart_mul E'
    have : 8 ≤ 4 * 1 := by
      calc 8 ≤ Nat.card E' := hE'8
        _ = _ := this
        _ ≤ 4 * 1 := Nat.mul_le_mul hlin hpi
    omega
  obtain ⟨e₀, he₀, rfl⟩ := hyE
  have hg2 : autEquiv e e₀ * autEquiv e e₀ = 1 := by rw [← map_mul, hE2 e₀ he₀, map_one]
  refine ⟨e₀, he₀, fun h => hyr ?_, ?_⟩
  · change (autEquiv e e₀).right = 1
    rw [h, map_one]
    rfl
  · obtain ⟨hσ, ⟨ρ⟩⟩ := eqLocus_equiv_fieldCent hodd e e₀ hg2 hyr
    obtain ⟨K₀, hK₀, hcard, -⟩ := exists_fixed_subfield _ hσ
    have hFodd : Odd (Nat.card F) := by
      obtain ⟨p', n, -, hpodd, -, hc⟩ := hodd
      rw [hc]
      exact hpodd.pow
    have hK₀odd : IsOddPrimePower (Nat.card K₀) := by
      apply isOddPrimePower_of_odd_card
      rw [hcard] at hFodd
      exact Nat.Odd.of_mul_left (by rwa [← pow_two])
    have h3 : 3 < Nat.card K₀ := by
      obtain ⟨p', n, hp', hpodd, hn, hc⟩ := hK₀odd
      have hp3 : 3 ≤ p' := by
        have := hp'.two_le
        rcases hpodd with ⟨m, hm⟩
        omega
      have hge : 3 ≤ Nat.card K₀ := by
        rw [hc]
        calc 3 ≤ p' := hp3
          _ = p' ^ 1 := (pow_one p').symm
          _ ≤ p' ^ n := Nat.pow_le_pow_right (by omega) hn
      have hne : Nat.card K₀ ≠ 3 := by
        intro h3
        apply h9
        rw [← hF, hcard, h3]
        norm_num
      omega
    intro hsolv
    exact not_isSolvable_fieldCent hK₀ hK₀odd h3
      (Group.isSolvable_of_isSolvable_injective (f := ρ.symm.toMonoidHom) ρ.symm.injective)

end CFSG.ComponentClassification.AutL2Facts
