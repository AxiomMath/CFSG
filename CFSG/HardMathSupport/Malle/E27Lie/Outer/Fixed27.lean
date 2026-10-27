module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Fixed

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_fixed_three_subgroup_of_dvd {K : Type} [Group K] [Finite K] (u : MulAut K)
    (h : 27 ∣ Nat.card (fixedSubgroup u)) :
    ∃ Q : Subgroup K, (∀ x ∈ Q, u x = x) ∧ IsPGroup 3 Q ∧ 27 ≤ Nat.card Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 ↥(fixedSubgroup u)))
  refine ⟨(P : Subgroup ↥(fixedSubgroup u)).map (fixedSubgroup u).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · exact P.isPGroup'.map _
  · rw [Subgroup.card_map_of_injective (fixedSubgroup u).subtype_injective,
      Sylow.card_eq_multiplicity P]
    have h3 : 3 ^ 3 ∣ Nat.card (fixedSubgroup u) := by simpa using h
    have hne : Nat.card (fixedSubgroup u) ≠ 0 := Nat.card_pos.ne'
    have : 3 ≤ (Nat.card (fixedSubgroup u)).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).1 h3
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (Nat.card (fixedSubgroup u)).factorization 3 :=
        Nat.pow_le_pow_right (by norm_num) this

theorem false_of_dvd_twentySeven {K : Type} [Group K] [Finite K] (u : MulAut K)
    (hQ : ∀ Q : Subgroup K, (∀ x ∈ Q, u x = x) → IsPGroup 3 Q → Nat.card Q ≤ 9)
    (h : 27 ∣ Nat.card (fixedSubgroup u)) : False := by
  obtain ⟨Q, hfix, hQ3, hcard⟩ := exists_fixed_three_subgroup_of_dvd u h
  have := hQ Q hfix hQ3
  omega

section


theorem card_adjointGroup_dvd_card_fixedSubgroup {τ : Tag} {M : Type} [Field M] [Finite M]
    (σ : M ≃+* M) :
    Nat.card (adjointGroup τ (fixSubfield σ)) ∣
      Nat.card (fixedSubgroup (entrywiseAdjointAut τ σ)) := by
  rw [CFSG.HardMathSupport.Lang.E6Descent.card_fixedSubgroup_entrywiseAdjointAut,
    Nat.card_congr (fixedFieldImageEquiv (τ := τ) σ).toEquiv]
  exact Subgroup.card_dvd_of_le fixedFieldImage_le

end

end CFSG.HardMathSupport.Malle.E27Lie
