module

public import CFSG.LieType.SeitzGeneration.OuterQuotient
public import CFSG.LocalAnalysis.SubfieldPairReeG2.Assembly
public import CFSG.RankThree.PartOne.SEITZRF.Two

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.RankThree.PartOne.CTP CFSG.ComponentClassification.OuterAutomorphisms

section OuterCoprime

theorem fieldAutData_of_not_dvd_card_outer {K : Type} [Group K] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (Outer K)) : FieldAutData K p := by
  have hcop : Nat.Coprime p (Nat.card (Outer K)) := (Nat.Prime.coprime_iff_not_dvd hp).mpr h
  have hinner : ∀ σ : MulAut K, orderOf σ = p → ∃ g : K, MulAut.conj g = σ := fun σ hσ =>
    MonoidHom.mem_range.mp (CFSG.LieType.SeitzGeneration.le_inner_of_coprime_card_outer
      (E := Subgroup.zpowers σ) (by rwa [Nat.card_zpowers, hσ]) (Subgroup.mem_zpowers σ))
  refine ⟨fun E _ hEc => ?_, fun σ hσ => ?_, fun σ τ hσ => ?_⟩
  · have hle := CFSG.LieType.SeitzGeneration.le_inner_of_coprime_card_outer (E := E)
      (by rw [hEc]; exact Nat.Coprime.pow_left 2 hcop)
    have hne : E ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hEc
      exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne hEc
    obtain ⟨⟨φ, hφE⟩, hφ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hle hφE)
    refine ⟨g, ?_, by rw [hg]; exact hφE⟩
    rintro rfl
    exact hφ1 (Subtype.ext (show φ = 1 by rw [← hg, map_one]))
  · obtain ⟨g, hg⟩ := hinner σ hσ.1
    exact (hσ.2 g hg.symm).elim
  · obtain ⟨g, hg⟩ := hinner σ hσ.1
    exact (hσ.2 g hg.symm).elim

end OuterCoprime

section ReeG2


theorem fieldAutData_five_reeG2 {L : Type} [Group L] [Finite L] {ℓ f : ℕ}
    (hM : CFSG.Blueprint.ReeTitsModel L .twistedG2 ℓ f) :
    CFSG.RankThree.PartOne.CTP.FieldAutData L 5 := by
  obtain ⟨-, -, rfl, ⟨b, hb, hfb⟩, hmain⟩ := CFSG.LieType.Ree.small_Ree_model_Schreier L ℓ f hM
  obtain ⟨-, a, hfa, K, _, _, hK, ⟨e⟩⟩ := hM
  have ha : 1 ≤ a := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K CFSG.LieType.Ree.ReeTag.G2.prime :=
    charP_of_card_eq_prime_pow (p := 3) (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨E⟩ := hmain a K hfa hK ⟨e⟩
  exact (CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.fieldAutData_reeG2
    CFSG.LocalAnalysis.SubfieldPairReeG2.subfieldPairReeG2_of_pieces Nat.prime_five le_rfl ha
    (by rw [← hfa]; exact hK)).of_mulEquiv E Nat.prime_five

end ReeG2

section ReeF4


theorem fieldAutData_five_reeF4 {L : Type} [Group L] [Finite L] {ℓ f : ℕ}
    (hM : CFSG.Blueprint.ReeTitsModel L .twistedF4 ℓ f) :
    CFSG.RankThree.PartOne.CTP.FieldAutData L 5 := by
  obtain ⟨-, -, -, rfl, ⟨b, hb, hfb⟩, hmain⟩ :=
    CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier L ℓ f hM
  obtain ⟨-, a, hfa, K, _, _, hK, ⟨e⟩⟩ := hM
  have ha : 1 ≤ a := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime :=
    charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨E⟩ := hmain a K hfa hK ⟨e⟩
  exact (CFSG.RankThree.PartOne.SEITZ2.fieldAutData_reeF4
    CFSG.RankThree.PartOne.SEITZRF.subfieldPairReeF4_holds Nat.prime_five le_rfl ha
    (by rw [← hfa]; exact hK)).of_mulEquiv E Nat.prime_five

end ReeF4

section Tits


theorem fieldAutData_five_tits {L : Type} [Group L] [Finite L] {ℓ f : ℕ}
    (hM : CFSG.Blueprint.ReeTitsModel L .Tits ℓ f) :
    CFSG.RankThree.PartOne.CTP.FieldAutData L 5 := by
  refine fieldAutData_of_not_dvd_card_outer Nat.prime_five ?_
  rw [(CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound L ℓ f hM).2.2.1]
  norm_num

end Tits

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
