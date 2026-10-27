module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open scoped commutatorElement

variable {G Y : Type*} [Group G] [Group Y]

theorem injective_restrict_of_inf_eq_bot (ρ : G →* Y) {A Z : Subgroup G}
    (hker : ∀ g ∈ ρ.ker, g ∈ Z) (hA : A ⊓ Z = ⊥) :
    Function.Injective (ρ.comp A.subtype) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : (a : G) ∈ ρ.ker := ha
  have h2 : (a : G) ∈ A ⊓ Z := ⟨a.2, hker _ h1⟩
  rw [hA, Subgroup.mem_bot] at h2
  exact Subtype.ext h2

theorem card_le_of_pRank_of_comap [Finite G] [Finite Y] (ρ : G →* Y) {Z : Subgroup G}
    (hker : ∀ g ∈ ρ.ker, g ∈ Z) (P : Subgroup Y) {k : ℕ} (hP : CFSG.Open.pRank 3 P ≤ k)
    {A' : Subgroup G} (hA' : A' ≤ P.comap ρ) (hAe : CFSG.Open.IsElemAbelian 3 A')
    (hAZ : A' ⊓ Z = ⊥) {j : ℕ} (hj : Nat.card A' = 3 ^ j) : j ≤ k := by
  have hinj := injective_restrict_of_inf_eq_bot ρ hker hAZ
  have hrange : (ρ.comp A'.subtype).range = A'.map ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card (A'.map ρ) = Nat.card A' := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hmem : j ∈ {k | ∃ E : Subgroup Y, E ≤ P ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} := by
    refine ⟨A'.map ρ, ?_, ?_, by rw [hcard, hj]⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact hA' ha
    · have h1 : IsMulCommutative A' := hAe.1
      refine ⟨⟨⟨?_⟩⟩, ?_⟩
      · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
        apply Subtype.ext
        show ρ a * ρ b = ρ b * ρ a
        rw [← map_mul, ← map_mul]
        congr 1
        exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A') ⟨b, hb⟩)
      · rintro _ ⟨a, ha, rfl⟩
        rw [← map_pow, hAe.2 a ha, map_one]
  have hbdd : BddAbove {k | ∃ E : Subgroup Y, E ≤ P ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k} := by
    refine ⟨Nat.card Y, ?_⟩
    rintro k ⟨E, -, -, hE⟩
    have h1 : 3 ^ k ≤ Nat.card Y := hE ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card E)
    exact (Nat.lt_pow_self (by norm_num : 1 < 3)).le.trans h1
  exact (le_csSup hbdd hmem).trans hP

end CFSG.HardMathSupport.Curtis.UnitaryLevi
