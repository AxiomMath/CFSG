module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbDefs
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbVoidCore
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
open scoped commutatorElement

theorem isSolvable_of_card_two_pow_mul_three_pow {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h])

theorem exists_two_pow_mul_three_pow_of_dvd_ninetySix {d : ℕ} (h : d ∣ 96) :
    ∃ a b : ℕ, d = 2 ^ a * 3 ^ b := by
  obtain ⟨d1, d2, h1, h2, rfl⟩ := Nat.dvd_mul.1 (show d ∣ 2 ^ 5 * 3 ^ 1 from h)
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
  exact ⟨a, b, rfl⟩

theorem isSolvable_of_card_dvd_ninetySix {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ∣ 96) : Group.IsSolvable G := by
  obtain ⟨a, b, hab⟩ := exists_two_pow_mul_three_pow_of_dvd_ninetySix h
  exact isSolvable_of_card_two_pow_mul_three_pow hab

section Void

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}

omit [Finite Y] in
theorem le_normalizer_centralizer_aux (Lb : Subgroup Y) :
    Lb ≤ Subgroup.normalizer (Subgroup.centralizer (Lb : Set Y) : Set Y) := by
  have key : ∀ g ∈ Lb, ∀ c, c ∈ Subgroup.centralizer (Lb : Set Y) → g * c * g⁻¹ ∈
      Subgroup.centralizer (Lb : Set Y) := by
    intro g hg c hc
    have : g * c * g⁻¹ = c := by
      rw [Subgroup.mem_centralizer_iff.mp hc g hg]; group
    rwa [this]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have := key g⁻¹ (Lb.inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem blockIb_false_of_isSolvable (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x)
    (hsol : Group.IsSolvable ↥Pb) : False := by
  have hPL : Pb ≤ Lb := hP.parab.1
  have hDC : D ≤ Subgroup.centralizer (Lb : Set Y) :=
    le_of_perfect_of_isSolvable (hPL.trans (le_normalizer_centralizer_aux Lb)) hsol hD.Dperf hD.Dle
  exact hD.hxC (hDC hD.hx)

end Void

end CFSG.HardMathSupport.Curtis.UnitaryLevi
