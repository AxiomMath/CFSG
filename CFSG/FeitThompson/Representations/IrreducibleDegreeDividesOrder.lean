module

public import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.RationalAlgebraicIntegerIsInteger
import CFSG.FeitThompson.Representations.CentralCharacterClassSumIntegral
import CFSG.FeitThompson.Representations.DegreeQuotientCentralCharacterSum
import CFSG.FeitThompson.Representations.CharacterValuesAlgebraicIntegers

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

namespace Representation

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

theorem isIntegral_card_div_character_one [Finite G] (ρ : _root_.Representation ℂ G V)
    [ρ.IsIrreducible] : IsIntegral ℤ ((Nat.card G : ℂ) / ρ.character 1) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (ConjClasses G) := Fintype.ofFinite _
  set x : ConjClasses G → G := fun K => (ConjClasses.exists_rep K).choose with hxdef
  have hx : ∀ K, ConjClasses.mk (x K) = K := fun K => (ConjClasses.exists_rep K).choose_spec
  rw [card_div_character_one_eq_sum ρ x hx]
  refine IsIntegral.sum _ fun K _ => IsIntegral.mul ?_ ?_
  · rw [← card_conjClassFinset_eq_card_carrier (hx K)]
    exact isIntegral_card_conjClass_mul_character_div ρ (x K)
  · exact isIntegral_character ρ _

theorem finrank_dvd_card [Finite G] (ρ : _root_.Representation ℂ G V) [ρ.IsIrreducible] :
    finrank ℂ V ∣ Nat.card G := by
  have := nontrivial_of_isIrreducible ρ ‹_›
  have hd : 0 < finrank ℂ V := Module.finrank_pos
  have hchar : ρ.character 1 = (finrank ℂ V : ℂ) := ρ.char_one
  have hrat : ∃ q : ℚ, (Nat.card G : ℂ) / ρ.character 1 = (q : ℂ) :=
    ⟨(Nat.card G : ℚ) / (finrank ℂ V : ℚ), by rw [hchar]; push_cast; ring⟩
  obtain ⟨n, hn⟩ := (Complex.isIntegral_int_iff_exists_int_of_exists_rat hrat).1
    (isIntegral_card_div_character_one ρ)
  have hne : (finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  rw [hchar, div_eq_iff hne] at hn
  have hz : (Nat.card G : ℤ) = n * (finrank ℂ V : ℤ) := by exact_mod_cast hn
  exact Int.ofNat_dvd.1 ⟨n, by rw [hz]; ring⟩

theorem character_one_eq_natCast_and_dvd [Finite G] (ρ : _root_.Representation ℂ G V)
    [ρ.IsIrreducible] :
    0 < finrank ℂ V ∧ ρ.character 1 = (finrank ℂ V : ℂ) ∧ finrank ℂ V ∣ Nat.card G :=
  have := nontrivial_of_isIrreducible ρ ‹_›
  ⟨Module.finrank_pos, ρ.char_one, finrank_dvd_card ρ⟩

end Representation

theorem Irr.exists_degree {G : Type*} [Group G] [Finite G] {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    ∃ n : ℕ, 0 < n ∧ χ 1 = (n : ℂ) ∧ n ∣ Nat.card G := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hχ
  have := hW
  exact ⟨finrank ℂ W.V, Representation.character_one_eq_natCast_and_dvd W.ρ⟩

theorem irreducibleCharacters.exists_degree {G : Type*} [Group G] [Finite G] {χ : G → ℂ}
    (hχ : χ ∈ irreducibleCharacters G) :
    ∃ n : ℕ, 0 < n ∧ χ 1 = (n : ℂ) ∧ n ∣ Nat.card G := by
  obtain ⟨W, hW, rfl⟩ := mem_irreducibleCharacters_iff.1 hχ
  have := hW
  exact ⟨finrank ℂ W.V, Representation.character_one_eq_natCast_and_dvd W.ρ⟩

theorem Irr.character_one_dvd_card_int {G : Type*} [Group G] [Finite G] {χ : G → ℂ}
    (hχ : χ ∈ Irr G) : ∃ n : ℤ, χ 1 = (n : ℂ) ∧ n ∣ (Nat.card G : ℤ) := by
  obtain ⟨n, -, hn, hdvd⟩ := Irr.exists_degree hχ
  exact ⟨n, by exact_mod_cast hn, Int.natCast_dvd_natCast.2 hdvd⟩

end CFSG.FeitThompson
