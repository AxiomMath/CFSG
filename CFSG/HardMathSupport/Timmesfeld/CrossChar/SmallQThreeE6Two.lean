module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoBalance

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.TableBExc.E6Three CFSG.HardMathSupport.Solomon.LocalBalance

variable {K : Type} [Field K] [Finite K]

theorem charP_two_of_card_two_E6 (hK : Nat.card K = 2) : CharP K 2 := by
  refine (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 ?_
  have h01 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have hu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
      have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 hu).1
      exact congrArg Units.val (Subsingleton.elim (Units.mk0 c hc) 1)
  rcases h01 (2 : K) with h | h
  · exact_mod_cast h
  · exfalso
    have : (1 : K) = 0 := by
      have e : (2 : K) = 1 + 1 := by norm_num
      rw [e] at h
      exact add_eq_left.1 h
    exact one_ne_zero this

theorem innerOneBalanceThree_E6_two_of_fusion (hK : Nat.card K = 2)
    (hfus : ∀ x : adjointGroup .E6 K, x ^ 3 = 1 → x ≠ 1 → ∃ c : adjointGroup .E6 K,
      c * x * c⁻¹ = uE6Two 0 ∨ c * x * c⁻¹ = uE6Two 0 * uE6Two 3 ∨
        c * x * c⁻¹ = uE6Two 0 * uE6Two 2 * uE6Two 3) :
    InnerOneBalanceThree (adjointGroup .E6 K) := by
  have : CharP K 2 := charP_two_of_card_two_E6 hK
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  refine SmallQ3.innerOneBalanceThree_of_toral
    (mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K))
    {uE6Two 0, uE6Two 0 * uE6Two 3, uE6Two 0 * uE6Two 2 * uE6Two 3} ?_ ?_ ?_
  · intro s hs3 hs1
    obtain ⟨c, hc⟩ := hfus s hs3 hs1
    refine ⟨c, ?_⟩
    rcases hc with h | h | h <;> simp [h]
  · rintro t (rfl | rfl | rfl)
    · exact gLAPPrimeCoreOf_centralizer_u0 hK
    · exact gLAPPrimeCoreOf_centralizer_u0u3 hK
    · exact gLAPPrimeCoreOf_centralizer_u0u2u3 hK
  · rintro t (rfl | rfl | rfl) α hα
    · exact mem_innerAut_of_fix_u0 hK α hα
    · exact mem_innerAut_of_fix_u0u3 hK α hα
    · exact mem_innerAut_of_fix_u0u2u3 hK α hα

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
