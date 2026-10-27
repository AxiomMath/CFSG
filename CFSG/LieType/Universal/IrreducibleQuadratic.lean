module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LieType.Universal

theorem exists_irreducible_quadratic (F : Type*) [Field F] [Finite F] :
    ∃ b c : F, ∀ s : F, s ^ 2 + b * s + c ≠ 0 := by
  classical
  by_cases h2 : ringChar F = 2
  · have : CharP F 2 := ringChar.of_eq h2
    have hns : ¬ Function.Surjective (fun s : F => s ^ 2 + s) := by
      intro hsurj
      have hinj : Function.Injective (fun s : F => s ^ 2 + s) :=
        Finite.injective_iff_surjective.mpr hsurj
      have h01 : (fun s : F => s ^ 2 + s) 0 = (fun s : F => s ^ 2 + s) 1 := by
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, one_pow]
        exact (CharTwo.add_self_eq_zero (1 : F)).symm
      exact zero_ne_one (hinj h01)
    simp only [Function.Surjective, not_forall, not_exists] at hns
    obtain ⟨c, hc⟩ := hns
    refine ⟨1, -c, fun s hs => hc s ?_⟩
    linear_combination hs
  · obtain ⟨d, hd⟩ := FiniteField.exists_nonsquare h2
    refine ⟨0, -d, fun s hs => hd ⟨s, ?_⟩⟩
    linear_combination -hs

end CFSG.LieType.Universal
