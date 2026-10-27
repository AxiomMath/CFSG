module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Foundations.SolvablePerfectTrivial
import CFSG.FeitThompson.Foundations.DerivedSubgroupCharacteristic
import CFSG.FeitThompson.Representations.LinearCharactersSeparateElements
import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable (H : Type*) [Group H]

theorem commutator_ne_top_of_isSolvable [Group.IsSolvable H] [Nontrivial H] :
    _root_.commutator H ≠ ⊤ := fun h =>
  not_subsingleton H (subsingleton_of_isSolvable_of_commutator_eq_top H h)

theorem isMulCommutative_abelianization : IsMulCommutative (Abelianization H) :=
  isMulCommutative_quotient_commutator H

theorem nontrivial_abelianization_of_isSolvable [Group.IsSolvable H] [Nontrivial H] :
    Nontrivial (Abelianization H) :=
  QuotientGroup.nontrivial_iff.2 (commutator_ne_top_of_isSolvable H)

theorem abelianization_of_surjective :
    Function.Surjective (Abelianization.of : H →* Abelianization H) := by
  intro q
  induction q using Quot.ind with
  | _ g => exact ⟨g, Abelianization.mk_eq_of g⟩

theorem finite_abelianization [Finite H] : Finite (Abelianization H) :=
  Finite.of_surjective _ (abelianization_of_surjective H)

theorem exists_mem_Irr_apply_one_eq_one_and_ne_one
    [Finite H] [Group.IsSolvable H] [Nontrivial H] :
    ∃ χ ∈ Irr H, χ 1 = 1 ∧ χ ≠ 1 := by
  have := nontrivial_abelianization_of_isSolvable H
  have := finite_abelianization H
  obtain ⟨q, hq⟩ := exists_ne (1 : Abelianization H)
  obtain ⟨χ, hχ, hne⟩ := exists_mem_Irr_apply_ne_one (A := Abelianization H) hq
  refine ⟨χ ∘ (Abelianization.of : H →* Abelianization H),
    irrTrivialOn_subset_Irr (mem_irrTrivialOn_comp_mk (N := _root_.commutator H) hχ), ?_, ?_⟩
  · rw [show (χ ∘ (Abelianization.of : H →* Abelianization H)) 1 = χ 1 from rfl,
      Irr.apply_one_eq_one hχ]
  · intro h
    obtain ⟨g, rfl⟩ := abelianization_of_surjective H q
    exact hne (by simpa using congrFun h g)

theorem exists_monoidHom_units_ne_one_of_isSolvable
    [Finite H] [Group.IsSolvable H] [Nontrivial H] :
    ∃ ψ : H →* ℂˣ, (fun g => (ψ g : ℂ)) ∈ Irr H ∧ ψ ≠ 1 := by
  have := nontrivial_abelianization_of_isSolvable H
  have := finite_abelianization H
  obtain ⟨q, hq⟩ := exists_ne (1 : Abelianization H)
  obtain ⟨χ, hχ, hne⟩ := exists_mem_Irr_apply_ne_one (A := Abelianization H) hq
  obtain ⟨ψ, rfl⟩ := exists_linearCharFun_eq_of_mem_Irr hχ
  refine ⟨ψ.comp (Abelianization.of : H →* Abelianization H), ?_, ?_⟩
  · have h : (fun g => ((ψ.comp (Abelianization.of : H →* Abelianization H)) g : ℂ))
        = linearCharFun ψ ∘ (Abelianization.of : H →* Abelianization H) := by
      funext g; simp
    rw [h]
    exact irrTrivialOn_subset_Irr (mem_irrTrivialOn_comp_mk (N := _root_.commutator H) hχ)
  · intro h
    obtain ⟨g, rfl⟩ := abelianization_of_surjective H q
    have hg := congrArg (fun f : H →* ℂˣ => (f g : ℂ)) h
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.one_apply, Units.val_one] at hg
    exact hne (by simpa using hg)

end CFSG.FeitThompson
