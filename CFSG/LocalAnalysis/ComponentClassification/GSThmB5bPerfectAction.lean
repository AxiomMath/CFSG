module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bAction

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {H : Type} [Group H]

theorem mem_coreActionKernel_of_perfect_of_solvable {A : Type*} [Group A] [Group.IsPerfect A]
    {J : Subgroup H} (f : A →* ↥(normalizer (J : Set H)))
    (hsol : Group.IsSolvable ((oddBarConj J).comp f).range) (x : A) :
    (f x : H) ∈ coreActionKernel J := by
  have h1 := SolvableKernelContainment.hom_eq_one ((oddBarConj J).comp f).rangeRestrict
  have h2 : ((oddBarConj J).comp f).rangeRestrict x = 1 := by rw [h1]; rfl
  have h3 : oddBarConj J (f x) = 1 := by
    have := congrArg Subtype.val h2
    simpa using this
  exact mem_coreActionKernel_of_oddBarConj_eq_one h3

theorem mem_coreActionKernel_of_perfect_of_index [Finite H] {A : Type*} [Group A]
    [Group.IsPerfect A] {J : Subgroup H} [Group.IsSolvable (OuterAutomorphisms.Outer (OddBar J))]
    (f : A →* ↥(normalizer (J : Set H)))
    (hA : ∀ N : Subgroup A, N.Normal → N.index ≤ Nat.card (OddBar J) → N = ⊤) (x : A) :
    (f x : H) ∈ coreActionKernel J := by
  set ρ := (oddBarConj J).comp f with hρ
  have hinn : ρ.range ≤ (MulAut.conj : OddBar J →* MulAut (OddBar J)).range := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨j, hj⟩ := OuterAutomorphisms.perfect_action_inner ρ y
    exact ⟨j, hj.symm⟩
  have hcard : Nat.card ρ.range ≤ Nat.card (OddBar J) :=
    (Subgroup.card_le_of_le hinn).trans (Nat.card_le_card_of_surjective _
      (MulAut.conj : OddBar J →* MulAut (OddBar J)).rangeRestrict_surjective)
  have hker : ρ.ker = ⊤ := hA ρ.ker inferInstance (by rw [Subgroup.index_ker]; exact hcard)
  have h1 : ρ x = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact mem_top x
  exact mem_coreActionKernel_of_oddBarConj_eq_one h1

end CFSG.ComponentClassification.GSThmB
