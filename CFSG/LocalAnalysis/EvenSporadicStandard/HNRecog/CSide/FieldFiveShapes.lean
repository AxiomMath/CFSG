module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.SetupData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.CaseShapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.CaseCent

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.CSide
open scoped commutatorElement

theorem cSideFacts_five_local_shapes :
    ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → CIrreducible C Q →
      (∀ ρ : C, orderOf ρ = 5 →
        (IsShapeZpTimesA5 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q))) ∧
            Q ⊓ Subgroup.centralizer ({ρ} : Set C) = centerOf Q) ∨
        IsShapeZpTimesZp 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q))) ∨
        IsShapeZpWrTwo 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q)))) ∧
      (∃ ρ : C, orderOf ρ = 5 ∧
        IsShapeZpTimesA5 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q)))) ∧
      (∃ ρ : C, orderOf ρ = 5 ∧
        IsShapeZpTimesZp 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q)))) ∧
      (∃ ρ : C, orderOf ρ = 5 ∧
        IsShapeZpWrTwo 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q)))) := by
  intro C _ Q _ hE hI
  haveI : Finite Q := hE.plus.finite
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hE.plus.isExtraspecialPGroup
  have hC : CFSG.EvenSporadicStandard.HNRecog.CSide.WeakHyp C Q :=
    CFSG.EvenSporadicStandard.HNRecog.CSide.WeakHyp.of_cIrreducible hE hI
  haveI : Finite C := hC.finite
  obtain ⟨S⟩ := hC.nonempty_setup
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨hρL, hg⟩ := S.odd_data hC (Or.inr rfl) hρ
    by_cases h1 : (S.θ ⟨ρ, hρL⟩).1 = 1 ∨ (S.θ ⟨ρ, hρL⟩).2 = 1
    · exact Or.inl ⟨S.shape_one_coord (Or.inr rfl) hρL hg h1,
        S.cent_eq_of_one_coord hC (Or.inr rfl) hρL hρ hg h1⟩
    · push Not at h1
      by_cases hc : IsConj (S.θ ⟨ρ, hρL⟩).1 (S.θ ⟨ρ, hρL⟩).2
      · exact Or.inr (Or.inr (S.shape_conj (Or.inr rfl) hρL hg hc))
      · exact Or.inr (Or.inl (S.shape_nonconj hρL hg h1.1 h1.2 hc))
  · obtain ⟨x, hx⟩ := cSide_exists_orderOf (p := 5) (Or.inr rfl)
    have hg5 : orderOf (x, (1 : alternatingGroup (Fin 5))) = 5 := by
      rw [Prod.orderOf_mk, hx, orderOf_one]; decide
    obtain ⟨ρ, hρL, hρ, hθ⟩ := S.exists_odd_lift hC (Or.inr rfl) hg5
    refine ⟨ρ, hρ, ?_⟩
    have hg' : orderOf (S.θ ⟨ρ, hρL⟩) = 5 := by rw [hθ]; exact hg5
    exact S.shape_one_coord (Or.inr rfl) hρL hg' (Or.inr (by simp [hθ]))
  · obtain ⟨x, y, hx, hy, hxy⟩ := cSide_exists_nonconj_five
    have hg5 : orderOf (x, y) = 5 := by
      rw [Prod.orderOf_mk, hx, hy]; decide
    obtain ⟨ρ, hρL, hρ, hθ⟩ := S.exists_odd_lift hC (Or.inr rfl) hg5
    refine ⟨ρ, hρ, ?_⟩
    have hg' : orderOf (S.θ ⟨ρ, hρL⟩) = 5 := by rw [hθ]; exact hg5
    have hxne : x ≠ 1 := ((orderOf_eq_prime_iff (x := x) (p := 5)).mp hx).2
    have hyne : y ≠ 1 := ((orderOf_eq_prime_iff (x := y) (p := 5)).mp hy).2
    refine S.shape_nonconj hρL hg' ?_ ?_ ?_
    · rw [hθ]; exact hxne
    · rw [hθ]; exact hyne
    · rw [hθ]; exact hxy
  · obtain ⟨x, hx⟩ := cSide_exists_orderOf (p := 5) (Or.inr rfl)
    have hg5 : orderOf (x, x) = 5 := by
      rw [Prod.orderOf_mk, hx]; decide
    obtain ⟨ρ, hρL, hρ, hθ⟩ := S.exists_odd_lift hC (Or.inr rfl) hg5
    refine ⟨ρ, hρ, ?_⟩
    have hg' : orderOf (S.θ ⟨ρ, hρL⟩) = 5 := by rw [hθ]; exact hg5
    refine S.shape_conj (Or.inr rfl) hρL hg' ?_
    simpa [hθ] using IsConj.refl x

end CFSG.EvenSporadicStandard.HNRecog.Section3
