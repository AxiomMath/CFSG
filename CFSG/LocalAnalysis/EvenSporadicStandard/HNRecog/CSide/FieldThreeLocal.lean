module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.SetupData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.CaseShapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.CaseCent

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.CSide
open scoped commutatorElement

theorem cSideFacts_three_local :
    ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → CIrreducible C Q →
      (∀ σ : C, orderOf σ = 3 →
        (IsShapeZpTimesA5 3 ↥(Subgroup.centralizer ({(σ : C ⧸ Q)} : Set (C ⧸ Q))) ∧
            Q ⊓ Subgroup.centralizer ({σ} : Set C) = centerOf Q) ∨
        (IsShapeZpWrTwo 3 ↥(Subgroup.centralizer ({(σ : C ⧸ Q)} : Set (C ⧸ Q))) ∧
            IsPlusExtraspecial 2 (Q ⊓ Subgroup.centralizer ({σ} : Set C)))) ∧
      (∃ σ : C, orderOf σ = 3 ∧
        IsShapeZpTimesA5 3 ↥(Subgroup.centralizer ({(σ : C ⧸ Q)} : Set (C ⧸ Q)))) ∧
      (∃ σ : C, orderOf σ = 3 ∧
        IsShapeZpWrTwo 3 ↥(Subgroup.centralizer ({(σ : C ⧸ Q)} : Set (C ⧸ Q)))) := by
  intro C _ Q _ hE hI
  have hC : WeakHyp C Q := WeakHyp.of_cIrreducible hE hI
  haveI : Finite C := hC.finite
  haveI : Finite Q := hC.finite_Q
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hC.isExtraspecialPGroup
  obtain ⟨S⟩ := hC.nonempty_setup
  refine ⟨?_, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨hσL, hg⟩ := CSideSetup.odd_data hC S (Or.inl rfl) hσ
    by_cases h1 : (S.θ ⟨σ, hσL⟩).1 = 1 ∨ (S.θ ⟨σ, hσL⟩).2 = 1
    · left
      exact ⟨CSideSetup.shape_one_coord S (Or.inl rfl) hσL hg h1,
        CSideSetup.cent_eq_of_one_coord hC S (Or.inl rfl) hσL hσ hg h1⟩
    · have hne1 : (S.θ ⟨σ, hσL⟩).1 ≠ 1 := fun h => h1 (Or.inl h)
      have hne2 : (S.θ ⟨σ, hσL⟩).2 ≠ 1 := fun h => h1 (Or.inr h)
      have hx : orderOf (S.θ ⟨σ, hσL⟩).1 = 3 := by
        have hdvd : orderOf (S.θ ⟨σ, hσL⟩).1 ∣ 3 := by
          rw [← hg]; exact orderOf_fst_dvd_orderOf
        exact (Nat.prime_three.eq_one_or_self_of_dvd _ hdvd).resolve_left
          (fun h => hne1 (orderOf_eq_one_iff.mp h))
      have hy : orderOf (S.θ ⟨σ, hσL⟩).2 = 3 := by
        have hdvd : orderOf (S.θ ⟨σ, hσL⟩).2 ∣ 3 := by
          rw [← hg]; exact orderOf_snd_dvd_orderOf
        exact (Nat.prime_three.eq_one_or_self_of_dvd _ hdvd).resolve_left
          (fun h => hne2 (orderOf_eq_one_iff.mp h))
      have hc : IsConj (S.θ ⟨σ, hσL⟩).1 (S.θ ⟨σ, hσL⟩).2 :=
        cSide_isConj_of_order_three hx hy
      right
      exact ⟨CSideSetup.shape_conj S (Or.inl rfl) hσL hg hc,
        CSideSetup.cent_plusExtraspecial_of_three hC S hσL hσ hg hne1 hne2⟩
  · obtain ⟨x, hx⟩ := cSide_exists_orderOf (Or.inl rfl)
    have hgx : orderOf (x, (1 : alternatingGroup (Fin 5))) = 3 := by
      rw [Prod.orderOf_mk, hx, orderOf_one]
      norm_num
    obtain ⟨σ, hσL, hσord, htheta⟩ :=
      CSideSetup.exists_odd_lift hC S (Or.inl rfl) (g := (x, 1)) hgx
    refine ⟨σ, hσord, ?_⟩
    have h1 : (S.θ ⟨σ, hσL⟩).1 = 1 ∨ (S.θ ⟨σ, hσL⟩).2 = 1 := by
      rw [htheta]; exact Or.inr rfl
    have hg' : orderOf (S.θ ⟨σ, hσL⟩) = 3 := by rw [htheta]; exact hgx
    exact CSideSetup.shape_one_coord S (Or.inl rfl) hσL hg' h1
  · obtain ⟨x, hx⟩ := cSide_exists_orderOf (Or.inl rfl)
    have hgx : orderOf (x, x) = 3 := by
      rw [Prod.orderOf_mk, hx]
      norm_num
    obtain ⟨σ, hσL, hσord, htheta⟩ :=
      CSideSetup.exists_odd_lift hC S (Or.inl rfl) (g := (x, x)) hgx
    refine ⟨σ, hσord, ?_⟩
    have hc : IsConj (S.θ ⟨σ, hσL⟩).1 (S.θ ⟨σ, hσL⟩).2 := by
      simpa [htheta] using (IsConj.refl x : IsConj x x)
    have hg' : orderOf (S.θ ⟨σ, hσL⟩) = 3 := by rw [htheta]; exact hgx
    exact CSideSetup.shape_conj S (Or.inl rfl) hσL hg' hc

end CFSG.EvenSporadicStandard.HNRecog.Section3
