module

public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal

@[expose] def RegularThreeSingular {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : Prop :=
  (polarBilin Q).Nondegenerate ∧
    ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0

@[expose] def WitnessFormsRegular (G : Type) [Group G] (t : StatedLieTag) (n p f : ℕ) : Prop :=
  match t with
  | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ Q : QuadraticForm K (Fin n ⊕ Fin n ⊕ Unit → K), ⇑Q = StatedQuadOdd n K →
      ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)), RegularThreeSingular Q
  | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ Q : QuadraticForm K (Fin n ⊕ Fin n → K), ⇑Q = StatedQuadPlus n K →
      ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)), RegularThreeSingular Q
  | .POmegaMinus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ Q : QuadraticForm K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
        ⇑Q = StatedQuadMinus n K b c →
      ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)), RegularThreeSingular Q
  | _ => True

theorem orthogonal_standard_forms_regular (G : Type) [Group G] (t : StatedLieTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n p f : ℕ)
    (hadm : StatedLieAdmissible t n p f) : WitnessFormsRegular G t n p f := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨hp, hf, hn, hp2⟩ := hadm
    intro K _ _ hK Q hQ _
    have hchar := ringChar_eq_of_card_eq hp hf hK
    have h2 : (2 : K) ≠ 0 := by
      rw [Ne, two_eq_zero_iff_ringChar_eq_two (hchar ▸ hp), hchar]
      exact hp2
    obtain rfl : Q = quadOdd n K := DFunLike.coe_injective (hQ.trans (coe_quadOdd n K).symm)
    exact regular_quadOdd h2 hn
  · obtain ⟨-, -, hn⟩ := hadm
    intro K _ _ _ Q hQ _
    obtain rfl : Q = quadPlus n K := DFunLike.coe_injective (hQ.trans (coe_quadPlus n K).symm)
    exact regular_quadPlus (by omega)
  · obtain ⟨-, -, hn⟩ := hadm
    intro K _ _ _ b c hirr Q hQ _
    obtain rfl : Q = quadMinus n K b c :=
      DFunLike.coe_injective (hQ.trans (coe_quadMinus n K b c).symm)
    exact regular_quadMinus hn hirr

theorem witnessFormsRegular_of_statedClassicalModel {G : Type} [Group G] {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {n p f : ℕ}
    (h : StatedClassicalModel G t n p f) : WitnessFormsRegular G t n p f :=
  orthogonal_standard_forms_regular G t ht n p f h.1

end CFSG.LocalAnalysis.ComponentInitial
