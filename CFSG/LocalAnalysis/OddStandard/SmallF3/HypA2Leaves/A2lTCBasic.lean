module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.FStarFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lInChev2

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint

@[expose] def TCSmall (Q : Type) [Group Q] : Prop :=
  LieModel Q .PSL 2 3 2 ∨ LieModel Q .PSU 3 3 1 ∨ LieModel Q .PSp 2 3 1

theorem TCSmall.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : TCSmall A) :
    TCSmall B := by
  unfold TCSmall at h ⊢
  rcases h with h | h | h
  · exact Or.inl (LieModel.of_mulEquiv e h)
  · exact Or.inr (Or.inl (LieModel.of_mulEquiv e h))
  · exact Or.inr (Or.inr (LieModel.of_mulEquiv e h))

theorem a2l_card_tcSmall {Q : Type} [Group Q] (h : TCSmall Q) :
    Nat.card Q = 360 ∨ Nat.card Q = 6048 ∨ Nat.card Q = 25920 := by
  rcases h with h | h | h
  · left
    rw [GH74.card_of_lieModel_PSL (G := Q) (n := 2) (p := 3) (f := 2) (by norm_num) h]
    decide
  · right; left
    rw [GH74.card_of_lieModel_PSU (G := Q) (n := 3) (p := 3) (f := 1) (by norm_num)
      (by norm_num) h]
    decide
  · right; right
    rw [GH74.card_of_lieModel_PSp (G := Q) (n := 2) (p := 3) (f := 1) (by norm_num)
      (by norm_num) h]
    decide

private theorem false_of_card {S : Type} [Group S]
    (hC : Nat.card S ∈ ({60, 168, 6048} : Finset ℕ) ∨ LieModel S .PSL 2 3 2 ∨
      LieModel S .PSp 2 3 1) {c : ℕ} (hc : Nat.card S = c)
    (hne : c ∉ ({60, 168, 6048, 360, 25920} : Finset ℕ)) : False := by
  rcases hC with h | h | h
  · exact hne (by rw [← hc]; simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; omega)
  · have h1 := GH74.card_of_lieModel_PSL (G := S) (n := 2) (p := 3) (f := 2) (by norm_num) h
    have h2 : Nat.card S = 360 := by rw [h1]; decide
    exact hne (by rw [← hc, h2]; decide)
  · have h1 := GH74.card_of_lieModel_PSp (G := S) (n := 2) (p := 3) (f := 1) (by norm_num)
      (by norm_num) h
    have h2 : Nat.card S = 25920 := by rw [h1]; decide
    exact hne (by rw [← hc, h2]; decide)

section


theorem a2l_tcSmall_of_fStarSimple {S : Type} [Group S] [Finite S] (hF : HypA2.FStarSimple S)
    (hI : GH74.GLS.InChev2 S) : TCSmall S := by
  have hC := chevOddInChev2_holds S 3 Nat.prime_three (by norm_num)
    (HypA2.isSimpleChevalleyOver_three_of_fStarSimple hF) hI
  unfold HypA2.FStarSimple at hF
  rcases hF with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · exact (false_of_card hC (c := Open.ordA (2 - 1) (3 ^ 4))
      (GH74.card_of_lieModel_PSL (G := S) (n := 2) (p := 3) (f := 4) (by norm_num) h2)
      (by decide)).elim
  · exact (false_of_card hC (c := Open.ordA (3 - 1) (3 ^ 1))
      (GH74.card_of_lieModel_PSL (G := S) (n := 3) (p := 3) (f := 1) (by norm_num) h3)
      (by decide)).elim
  · exact Or.inr (Or.inl h4)
  · unfold SmallF3OmegaQuotient at h5
    rcases h5 with h | h | h | h | h | h
    · exact Or.inr (Or.inr h)
    · exact (false_of_card hC (c := Open.ordA (4 - 1) (3 ^ 1))
        (GH74.card_of_lieModel_PSL (G := S) (n := 4) (p := 3) (f := 1) (by norm_num) h)
        (by decide)).elim
    · exact (false_of_card hC (c := Open.ordTwistedA (4 - 1) (3 ^ 1))
        (GH74.card_of_lieModel_PSU (G := S) (n := 4) (p := 3) (f := 1) (by norm_num)
          (by norm_num) h) (by decide)).elim
    · exact (false_of_card hC (c := Open.ordBC 3 (3 ^ 1))
        ((CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := S)
          (t := .POmegaOdd) (n := 3) (p := 3) (f := 1) (by norm_num)
          (GH74.statedClassicalModel_of_lieModel (G := S) (t := .POmegaOdd) (n := 3) (p := 3)
            (f := 1) (by norm_num) h)).2.2.2.1 rfl) (by decide)).elim
    · exact (false_of_card hC (c := Open.ordD 4 (3 ^ 1))
        ((CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := S)
          (t := .POmegaPlus) (n := 4) (p := 3) (f := 1) (by norm_num)
          (GH74.statedClassicalModel_of_lieModel (G := S) (t := .POmegaPlus) (n := 4) (p := 3)
            (f := 1) (by norm_num) h)).2.2.2.2.1 rfl) (by decide)).elim
    · exact (false_of_card hC (c := Open.ordTwistedD 4 (3 ^ 1))
        ((CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := S)
          (t := .POmegaMinus) (n := 4) (p := 3) (f := 1) (by norm_num)
          (GH74.statedClassicalModel_of_lieModel (G := S) (t := .POmegaMinus) (n := 4) (p := 3)
            (f := 1) (by norm_num) h)).2.2.2.2.2 rfl) (by decide)).elim

theorem a2l_tcSmall_of_isFStar {X : Type} [Group X] [Finite X] (hX : HypA2.IsFStar X)
    (hI : GH74.GLS.InChev2 (X ⧸ Open.fusionZStar X)) : TCSmall (X ⧸ Open.fusionZStar X) :=
  a2l_tcSmall_of_fStarSimple (HypA2.fStarSimple_of_isFStar hX) hI

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
