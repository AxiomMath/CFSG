module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G]

theorem card_modEq_card_normalized {Pts : Set (Subgroup G)} [Finite Pts] {j : G} {n : ℕ}
    (hj : j ^ 3 ^ n = 1) (hPts : ∀ Q ∈ Pts, rightConjugate Q j ∈ Pts) :
    Nat.card Pts ≡ Nat.card {Q : Pts // j ∈ normalizer ((Q : Subgroup G) : Set G)} [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite Pts
  let f : Function.End Pts := fun Q => ⟨rightConjugate Q.1 j, hPts _ Q.2⟩
  have hfm : ∀ m : ℕ, ∀ Q : Pts, ((f ^ m) Q).1 = rightConjugate Q.1 (j ^ m) := by
    intro m
    induction m with
    | zero => intro Q; rw [pow_zero, pow_zero, rightConjugate_one]; rfl
    | succ m ih =>
      intro Q
      rw [pow_succ', pow_succ]
      change rightConjugate ((f ^ m) Q).1 j = _
      rw [ih, rightConjugate_mul]
  have hf : f ^ 3 ^ n = 1 := by
    funext Q
    apply Subtype.ext
    rw [hfm, hj, rightConjugate_one]
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  have he : Nat.card (Function.fixedPoints f) =
      Nat.card {Q : Pts // j ∈ normalizer ((Q : Subgroup G) : Set G)} :=
    Nat.card_congr
      { toFun := fun Q => ⟨Q.1, (rightConjugate_eq_self_iff _ _).mp (congrArg Subtype.val Q.2)⟩
        invFun := fun Q => ⟨Q.1, Subtype.ext ((rightConjugate_eq_self_iff _ _).mpr Q.2)⟩
        left_inv := fun Q => rfl
        right_inv := fun Q => rfl }
  rw [he] at h
  exact h

theorem even_card_of_parity {Pts : Set (Subgroup G)} [Finite Pts] (j : Subgroup G → G)
    (ζ : Subgroup G → Subgroup G) (hj3 : ∀ P ∈ Pts, ∃ n : ℕ, j P ^ 3 ^ n = 1)
    (hPts : ∀ P ∈ Pts, ∀ Q ∈ Pts, rightConjugate Q (j P) ∈ Pts)
    (hjζ : ∀ P ∈ Pts, j P ∈ normalizer (ζ P : Set G)) (hne : ∀ P ∈ Pts, ζ P ≠ P)
    (hfix : ∀ P ∈ Pts, ∀ Q ∈ Pts, j P ∈ normalizer (Q : Set G) → Q = P ∨ Q = ζ P)
    (hcomp : ∀ P ∈ Pts, ∀ Q ∈ Pts, j P ∈ normalizer (Q : Set G) → j P ∈ normalizer (ζ Q : Set G))
    (h2 : Nat.card Pts % 3 = 2) : Even (Nat.card Pts) := by
  classical
  have hmem : ∀ P ∈ Pts, ζ P ∈ Pts := by
    intro P hP
    by_contra hζ
    obtain ⟨n, hn⟩ := hj3 P hP
    have hmod := card_modEq_card_normalized hn (hPts P hP)
    have hsub : Subsingleton {Q : Pts // j P ∈ normalizer ((Q : Subgroup G) : Set G)} := by
      refine ⟨fun Q₁ Q₂ => ?_⟩
      have key : ∀ Q : {Q : Pts // j P ∈ normalizer ((Q : Subgroup G) : Set G)},
          (Q : Pts).1 = P := by
        intro Q
        rcases hfix P hP Q.1.1 Q.1.2 Q.2 with h | h
        · exact h
        · exact absurd (h ▸ Q.1.2) hζ
      exact Subtype.ext (Subtype.ext ((key Q₁).trans (key Q₂).symm))
    have hle := Finite.card_le_one_iff_subsingleton.mpr hsub
    have hmod' := hmod
    unfold Nat.ModEq at hmod'
    rw [h2, Nat.mod_eq_of_lt (by omega)] at hmod'
    omega
  have hinv : ∀ P ∈ Pts, ζ (ζ P) = P := by
    intro P hP
    have hQ := hmem P hP
    have h1 := hcomp P hP (ζ P) hQ (hjζ P hP)
    rcases hfix P hP (ζ (ζ P)) (hmem _ hQ) h1 with h | h
    · exact h
    · exact absurd h (hne _ hQ)
  have := Fintype.ofFinite Pts
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ : Function.End Pts := fun Q => ⟨ζ Q.1, hmem _ Q.2⟩
  have hσ : σ ^ 2 ^ 1 = 1 := by
    funext Q
    apply Subtype.ext
    change ζ (ζ Q.1) = Q.1
    exact hinv _ Q.2
  have h := Equiv.Perm.card_fixedPoints_modEq hσ
  have hempty : Fintype.card (Function.fixedPoints σ) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun Q => hne _ Q.1.2 ?_⟩
    exact congrArg Subtype.val Q.2
  rw [hempty, ← Nat.card_eq_fintype_card] at h
  exact Nat.even_iff.mpr h
