module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicEndgame

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Ru

open Subgroup CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.ComponentClassification.RankTwoSporadic.Endgame

@[expose] noncomputable def ruEndE (i : ℕ) : Equiv.Perm (Fin 4060) := permOfArr 4060 ruE0[i]!

@[expose] noncomputable def ruLStrong (i : ℕ) : Equiv.Perm (Fin 4060) :=
  permOfArr 4060 (ruField4060 5)[i]!

@[expose] def ruEndSig (i a : ℕ) : ℕ :=
  (([[0, 4, 3, 2, 1], [0, 3, 4, 1, 2], [0, 2, 1, 4, 3]] : List (List ℕ)).getD i []).getD a 0

@[expose] def ruInPA (a : Array ℕ) : Prop := isInvA 4060 a (ruInv a) = true ∧ ruInP a = true

structure RuEndFactsK : Prop where
  e_mem : ∀ i < 2, ruInPA ruE0[i]!
  e_sq : ∀ i < 2, ruEndE i * ruEndE i = 1
  e_comm : ruEndE 0 * ruEndE 1 = ruEndE 1 * ruEndE 0
  e_fpf : ∀ p, ruEndE 0 p ≠ p ∧ ruEndE 1 p ≠ p ∧ (ruEndE 0 * ruEndE 1) p ≠ p
  conj : ∃ b : Array ℕ, ∃ x : Fin 8 → Array ℕ, ruInPA b ∧ (∀ i, ruInPA (x i)) ∧
    (∀ i < 2, ∀ j < 2, ruEndE i * ((permOfArr 4060 b)⁻¹ * ruEndE j * permOfArr 4060 b) =
      (permOfArr 4060 b)⁻¹ * ruEndE j * permOfArr 4060 b * ruEndE i) ∧
    (permOfArr 4060 b)⁻¹ * ruEndE 0 * permOfArr 4060 b ∉
      ({1, ruEndE 0, ruEndE 1, ruEndE 0 * ruEndE 1} : Set (Equiv.Perm (Fin 4060))) ∧
    (∀ i, ∀ j < 2, permOfArr 4060 (x i) * ruEndE j = ruEndE j * permOfArr 4060 (x i)) ∧
    tree3 (fun i => permOfArr 4060 (x i)) =
      ruEndE 0 * ((permOfArr 4060 b)⁻¹ * ruEndE 0 * permOfArr 4060 b)
  sylow : ∃ lab : Fin 4060 → ℕ, (∀ p, lab p < 5) ∧
    (∀ i < 3, ∀ p, lab (ruLStrong i p) = ruEndSig i (lab p)) ∧
    ∃ s : Array (Array ℕ), (∀ k < s.size, ruInPA s[k]! ∧
      permOfArr 4060 s[k]! * ruEndE 0 = ruEndE 0 * permOfArr 4060 s[k]!) ∧
      Nat.card (closure (permsA 4060 s)) = 256 ∧
      ∀ z ∈ closure (permsA 4060 s), z ^ 2 = 1 → (∀ p, lab (z p) = lab p) → ∃ p, z p = p

end CFSG.ComponentClassification.RankTwoSporadic.Ru

end
