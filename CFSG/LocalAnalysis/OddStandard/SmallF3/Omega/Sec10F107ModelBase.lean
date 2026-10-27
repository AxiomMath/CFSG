
module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107Over
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TypesCert

@[expose] public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

namespace Mo107

open Certificates.OmegaS107

theorem stepL_mem {H : Subgroup P45} {«gens» : List P45} (hg : ∀ g ∈ «gens», g ∈ H) {S : List P45}
    (hS : ∀ s ∈ S, s ∈ H) : ∀ x ∈ Certificates.OmegaF1051.stepL «gens» S, x ∈ H := by
  have inner : ∀ s ∈ H, ∀ (gl : List P45), (∀ g ∈ gl, g ∈ H) → ∀ acc : List P45,
      (∀ x ∈ acc, x ∈ H) → ∀ x ∈ gl.foldl (fun acc' g =>
        if s * g ∈ acc' then acc' else acc' ++ [s * g]) acc, x ∈ H := by
    intro s hs gl
    induction gl with
    | nil => exact fun _ acc hacc => hacc
    | cons g gl ih =>
      intro hgl acc hacc
      refine ih (fun g' hg' => hgl g' (List.mem_cons_of_mem _ hg')) _ ?_
      intro x hx
      simp only at hx
      split_ifs at hx with h
      · exact hacc x hx
      · rcases List.mem_append.1 hx with hx | hx
        · exact hacc x hx
        · rw [List.mem_singleton.1 hx]
          exact H.mul_mem hs (hgl g List.mem_cons_self)
  have outer : ∀ (l : List P45), (∀ s ∈ l, s ∈ H) → ∀ acc : List P45, (∀ x ∈ acc, x ∈ H) →
      ∀ x ∈ l.foldl (fun acc s => «gens».foldl (fun acc' g =>
        if s * g ∈ acc' then acc' else acc' ++ [s * g]) acc) acc, x ∈ H := by
    intro l
    induction l with
    | nil => exact fun _ acc hacc => hacc
    | cons s l ih =>
      intro hl acc hacc
      exact ih (fun s' hs' => hl s' (List.mem_cons_of_mem _ hs')) _
        (inner s (hl s List.mem_cons_self) «gens» hg acc hacc)
  exact outer S hS S hS

theorem closeL_mem {H : Subgroup P45} {«gens» : List P45} (hg : ∀ g ∈ «gens», g ∈ H) :
    ∀ (n : ℕ) (S : List P45), (∀ s ∈ S, s ∈ H) →
      ∀ x ∈ Certificates.OmegaF1051.closeL «gens» n S, x ∈ H
  | 0, _, hS => hS
  | n + 1, S, hS => closeL_mem hg n _ (stepL_mem hg hS)

structure Model107 (T B2 : Subgroup P45) (y2 : P45) : Prop where
  le : B2 ≤ T
  comm : ∀ a ∈ B2, ∀ b ∈ B2, a * b = b * a
  sq : ∀ a ∈ B2, a * a = 1
  card : Nat.card B2 = 16
  normal : ∀ g ∈ T, ∀ b ∈ B2, g * b * g⁻¹ ∈ B2
  normB0 : ∀ g ∈ T, ∀ b ∈ B0, g * b * g⁻¹ ∈ B0
  y2_mem : y2 ∈ B2
  y2_out : y2 ∉ QT0.originalSubgroup
  y2_inv : InvCent 1440 y2
  mem_B2 : ∀ b : P45, b ∈ B2 ↔
    (b ∈ Q32 ∧ b * y2 = y2 * b) ∨ ∃ c ∈ Q32, c * y2 = y2 * c ∧ c * y2 = b
  normal_elem : ∀ X : Subgroup P45, X ≤ T → (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) →
    (∀ a ∈ X, a * a = 1) → Nat.card X = 16 → (∀ g ∈ T, ∀ x ∈ X, g * x * g⁻¹ ∈ X) →
      X = B0 ∨ X = B2
  meet : ∀ X : Subgroup P45, X ≤ T → (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) →
    (∀ a ∈ X, a * a = 1) → Nat.card X = 16 → ¬ X ≤ QT0.originalSubgroup →
      ∃ y ∈ X, y ∈ B2 ∧ y ∉ QT0.originalSubgroup

end Mo107

end CFSG.OddStandard.SmallF3.Omega
