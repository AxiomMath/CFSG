module

public import CFSG.ClassicalInvolution.Q3.Q3T6CoreSec

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups

section Tag


variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)}

theorem tag_cases_of_sysData (D : LieSystemDataU 3 1 (Fin 1) Y Φ) (hconj : ConjInvariant Φ)
    (hno : ∀ A ∈ Φ, ∀ B ∈ Φ, ¬ Commutes A B) (hΦne : Φ.Nonempty)
    (hTop : (⊤ : Subgroup Y) ∉ Φ) :
    (∃ (t : StatedLieTag) (k : ℕ), ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3) ∨
        (t = .G2 ∧ k = 0) ∨ (t = .trialityD4 ∧ k = 0)) ∧ CompIs 3 1 (D.kind 0) t k) ∨
      D.kind 0 = Q3.CompData.m11 := by
  rcases D.valid 0 with ⟨t, k, e, hft, hadm, he, hc⟩ | ⟨-, hc | hc⟩
  · left
    have he1 : e = 1 := by
      rcases he with he | ⟨-, he⟩ <;> omega
    subst he1
    let M : Ih8Model 3 1 Φ t k 1 := Q3T6.ih8ModelOfSystemU D 0 hconj hft hadm (Or.inl rfl) hc
    refine ⟨t, k, ?_, ⟨1, Or.inl rfl, hft, hadm, hc⟩⟩
    by_cases hG2 : t = .G2
    · subst hG2
      obtain ⟨hk, -⟩ := hadm.2.2
      subst hk
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    by_cases hD4 : t = .trialityD4
    · subst hD4
      have hk : k = 0 := hadm.2.2
      subst hk
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    by_cases hL3 : t = .PSL ∧ k = 3
    · exact Or.inl hL3
    by_cases hU3 : t = .PSU ∧ k = 3
    · exact Or.inr (Or.inl hU3)
    exfalso
    have hA1 : ¬ (t = .PSL ∧ k = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hadm.2.2.2.2 (by simp)
    have h3' : ¬ ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) := by
      rintro (h | h)
      · exact hL3 h
      · exact hU3 h
    obtain ⟨R₀, hR₀⟩ := M.cls_nonempty hΦne
    obtain ⟨R, hR, S, hS, hRS⟩ :=
      exists_commuting_fund (by norm_num : (3 : ℕ) ≠ 2) hft hadm hG2 hD4 hA1 h3' (M.cls_sub hR₀)
    have hK := M.map_mem (M.fund_subset_cls hΦne hG2 hD4 hR)
    have hJ := M.map_mem (M.fund_subset_cls hΦne hG2 hD4 hS)
    exact hno _ hK _ hJ (ih8_commutes_map M.ψ hRS)
  · exfalso
    exact hTop (Q3T6.top_mem_of_sl23 D 0 hc)
  · exact Or.inr hc


variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Φ' : Set (Subgroup G)}

@[expose] noncomputable def omegaLieU_of_sysData (D : LieSystemDataU p f (Fin 1) G Φ')
    (hgen : omegaGen Φ' = ⊤) : OmegaLieU p f Φ' where
  card := 1
  kind := D.kind
  valid := D.valid
  hom := D.hom
  ker_le_center := D.ker_le_center
  commute := fun i j hij x y => absurd (Subsingleton.elim i j) hij
  generate := by rw [hgen]; exact D.generate
  fundamental := D.fundamental
  meets := D.meets
  card_eq := D.card_eq


end Tag

end CFSG.ClassicalInvolution.Q3.Q3T8
