module

public import CFSG.ClassicalInvolution.Asc77.AscBSCPair
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinCtx
public import CFSG.ClassicalInvolution.Asc77.AscIH8Graph
import CFSG.ClassicalInvolution.Uniform.U3Edge
public import CFSG.ClassicalInvolution.Asc77.WP2Interface

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

set_option linter.unusedSectionVars false

section Tags

variable {p : ℕ} [Fact p.Prime]

theorem tag_cases_of_small {t : LTag} {n e : ℕ} (hadm : StatedLieAdmissible t n p e)
    (hsmall : SmallModel t n) (hnA1 : ¬ (t = .PSL ∧ n = 2)) :
    ((t = .PSL ∨ t = .PSU) ∧ n = 3) ∨ ListedTwin t n := by
  rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hk2 : 2 ≤ n := hadm.2.2.1
    have : n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases this with rfl | rfl | rfl
    · exact (hnA1 ⟨rfl, rfl⟩).elim
    · exact Or.inl ⟨Or.inl rfl, rfl⟩
    · exact Or.inr (by simp [ListedTwin])
  · have hk3 : 3 ≤ n := hadm.2.2.1
    have : n = 3 ∨ n = 4 := by omega
    rcases this with rfl | rfl
    · exact Or.inl ⟨Or.inr rfl, rfl⟩
    · exact Or.inr (by simp [ListedTwin])
  · exact Or.inr (by simp [ListedTwin])
  · exact Or.inr (by simp [ListedTwin])
  · exact Or.inr (by simp [ListedTwin])
  · exact Or.inr (by simp [ListedTwin])

end Tags

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}


section Components

variable (C : XCtx p f Ω z)

theorem tag_cases_of_noFrame (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    (j : Fin C.D.card) (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2)) :
    (C.D.tag j = .G2 ∨ C.D.tag j = .trialityD4) ∨
      (((C.D.tag j = .PSL ∨ C.D.tag j = .PSU) ∧ C.D.rank j = 3) ∨
        ListedTwin (C.D.tag j) (C.D.rank j)) := by
  by_cases hG2 : C.D.tag j = .G2
  · exact Or.inl (Or.inl hG2)
  by_cases hD4 : C.D.tag j = .trialityD4
  · exact Or.inl (Or.inr hD4)
  refine Or.inr ?_
  rcases Uniform.tag_casesU C.hp (C.D.isFundTag j) (C.D.admissible j) hG2 hD4 with hconn | hsmall
  · exfalso
    obtain ⟨A, hA⟩ := exists_fuzzyFrame_of_pair C j hj hG2 hD4 hconn
    exact hno A hA
  · exact tag_cases_of_small (C.D.admissible j) hsmall hj

theorem eq_of_not_A1 (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    {j₁ j₂ : Fin C.D.card} (h₁ : ¬ (C.D.tag j₁ = .PSL ∧ C.D.rank j₁ = 2))
    (h₂ : ¬ (C.D.tag j₂ = .PSL ∧ C.D.rank j₂ = 2)) : j₁ = j₂ := by
  by_contra hne
  obtain ⟨m₁⟩ := exists_compMem C j₁
  obtain ⟨m₂⟩ := exists_compMem C j₂
  have h1z : m₁.nbar ≠ zbar z := fun h => zbar_not_mem C j₁ h₁ m₁.hR (h ▸ m₁.nbar_mem)
  obtain ⟨A, hA⟩ := exists_fuzzyFrame_of_components C hne h₂ m₁ m₂ h1z
  exact hno A hA

theorem nbar_eq_of_A1 (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    {b : Fin C.D.card} (hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2)) {j : Fin C.D.card}
    (hne : j ≠ b) :
    (C.D.tag j = .PSL ∧ C.D.rank j = 2) ∧ ∀ m : CompMem C j, m.nbar = zbar z := by
  have hj : C.D.tag j = .PSL ∧ C.D.rank j = 2 := by
    by_contra hj
    exact hne (eq_of_not_A1 C hno hj hb)
  refine ⟨hj, fun m => ?_⟩
  by_contra h
  obtain ⟨mb⟩ := exists_compMem C b
  obtain ⟨A, hA⟩ := exists_fuzzyFrame_of_components C hne hb m mb h
  exact hno A hA

theorem twin_ne_K {j₀ e : Fin C.D.card} (hj₀ : C.D.tag j₀ = .PSL ∧ C.D.rank j₀ = 2)
    (hK₀ : modOdd z (exactCore z C.K) = (C.psi j₀).range) (hee : e ≠ j₀)
    (he : C.D.tag e = .PSL ∧ C.D.rank e = 2) (m : CompMem C e) (hm : m.nbar = zbar z) :
    m.N ≠ C.K := by
  intro h
  have hmod : modOdd z m.N = (C.psi e).range := (classical_of_nbar_eq C he m hm).2
  have hKr : modOdd z C.K = (C.psi j₀).range := by
    rw [← hK₀, C.exactCore_K]
  rw [h, hKr] at hmod
  have hzK : zbar z ∈ (C.psi j₀).range := by
    rw [← hKr]
    exact oddQuotMk_mem_modOdd C.K_cl.mem (XCtx.hzC z)
  refine C.range_not_comm_of_A1 j₀ hj₀ hzK ?_
  intro a ha b hb
  rw [hmod] at hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact C.psi_commute (Ne.symm hee) a' b'

theorem localShape (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A) :
    (∀ i : Fin C.D.card, C.D.tag i = .PSL ∧ C.D.rank i = 2) ∨
      ∃ b : Fin C.D.card, ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) ∧
        ((C.D.tag b = .G2 ∨ C.D.tag b = .trialityD4) ∨
          (((C.D.tag b = .PSL ∨ C.D.tag b = .PSU) ∧ C.D.rank b = 3) ∨
            ListedTwin (C.D.tag b) (C.D.rank b))) ∧
        ∀ j : Fin C.D.card, j ≠ b → (C.D.tag j = .PSL ∧ C.D.rank j = 2) ∧
          ∀ m : CompMem C j, m.nbar = zbar z := by
  by_cases hall : ∀ i : Fin C.D.card, C.D.tag i = .PSL ∧ C.D.rank i = 2
  · exact Or.inl hall
  · right
    obtain ⟨b, hb⟩ : ∃ b : Fin C.D.card, ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) := by
      by_contra h
      exact hall fun i => by_contra fun hi => h ⟨i, hi⟩
    exact ⟨b, hb, tag_cases_of_noFrame C hno b hb, fun j hj => nbar_eq_of_A1 C hno hb hj⟩

end Components

end CFSG.ClassicalInvolution.Asc77.BSC
