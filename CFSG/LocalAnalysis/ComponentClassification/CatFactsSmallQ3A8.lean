module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallNoNilpCheck
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8Model
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallNoNilpCheck
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Inputs
public import Certificates.Certificate2013
public import Certificates.Certificate2007

public section

namespace CFSG.ComponentClassification.CatFactsSmall.A8

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup

local notation "P8" => Equiv.Perm (Fin 8)

theorem P_le_A : QA8.originalSubgroup ≤ QS8.originalSubgroup := by
  rw [QS8_eq]
  exact le_top

theorem cent_ok : centTrivCheck (elemsT QS8) a8 b8 = true :=
  Certificates.certificate2013.1

theorem a8_mem : a8 ∈ QA8.originalSubgroup := by
  rw [QA8, certificate_originalSubgroup]
  exact subset_closure (by simp [tab_eq])

theorem b8_mem : b8 ∈ QA8.originalSubgroup := by
  rw [QA8, certificate_originalSubgroup]
  exact subset_closure (by simp [tab_eq])

theorem cent_triv : ∀ g ∈ QS8.originalSubgroup,
    (∀ x ∈ QA8.originalSubgroup, g * x = x * g) → g = 1 := by
  intro g hg hc
  by_contra hne
  have h1 := List.all_eq_true.1 cent_ok g ((mem_elemsT QS8 QS8_ok g).2 hg)
  simp [hc a8 a8_mem, hc b8 b8_mem, hne] at h1

theorem card_A_eq : Nat.card QS8.originalSubgroup = 2 * Nat.card QA8.originalSubgroup := by
  rw [card_QS8, card_QA8]

theorem noNilp_ok : noNilpCheck (elemsT QS8) ((elemsT QA8).filter oddTest) 315 = true :=
  Certificates.certificate2013.2

theorem pow_of_oddTest {x : P8} (h : oddTest x = true) : x ^ 315 = 1 := by
  simp only [oddTest, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · rw [show 315 = 15 * 21 by norm_num, pow_mul, h, one_pow]
  · rw [show 315 = 7 * 45 by norm_num, pow_mul, h, one_pow]

theorem noNilp_fact {s : P8} (hs : s ∈ QS8.originalSubgroup) (hs2 : s * s = 1) :
    ∃ x₁ ∈ QA8.originalSubgroup, ∃ x₂ ∈ QA8.originalSubgroup, x₁ * s = s * x₁ ∧
      x₂ * s = s * x₂ ∧ x₁ ^ 315 = 1 ∧ x₂ ^ 315 = 1 ∧ (x₁ * x₂) ^ 315 ≠ 1 := by
  obtain ⟨x₁, hx₁, x₂, hx₂, hc₁, hc₂, h12⟩ :=
    noNilpCheck_sound noNilp_ok ((mem_elemsT QS8 QS8_ok s).2 hs) hs2
  rw [List.mem_filter] at hx₁ hx₂
  exact ⟨x₁, (mem_elemsT QA8 QA8_ok x₁).1 hx₁.1, x₂, (mem_elemsT QA8 QA8_ok x₂).1 hx₂.1, hc₁,
    hc₂, pow_of_oddTest hx₁.2, pow_of_oddTest hx₂.2, h12⟩

end CFSG.ComponentClassification.CatFactsSmall.A8
