module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutClasses
public import Certificates.Certificate27204

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.G24Aut

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block
open Subgroup

section Outer


theorem mem_normalizer_of_gens {g : PP} (hx : g * xBar * g⁻¹ ∈ twoBD)
    (hy : g * yBar * g⁻¹ ∈ twoBD) : g ∈ normalizer (twoBD : Set PP) := by
  let φ : PP →* PP := (MulAut.conj g).toMonoidHom
  have hle : twoBD.map φ ≤ twoBD := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hx
    · exact hy
  have hcard : Nat.card (twoBD.map φ) = Nat.card twoBD :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : twoBD.map φ = twoBD := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hle ⟨h, hh, rfl⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨h', hh', hh'e⟩ := hh
    have : h' = h := (MulAut.conj g).injective hh'e
    rwa [← this]

theorem outer_facts :
    (∀ c : PP, (∀ x ∈ twoBD, c * x = x * c) → c = 1) ∧
    ∃ o : PP, Rep nn oa o ∧ o * o = 1 ∧ o ≠ 1 ∧ o ∈ normalizer (twoBD : Set PP) ∧ o ∉ twoBD ∧
      (Nat.card ↥(normalizer (twoBD : Set PP)) = 503193600 →
        ∀ s ∈ normalizer (twoBD : Set PP), s * s = 1 → s ∉ twoBD →
          ∃ d ∈ twoBD, d * s * d⁻¹ = o) := by
  have h := Certificates.certificate27204
  have hX : permOfArr 1365 xa = xBar := strong0_eq
  have hY : permOfArr 1365 ya = yBar := strong1_eq
  rw [hX, hY] at h
  exact h

theorem g24_outer_basic :
    ∃ σ : PP, Rep nn oa σ ∧ (∀ d ∈ twoBD, σ * d * σ⁻¹ ∈ twoBD) ∧ σ ∉ twoBD ∧
      (∀ c : PP, (∀ x ∈ twoBD, c * x = x * c) → c = 1) ∧
      ∃ o : PP, Rep nn oa o ∧ o * o = 1 ∧ o ≠ 1 ∧ o ∈ normalizer (twoBD : Set PP) := by
  obtain ⟨hC, o, ho, hoo, ho1, hoN, hoD, -⟩ := outer_facts
  exact ⟨o, ho, fun d hd => (Subgroup.mem_normalizer_iff.1 hoN d).1 hd, hoD, hC, o, ho, hoo, ho1,
    hoN⟩

theorem g24_outer_fusion
    {tA o : PP} (htA : Rep nn tAa tA) (ho : Rep nn oa o)
    (hN : Nat.card ↥(normalizer (twoBD : Set PP)) = 503193600) :
    ∀ s ∈ normalizer (twoBD : Set PP), s * s = 1 → s ≠ 1 →
      (∃ n ∈ normalizer (twoBD : Set PP), s = n * tA * n⁻¹) ∨
        (∃ n ∈ normalizer (twoBD : Set PP), s = n * xBar * n⁻¹) ∨
          ∃ n ∈ normalizer (twoBD : Set PP), s = n * o * n⁻¹ := by
  obtain ⟨tA', htA', -, -, -, -, -, -, -, hfusD⟩ := g24_classes
  have htt : tA' = tA := htA'.unique htA
  obtain ⟨-, o', ho', -, -, -, -, hout⟩ := outer_facts
  have hoo : o' = o := ho'.unique ho
  intro s hs hsq hs1
  by_cases hsD : s ∈ twoBD
  · rcases hfusD s hsD hsq hs1 with ⟨d, hd, e⟩ | ⟨d, hd, e⟩
    · refine Or.inl ⟨d⁻¹, Subgroup.le_normalizer (inv_mem hd), ?_⟩
      rw [← htt, ← e]
      group
    · refine Or.inr (Or.inl ⟨d⁻¹, Subgroup.le_normalizer (inv_mem hd), ?_⟩)
      rw [← e]
      group
  · obtain ⟨d, hd, e⟩ := hout hN s hs hsq hsD
    refine Or.inr (Or.inr ⟨d⁻¹, Subgroup.le_normalizer (inv_mem hd), ?_⟩)
    rw [← hoo, ← e]
    group

end Outer

end CFSG.EvenSporadicStandard.G24Aut
