module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoBYf
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoASig

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools
open CFSG.ComponentClassification.HarrisLit (SectionalRankLeFour)
open CFSG.ComponentClassification.HSFLit (HaradaInput)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A] [Finite A]

namespace LocalDatum

variable (Δ : LocalDatum X A)

theorem coreOut
    (hH : HaradaInput) (hA : AutFacts Δ) (hX : ¬ SectionalRankLeFour X) : Δ.CoreOut := by
  rcases hA.dichotomy with h1 | ⟨k, h2⟩
  · exact (Δ.false_of_caseOne hH hA hX h1).elim
  rcases Δ.out_or_sqrt h2 with h | ⟨c, hcS, hcD, hct⟩
  · exact h
  exfalso
  obtain ⟨φ⟩ := Δ.nonempty_fusion hA hX
  by_cases hu : ∃ u ∈ Δ.D, u ≠ 1 ∧ φ.x⁻¹ * u * φ.x ∈ Δ.D
  · have hxz := TwoA_conj_dz h2 φ hu
    have hxQ : ∀ q ∈ Δ.Q, ∀ d ∈ Δ.D, φ.x * q * φ.x⁻¹ * d = d * (φ.x * q * φ.x⁻¹) :=
      fun q hq d hd => TwoA_commute h2 φ hxz hq hd
    have hQ := TwoA_Q h2 φ hxQ
    have hxt := TwoA_conj_t h2 φ hxz hxQ hQ hcS hcD hct
    by_cases hσ : ∃ σ ∈ Δ.S, σ ^ 2 = 1 ∧ Δ.ψe σ ∉ Δ.Dbar
    · obtain ⟨σ, hσS, hσ2, hσD⟩ := hσ
      exact TwoA_false_of_sigma h2 φ hA hX hxt hxz hQ hcS hcD hct hσS hσ2 hσD
    · push Not at hσ
      exact TwoA_false_of_inv h2 φ hQ hcS hcD hct hσ
  · push Not at hu
    exact TwoB_false h2 hH hA hX φ fun u hu' hu'' => by
      by_contra h1
      exact hu u hu' h1 hu''

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
