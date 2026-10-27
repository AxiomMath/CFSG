module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtensionData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open CFSG.Open Bender

theorem bender_involution_automorphism_inner (X : Type) [Group X] [Finite X]
    (hX : CFSG.Open.fusionIsBenderGroup X) (α : MulAut X) (hα : α * α = 1)
    (hT : ∃ T : Sylow 2 X, ∀ x : X, α x = x →
      x ∈ Subgroup.normalizer ((T : Subgroup X) : Set X)) :
    ∃ y : X, α = MulAut.conj y := by
  obtain ⟨T, hT⟩ := hT
  obtain ⟨q, k, hq4, hB⟩ := (BenderExt.benderData_of_isBenderGroup hX).borel
  have hSE : ∀ S : Sylow 2 X,
      fusionStronglyEmbedded (Subgroup.normalizer ((S : Subgroup X) : Set X)) :=
    fun S => (benderBorel_sylowCenter hB S).1
  have hodd : Odd (Nat.card (Sylow 2 X)) :=
    Nat.not_even_iff_odd.mp fun he => not_dvd_card_sylow (p := 2) (G := X) (even_iff_two_dvd.mp he)
  have hnt : ∀ S : Sylow 2 X, (S : Subgroup X) ≠ ⊥ := by
    intro S hS
    obtain ⟨-, -, hZcard, -⟩ := benderBorel_sylowCenter hB S
    have h1 := Subgroup.card_le_of_le (sylowCenter_le (S : Subgroup X))
    rw [hZcard, hS, Subgroup.card_bot] at h1
    omega
  have hdich : ∀ S : Sylow 2 X, InvDichotomyAt (S : Subgroup X) := by
    rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact invDichotomyAt_of_mulEquiv_psl2 hf e
    · exact invDichotomyAt_of_mulEquiv_psu3 hf e
    · exact invDichotomyAt_of_mulEquiv_sz ha e
  exact exists_eq_conj_of_dichotomy hSE hodd hnt hdich α hα T hT

end CFSG.ComponentClassification.AschbacherToolkit
