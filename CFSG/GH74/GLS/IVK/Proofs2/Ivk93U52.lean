module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93UBlock2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93UBlock

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Module CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem ivk93_u52 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 →
    Ivk93Empty2 (fun X _ => LieModel X .PSU 5 p f) := by
  intro p f hp hf hmod
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp hf)
    omega
  intro J _ _ hJ x hx q₁ q₂ L₁ L₂ h
  obtain ⟨⟨-, -, -⟩, K, _, _, hK, ⟨φ⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  have : Finite (StatedProj (StatedSU (2 * 2 + 1) (p ^ f) K)) := Finite.of_equiv _ φ.toEquiv
  have h' := h.of_equiv (J' := StatedProj (StatedSU (2 * 2 + 1) (p ^ f) K)) φ
  obtain ⟨hud, A, hA, M₁, M₂, hM₁, hM₂, hne, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    h'.exists_unitary' hp hf hK (r := 2) (ε := 1) (by norm_num) (by norm_num)
  have : Finite K := hud.finite
  have hdim : finrank K (HypIndex 2 1 → K) = 5 := UnitaryHigher.finrank_hypIndex_fun
  obtain ⟨d₁, d₂, hd, h₂₁, h₂₂, ⟨hq₁, -, b₁⟩, ⟨hq₂, -, b₂⟩⟩ :=
    ivk93_unitary_two_pComponents_blocks hud hp2 (by omega) (hypForm_isSymm hud)
      (hypForm_separatingLeft hud) hA hM₁ hM₂ hne
  rcases (by omega : 3 ≤ d₁ ∨ 3 ≤ d₂) with h3 | h3
  · obtain ⟨ψ, hψ⟩ := b₁ h3
    exact h'.false_of_quaternion e₁ hq₁ ψ hψ
  · obtain ⟨ψ, hψ⟩ := b₂ h3
    exact h'.symm.false_of_quaternion e₂ hq₂ ψ hψ

end CFSG.GH74.GLS.IVK.Proofs2
