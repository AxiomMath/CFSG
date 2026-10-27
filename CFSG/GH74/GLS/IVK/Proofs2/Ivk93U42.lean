module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Field2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93U4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93UBlock2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Module CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem ivk93_u42 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk93Eq2 (fun X _ => LieModel X .PSU 4 p f) (p ^ f) := by
  intro p f hp hp2 hf _ J _ _ hJ x hx q₁ q₂ L₁ L₂ h
  obtain ⟨⟨-, -, -⟩, K, _, _, hK, ⟨φ⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  have : Finite (StatedProj (StatedSU (2 * 2 + 0) (p ^ f) K)) := Finite.of_equiv _ φ.toEquiv
  have h' := h.of_equiv (J' := StatedProj (StatedSU (2 * 2 + 0) (p ^ f) K)) φ
  obtain ⟨hud, A, hA, M₁, M₂, hM₁, hM₂, hne, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    h'.exists_unitary' hp hf hK (r := 2) (ε := 0) (by norm_num) (by norm_num)
  have : Finite K := hud.finite
  have hdim : finrank K (HypIndex 2 0 → K) = 4 := UnitaryHigher.finrank_hypIndex_fun
  obtain ⟨d₁, d₂, hd, h₂₁, h₂₂, ⟨-, b₁, -⟩, ⟨-, b₂, -⟩⟩ :=
    ivk93_unitary_two_pComponents_blocks hud hp2 (by omega) (hypForm_isSymm hud)
      (hypForm_separatingLeft hud) hA hM₁ hM₂ hne
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨hq3, k, _, _, hk, ⟨eSL⟩⟩ := b₁ (by omega)
  obtain ⟨hq3', k', _, _, hk', ⟨eSL'⟩⟩ := b₂ (by omega)
  have h1 := h'.q_eq_of_equiv_sl2 (by rw [hk]; exact hodd)
    (by rw [hk]; exact ivk93_five_le_pow hp hp2 hf hq3) (eSL.trans e₁.symm)
  have h2 := h'.q_eq_of_equiv_sl2' (by rw [hk']; exact hodd)
    (by rw [hk']; exact ivk93_five_le_pow hp hp2 hf hq3') (eSL'.trans e₂.symm)
  rw [hk] at h1
  rw [hk'] at h2
  exact ⟨h1, h2⟩

end CFSG.GH74.GLS.IVK.Proofs2
