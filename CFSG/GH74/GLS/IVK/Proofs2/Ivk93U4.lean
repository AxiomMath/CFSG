module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Field
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93UBlock
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Module CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem ivk93_five_le_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h3 : p ^ f ≠ 3) : 5 ≤ p ^ f := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h1 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by omega) p)
  have h2 : p ^ f % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  omega

theorem ivk93_u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk93Eq (fun X _ => LieModel X .PSU 4 p f) (p ^ f) := by
  intro p f hp hp2 hf _ J _ _ hJ x hx q L₁ L₂ h
  obtain ⟨⟨-, -, -⟩, K, _, _, hK, ⟨φ⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  have : Finite (StatedProj (StatedSU (2 * 2 + 0) (p ^ f) K)) := Finite.of_equiv _ φ.toEquiv
  have h' := h.of_equiv (J' := StatedProj (StatedSU (2 * 2 + 0) (p ^ f) K)) φ
  obtain ⟨hud, A, hA, M₁, M₂, hM₁, hM₂, hne, ⟨e₁⟩, -⟩ :=
    h'.exists_unitary' hp hf hK (r := 2) (ε := 0) (by norm_num) (by norm_num)
  have : Finite K := hud.finite
  have hdim : finrank K (HypIndex 2 0 → K) = 4 := UnitaryHigher.finrank_hypIndex_fun
  obtain ⟨d₁, d₂, hd, h₂₁, h₂₂, ⟨-, b₁, -⟩, -⟩ :=
    ivk93_unitary_two_pComponents_blocks hud hp2 (by omega) (hypForm_isSymm hud)
      (hypForm_separatingLeft hud) hA hM₁ hM₂ hne
  obtain ⟨hq3, k, _, _, hk, ⟨eSL⟩⟩ := b₁ (by omega)
  have hodd : Odd (Nat.card k) := by
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ Nat.card k := by
    rw [hk]
    exact ivk93_five_le_pow hp hp2 hf hq3
  have := h'.q_eq_of_equiv_sl2 hodd h5 (eSL.trans e₁.symm)
  rw [hk] at this
  exact this

end CFSG.GH74.GLS.IVK.Proofs2
