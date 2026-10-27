module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WPaired
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WLeaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WPGU
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WTransport

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Module CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem ivk93w_u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk93WEmpty (fun X _ => LieModel X .PSU 4 p f) := by
  intro p f hp hp2 hf _ J _ _ hJ x q B h hB
  obtain ⟨⟨-, -, -⟩, K, _, _, hK, ⟨φ⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  have : Finite (StatedProj (StatedSU (2 * 2 + 0) (p ^ f) K)) := Finite.of_equiv _ φ.toEquiv
  have h' := Ivk93W.of_equiv (J' := StatedProj (StatedSU (2 * 2 + 0) (p ^ f) K)) φ h
  obtain ⟨hud, A, hA, M, hM, ⟨e⟩⟩ :=
    h'.exists_unitary hp hf hK (r := 2) (ε := 0) (by norm_num) (by norm_num)
  have : Finite K := hud.finite
  have hdim : finrank K (HypIndex 2 0 → K) = 4 := UnitaryHigher.finrank_hypIndex_fun
  obtain ⟨hq, hcases⟩ := ivk93w_unitary_block hud hp2 (V := HypIndex 2 0 → K) (by omega)
    (hypForm_isSymm hud) (hypForm_separatingLeft hud) hA hM
  rcases hcases with ⟨k, _, _, hk, hq3', ⟨eSL⟩⟩ | ⟨d, hd3, hdn, ⟨eP⟩⟩ | ⟨m, hm, hsimple⟩
  ·
    have hodd : Odd (Nat.card k) := by
      rw [hk]
      exact (hp.odd_of_ne_two hp2).pow
    have h5 : 5 ≤ Nat.card k := by
      rw [hk]
      exact ivk93w_five_le_pow hp hp2 hf hq3'
    have hqk := h'.q_eq_of_equiv_sl2 hodd h5 (eSL.trans e.symm)
    have hB' := Ivk93WBound.of_equiv φ hB
    rw [← hqk, hk] at hB'
    exact ivk93w_false_of_bound hp hp2 hf hK (d := 4) (Or.inl rfl) hB'
  ·
    obtain ⟨ψ, hψ⟩ := ivk93w_quaternion_psu hud hp2 hd3
    exact h'.false_of_quaternion e hq (eP.symm.toMonoidHom.comp ψ) (eP.symm.injective.comp hψ)
  ·
    have hm2 : m = 2 := by omega
    have := hsimple hm2
    exact h'.false_of_simple (MulEquiv.isSimpleGroup e)

end CFSG.GH74.GLS.IVK.Proofs2
