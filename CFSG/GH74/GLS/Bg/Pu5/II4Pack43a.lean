module

public import CFSG.GH74.GLS.Bg.Pu5.II4Pack
public import CFSG.GH74.GLS.Bg.Pu5.II4PackMat

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Lifted
open CFSG.Semidihedral.MatrixCoverData (slConjugation)
open CFSG.GH74.GLS.Stage1.Thm2.Recip (innOf)

theorem ii4_two_ne_zero_of_odd_card {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  intro h2
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F = 2 :=
    CharP.ringChar_of_prime_eq_zero Nat.prime_two (by exact_mod_cast h2)
  have h0 := FiniteField.even_card_iff_char_two.1 hchar
  rw [← Nat.card_eq_fintype_card] at h0
  exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_iff.2 h0)

theorem ii4_mem_center_equiv_iff {G H : Type} [Group G] [Group H] (e : G ≃* H) {c : G} :
    e c ∈ Subgroup.center H ↔ c ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e g)
  · intro h g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, h g']

theorem ii4_43a (h2A7 : II4_2A7) {Q : Type} [Group Q] [Finite Q] (hO : HatOK Q)
    (φ : MulAut Q) (hφ2 : φ * φ = 1) (hφin : φ ∉ innOf Q) (hφf : ¬ IsFAutomorphism Q φ) :
    ∀ c : Q, orderOf c = 4 → φ c ≠ c := by
  rcases sl_or_a7 hO.sl2 with ⟨F, _, _, hodd, h3, ⟨e⟩⟩ | h7
  · intro c hc4 hφc
    have hα2 : MulAut.congr e φ * MulAut.congr e φ = 1 := by rw [← map_mul, hφ2, map_one]
    have hFC : ¬ FixedCond Q φ := fun h =>
      hφf (isFAutomorphism_of_fixedCond hO.quasi hO.kgrp hO.rank hφ2 h)
    have hσ : (gammaOf hodd h3 (MulAut.congr e φ)).right = 1 := by
      by_contra h
      exact hFC (fixedCond_of_congr e (fixedCond_of_field_part hodd h3 _ hα2 h))
    obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 _ hσ
    obtain ⟨hcz, hcc, -⟩ := ii4_orderFour_facts hO hc4
    have hfix : slConjugation F G (e c) = e c := by
      rw [← hG]
      show (MulAut.congr e φ) (e c) = e c
      simp [MulAut.congr_apply, hφc]
    obtain ⟨s, hs⟩ := ii4_inner_of_slConjugation_fix (ii4_two_ne_zero_of_odd_card hodd) G
      (by rw [← hG]; exact hα2) (e c) (fun h => hcz ((ii4_mem_center_equiv_iff e).1 h))
      (by rw [← map_mul]; exact (ii4_mem_center_equiv_iff e).2 hcc) hfix
    apply hφin
    refine ⟨e.symm s, ?_⟩
    apply (MulAut.congr e).injective
    rw [congr_conj, MulEquiv.apply_symm_apply, ← hs, ← hG]
  · exact fun c _ _ => absurd ((h2A7 Q h7).2.2.1 φ hφ2 hφin hO.kgrp) hφf

theorem ii4_43f (h2A7 : II4_2A7) {Q : Type} [Group Q] [Finite Q] (hO : HatOK Q)
    (φ ψ : MulAut Q) (hφ2 : φ * φ = 1) (hψ2 : ψ * ψ = 1) (hcomm : φ * ψ = ψ * φ)
    (hφ1 : φ ≠ 1) (hψ1 : ψ ≠ 1) (hne : φ ≠ ψ)
    (hφf : ¬ IsFAutomorphism Q φ) (hψf : ¬ IsFAutomorphism Q ψ) (hψin : ψ ∈ innOf Q) :
    ∃ u : Q, orderOf u = 4 ∧ ψ u = u ∧ φ u = u⁻¹ :=
  ii4_43f_of_43a hO (fun φ' h2 hin hf => ii4_43a h2A7 hO φ' h2 hin hf) φ ψ hφ2 hψ2 hcomm hφ1 hψ1
    hne hφf hψf hψin

end CFSG.GH74.GLS.Bg.Pu5
