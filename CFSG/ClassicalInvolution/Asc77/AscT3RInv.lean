module

public import CFSG.ClassicalInvolution.Asc77.AscT3RCoset
public import CFSG.ClassicalInvolution.Asc77.AscT3RPsi

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3R

open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.GorensteinWalter
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups commutatorElement Pointwise

section Inv

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
  {L : Subgroup G} {e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F)}

theorem exists_field_involution_mul (hF : Odd (Nat.card F)) (hK : IsOddPrimePower (Nat.card F))
    (h4 : 4 ≤ Nat.card F) {T RL : Subgroup G} (hT2 : IsPGroup 2 ↥T)
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hRT : RL ≤ T) (hRL : IsSylow2In RL L)
    (hTR : ∀ x ∈ T, x ∈ Subgroup.normalizer (RL : Set G)) {σ : F ≃+* F} (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) {x : G} (hxT : x ∈ T) (hε : epsG hK L e x = 1) (hρ : rhoG L e x = σ) :
    ∃ r ∈ RL, ∃ γ : MulAut SL(2, F), phiG L e (x * r) = γ * slFieldAut F σ * γ⁻¹ := by
  classical
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 SL(2, F)))
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hTN hxT
  have hα2 : phiG L e x * phiG L e x ∈ phiImage L e RL := by
    have hin : phiG L e (x * x) ∈ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range := by
      apply (slEps_slRho_eq_one_iff F hK h4 _).mp
      refine ⟨?_, ?_⟩
      · have h1 : epsG hK L e (x * x) = epsG hK L e x * epsG hK L e x := epsG_mul hxN hxN
        rw [hε, mul_one] at h1
        exact h1
      · have h1 : rhoG L e (x * x) = rhoG L e x * rhoG L e x := rhoG_mul hxN hxN
        rw [hρ, hσ2] at h1
        exact h1
    obtain ⟨r, hr, hrx⟩ := exists_mem_of_phiG_inner hF hT2 hTN hRT hRL (T.mul_mem hxT hxT) hin
    rw [← phiG_mul hxN hxN, ← hrx]
    exact phiG_mem_phiImage hr (hTN (hRT hr))
  have hαD : ∀ d ∈ phiImage L e RL, (phiG L e x)⁻¹ * d * phiG L e x ∈ phiImage L e RL := by
    intro d hd
    obtain ⟨r, hr, hrN, rfl⟩ := mem_phiImage.mp hd
    have hxinv : x⁻¹ ∈ Subgroup.normalizer (RL : Set G) := Subgroup.inv_mem _ (hTR x hxT)
    have hr' : x⁻¹ * r * x⁻¹⁻¹ ∈ RL := (Subgroup.mem_normalizer_iff.mp hxinv r).mp hr
    have hxN' : x⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hxN
    have : (phiG L e x)⁻¹ * phiG L e r * phiG L e x = phiG L e (x⁻¹ * r * x⁻¹⁻¹) := by
      rw [phiG_mul (Subgroup.mul_mem _ hxN' hrN) (by simpa using hxN), phiG_mul hxN' hrN,
        phiG_inv hxN, inv_inv]
    rw [this]
    exact phiG_mem_phiImage hr' (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN' hrN)
      (by simpa using hxN))
  obtain ⟨d, hd, -, γ, hdγ⟩ := exists_involution_mem_coset hF hK h4 Q hσ2 hσ1
    (α := phiG L e x) hε hρ (phiImage_le_inn hRL.1) (isPGroup_phiImage hRL.2.1)
    (two_mul_natCard_phiImage (e := e) hF Q hRL) hαD hα2
  obtain ⟨r, hr, hrN, rfl⟩ := mem_phiImage.mp hd
  exact ⟨r, hr, γ, by rw [phiG_mul hxN hrN]; exact hdγ⟩

end Inv

end CFSG.ClassicalInvolution.Asc77.T3CII.T3R
