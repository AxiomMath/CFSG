module

public import CFSG.ClassicalInvolution.SmallCases.NDBE9Main
public import CFSG.ClassicalInvolution.SmallCases.NDBE4SModel

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77 CFSG.LieType.Universal.Spin CFSG.LieType.Universal
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.NDB.SpinVertex CFSG.ClassicalInvolution.NDB.ExoticModel

variable (p : ℕ) [Fact p.Prime]

theorem spinOuterKleinAlpha_proved : SpinOuterKleinAlpha p := by
  intro t n e ht hp2 hq hadm H _ _ ψ hψ R hR x hx v hv hv2 hvR hout
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have h5 : 5 ≤ Nat.card (GaloisField p e) := by rw [GaloisField.card p e he]; exact hq
  have h2 := ModelFacts.two_ne_zero_galoisField e hp2
  have hσ2 : ∀ y, MulAut.conj v (MulAut.conj v y) = y := fun y => by
    simp only [MulAut.conj_apply]
    rw [show v * (v * y * v⁻¹) * v⁻¹ = (v * v) * y * (v * v)⁻¹ by group, hv2]
    group
  have hσr : ∀ k, MulAut.conj v (ψ k) ∈ ψ.range := fun k =>
    (Subgroup.mem_normalizer_iff.mp hv (ψ k)).mp ⟨k, rfl⟩
  have hfixR : ∀ r ∈ R, MulAut.conj v (ψ r) = ψ r := fun r hr => by
    rw [MulAut.conj_apply, hvR r hr, mul_inv_cancel_right]
  have hfin : ∀ {R' : Subgroup (modelUniv t n p e Fact.out).K},
      (∀ r ∈ R', MulAut.conj v (ψ r) = ψ r) → ∀ r ∈ R', v * ψ r = ψ r * v := fun h r hr => by
    have h1 := h r hr
    rw [MulAut.conj_apply] at h1
    calc v * ψ r = v * ψ r * v⁻¹ * v := by group
      _ = ψ r * v := by rw [h1]
  have hxo := orderOf_eq_two_of_isUniqueInvolution hx
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hQuot := centralQuot_odd (p := p) (f := e) hp2 (le_refl 3) hq
    obtain ⟨i, fr, hRfr, hi⟩ := hQuot.map_mem R hR
    obtain ⟨R', hR', htw⟩ := oddTwinsExist hp2 hq hadm R hR
    have htwin := IsFundTwin.to_map _ hQuot.ker_le hQuot.perf hQuot.surj hR hR' htw
    rw [hRfr] at htwin
    have hdim : Module.finrank (GaloisField p e) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) = 7 :=
      finrank_odd p e 3
    have hR'fr := eq_swap_of_isFundTwin hodd
      (fun R₀ R₁ i₀ i₁ h₀ h₁ hc => commuting_same_involution hodd (by rw [hdim]; omega) h₀ h₁ hc)
      fr (hQuot.map_mem R' hR') htwin
    have hvR' := hfin (oddTwinFixed_spin hq hadm ψ hψ (MulAut.conj v) hσ2 hσr hR hR' htw hfixR)
    have hxθ : spinAction _ x = fr.La (-1) := by
      have h1 := invOf_eq hodd ⟨fr, hRfr, hi⟩ (hQuot.invOf hR ⟨hx.mem, hxo⟩)
      rw [h1, hi]
    have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField p e))) :=
      isPerfect_spinGroup_quadOdd h2 le_rfl
    exact alphaOf_outer hodd h5 (nondegenerate_polarBilin_quadOdd 3 _ h2)
      (range_spinAction_quadOdd h2 le_rfl) fr (by rw [hdim]) hψ
      (liftSim_quadOdd hp2 le_rfl (by omega) ψ hψ) hRfr hR'fr hx.mem hxθ hx.sq hv hv2 hvR hvR'
      hout
  · have hQuot := centralQuot_minus (p := p) (f := e) hp2 hq hadm
    obtain ⟨i, fr, hRfr, hi⟩ := hQuot.map_mem R hR
    obtain ⟨R', hR', htw⟩ := minusTwinsExist_four hp2 hq hadm R hR
    have htwin := IsFundTwin.to_map _ hQuot.ker_le hQuot.perf hQuot.surj hR hR' htw
    rw [hRfr] at htwin
    have h4 : 4 ≤ Nat.card (GaloisField p e) := by omega
    have hR'fr := eq_swap_of_isFundTwin hodd
      (fun R₀ R₁ i₀ i₁ h₀ h₁ hc =>
        quadMinus_four_same_involution hodd (minusCoeffs_irr p e) h4 h₀ h₁ hc)
      fr (hQuot.map_mem R' hR') htwin
    have hvR' := hfin (minusTwinFixed_spin hp2 hq hadm ψ hψ (MulAut.conj v) hσ2 hσr hR hR' htw
      hfixR)
    have hxθ : spinAction _ x = fr.La (-1) := by
      have h1 := invOf_eq hodd ⟨fr, hRfr, hi⟩ (hQuot.invOf hR ⟨hx.mem, hxo⟩)
      rw [h1, hi]
    have : Group.IsPerfect (spinGroup (quadMinus 4 (GaloisField p e) (minusCoeffs p e).1
        (minusCoeffs p e).2)) := isPerfect_spinGroup_quadMinus le_rfl (minusCoeffs_irr p e)
    have hdim : Module.finrank (GaloisField p e)
        (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p e) = 8 := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp
    exact alphaOf_outer hodd h5
      (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr p e))
      (range_spinAction_quadMinus le_rfl (minusCoeffs_irr p e)) fr (by rw [hdim]; omega) hψ
      (liftSim_quadMinus hp2 le_rfl (by omega) ψ hψ) hRfr hR'fr hx.mem hxθ hx.sq hv hv2 hvR hvR'
      hout

end CFSG.ClassicalInvolution.NDB
