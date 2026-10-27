module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.TorusScale
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ExtractUNoT

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed
open scoped MatrixGroups commutatorElement

section NormaliseShort


variable {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)

section WithCerts


include hσ in
theorem hHat_le_normalizer_longSub :
    (⨆ i, hHat σ.toRingHom i) ≤ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)) := by
  have RG := d4RGD2 σ.toRingHom hσ
  intro h hh
  have hg := RG.goodActEven_of_mem_H (n := 6) hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_longSub (by norm_num) (by norm_num) hg hx
  · intro hx
    have := conj_mem_longSub (by norm_num) (by norm_num) hg.inv hx
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rwa [e] at this

include hσ in
theorem exists_torus_conj_short_one [Finite K]
    {H : Subgroup (twistedGroup σ.toRingHom)} (hs : HasShortRoot H) :
    ∃ t ∈ (⨆ i, hHat σ.toRingHom i), d4X hσ 2 (1 : K) ∈ H.map (MulAut.conj t).toMonoidHom ∨
      d4X hσ 4 (1 : K) ∈ H.map (MulAut.conj t).toMonoidHom := by
  obtain ⟨k, hk, x, hx, hxH, hx1⟩ := hs
  have h1 : ((1 : fixedUnits σ.toRingHom) : Kˣ) = 1 := rfl
  rcases hk with rfl | rfl
  · obtain ⟨c, rfl⟩ : ∃ c : K, d4X hσ 4 c = x :=
      (mem_hexGroup_iff' hσ 4 (by norm_num : ((4 : Fin 6) : ℤ) + 1 = 5)).1 hx
    have hc : c ≠ 0 := by
      rintro rfl
      exact hx1 ((d4X_eq_one_iff hσ).2 rfl)
    obtain ⟨t, ht⟩ := exists_t_chi_four hσ (Units.mk0 c hc)⁻¹
    refine ⟨tor hσ 1 t, Subgroup.mem_iSup_of_mem (ng 1) (d4z_tor_one_mem_hHat hσ t),
      Or.inr ⟨d4X hσ 4 c, hxH, ?_⟩⟩
    show tor hσ 1 t * d4X hσ 4 c * (tor hσ 1 t)⁻¹ = d4X hσ 4 (1 : K)
    rw [tor_conj_d4X_four hσ 1 t c, h1, ht]
    refine congrArg (d4X hσ 4) ?_
    exact (show ((((Units.mk0 c hc)⁻¹ : Kˣ) : K) * c = 1) from by
      rw [Units.val_inv_eq_inv_val, Units.val_mk0]; exact inv_mul_cancel₀ hc)
  · obtain ⟨c, rfl⟩ : ∃ c : K, d4X hσ 2 c = x :=
      (mem_hexGroup_iff' hσ 2 (by norm_num : ((2 : Fin 6) : ℤ) + 1 = 3)).1 hx
    have hc : c ≠ 0 := by
      rintro rfl
      exact hx1 ((d4X_eq_one_iff hσ).2 rfl)
    obtain ⟨t, ht⟩ := exists_t_chi_two hσ (Units.mk0 c hc)⁻¹
    refine ⟨tor hσ 1 t, Subgroup.mem_iSup_of_mem (ng 1) (d4z_tor_one_mem_hHat hσ t),
      Or.inl ⟨d4X hσ 2 c, hxH, ?_⟩⟩
    show tor hσ 1 t * d4X hσ 2 c * (tor hσ 1 t)⁻¹ = d4X hσ 2 (1 : K)
    rw [tor_conj_d4X_two hσ 1 t c, h1, ht]
    refine congrArg (d4X hσ 2) ?_
    exact (show ((((Units.mk0 c hc)⁻¹ : Kˣ) : K) * c = 1) from by
      rw [Units.val_inv_eq_inv_val, Units.val_mk0]; exact inv_mul_cancel₀ hc)

end WithCerts

end NormaliseShort

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
