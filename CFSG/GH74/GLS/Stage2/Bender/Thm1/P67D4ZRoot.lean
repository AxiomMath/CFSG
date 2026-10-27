module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Defs
public import CFSG.ClassicalInvolution.Balance.BootstrapExoticD4Sl3
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Field
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStage

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalInvolution.Balance

theorem d4_root_trichotomy (β : Fin d4.rank → ℤ)
    (hβ : IsRoot d4 β) :
    (rho β = β ∧ (β 0 + β 1 + β 3) % 3 = 0) ∨ (rho β ≠ β ∧ (β 0 + β 1 + β 3) % 3 ≠ 0) := by
  obtain ⟨k, hk, rfl⟩ := (isRoot_d4_iff).1 hβ
  clear hβ
  revert k
  decide +kernel

theorem rootChar_z {K : Type} [Field K] (ω : Kˣ) (β : Fin d4.rank → ℤ) :
    rootChar (τ := d4) ![ω, ω, 1, ω] β = ω ^ (β 0 + β 1 + β 3) := by
  have e : ∀ f : Fin d4.rank → Kˣ, ∏ x, f x = f 0 * f 1 * f 2 * f 3 := fun f =>
    Fin.prod_univ_four f
  unfold rootChar
  rw [e]
  simp [zpow_add]

theorem rootChar_z_fixed {K : Type} [Field K] (ω : Kˣ)
    (hω : ω ^ 3 = 1) {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) (hρ : rho β = β) :
    rootChar (τ := d4) ![ω, ω, 1, ω] β = 1 := by
  rw [rootChar_z]
  rcases d4_root_trichotomy β hβ with ⟨-, h⟩ | ⟨h, -⟩
  · obtain ⟨m, hm⟩ : (3 : ℤ) ∣ β 0 + β 1 + β 3 := Int.dvd_of_emod_eq_zero h
    rw [hm, zpow_mul]
    simp [hω]
  · exact absurd hρ h

theorem rootChar_z_ne_one {K : Type} [Field K] (ω : Kˣ)
    (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) (hρ : rho β ≠ β) :
    rootChar (τ := d4) ![ω, ω, 1, ω] β ≠ 1 := by
  rw [rootChar_z]
  rcases d4_root_trichotomy β hβ with ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd h hρ
  · intro h1
    have hord : orderOf ω = 3 := orderOf_eq_prime hω hω1
    have h2 : ((orderOf ω : ℕ) : ℤ) ∣ β 0 + β 1 + β 3 := orderOf_dvd_iff_zpow_eq_one.2 h1
    rw [hord] at h2
    exact h (Int.emod_eq_zero_of_dvd (by exact_mod_cast h2))

end CFSG.GH74.GLS.Stage2.Bender.Thm1
