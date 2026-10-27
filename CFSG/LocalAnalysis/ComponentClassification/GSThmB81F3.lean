module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81F2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4e

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

theorem exists_lieModel_Jbar (H₁ : h.L81Hyp) : ∃ p' f' : ℕ, p'.Prime ∧ p' ≠ 2 ∧ 1 ≤ f' ∧
    Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p' f' := by
  obtain ⟨-, p, f, hp, hp2, hf, -, hJ⟩ := Hyp52.Sec8Case.exists_params h.toHyp52 H₁.case8
  exact lieModel_of_isSec8JType hp hp2 hf hJ

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)

theorem rhoImg_mul_self {E : Subgroup H} (hE : ∀ e ∈ E, e * e = 1) :
    ∀ w ∈ Seven.rhoImg h.J E, w * w = 1 := by
  rintro _ ⟨e, he, rfl⟩
  rw [← map_mul]
  have : e * e = 1 := Subtype.ext (hE _ (mem_subgroupOf.mp he))
  rw [this, map_one]

include d in
theorem card_elem_le (hRk : CFL2Rank) {E : Subgroup H} (hES : E ≤ h.S)
    (hE : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 32 := by
  have hEN : E ≤ normalizer (h.J : Set H) := hES.trans h.toHyp52.S_le_normalizer
  have h1 := Seven.card_eq_card_rhoImg_mul hEN
  obtain ⟨p', f', hp', hp2', hf', hJL⟩ := H₁.exists_lieModel_Jbar
  have h2 : Nat.card (Seven.rhoImg h.J E) ≤ 8 :=
    hRk _ p' f' hp' hp2' hf' hJL _ (rhoImg_mul_self hE)
  obtain ⟨β, hP⟩ := d.pres
  have h3 : Nat.card ↥(E ⊓ coreActionKernel h.J) ≤ 4 :=
    hP.card_le_four (fun w hw => mem_inf.mpr ⟨hES (mem_inf.mp hw).1, (mem_inf.mp hw).2⟩)
      (fun w hw => hE w (mem_inf.mp hw).1)
  rw [h1]
  calc _ ≤ 8 * 4 := Nat.mul_le_mul h2 h3
    _ = 32 := by norm_num

theorem D_inf_R0 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    h.D ⊓ d.R0 = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwD, hwR⟩ := mem_inf.mp hw
  obtain ⟨π, hπ, rfl | rfl⟩ := d.mem_R0_cases hwR
  · rw [← h.toHyp52.D_inf_P_eq_bot H₁.center_J]
    exact mem_inf.mpr ⟨hwD, hπ⟩
  · exfalso
    apply d.tau_not_mem_DP hCF1 hCF2 F
    have hc := H₁.D_comm_P hwD (inv_mem hπ)
    have hτ : d.tau = d.sigma * d.b := by
      show d.tau = d.tau * d.b * d.b
      rw [mul_assoc, d.b_mul_self, mul_one]
    have h1 : d.tau = π * d.sigma * (π⁻¹ * d.b) := by
      rw [show π * d.sigma * (π⁻¹ * d.b) = (π * d.sigma * π⁻¹) * d.b by group, hc,
        ← mul_assoc π⁻¹ π d.sigma, inv_mul_cancel, one_mul]
      exact hτ
    rw [h1]
    exact mul_mem_sup hwD (mul_mem (inv_mem hπ) d.b_mem_P)

theorem card_rhoImg_R0_le {X : Subgroup H} (hX : X ≤ d.R0) :
    Nat.card (Seven.rhoImg h.J X) ≤ 2 := by
  set σρ := Eight.oddBarAction h.J ⟨d.sigma, h.toHyp52.S_le_normalizer d.sigma_mem_S⟩
  have hle : Seven.rhoImg h.J X ≤ zpowers σρ := by
    rintro _ ⟨⟨r, hrN⟩, hr, rfl⟩
    have hrR : r ∈ d.R0 := hX (mem_subgroupOf.mp hr)
    obtain ⟨π, hπ, hr' | hr'⟩ := d.mem_R0_cases hrR
    · subst r
      have : Eight.oddBarAction h.J ⟨π, hrN⟩ = 1 :=
        (rho_eq_one_iff (h := h) (mem_inf.mp hπ).1).mpr hπ
      rw [this]
      exact one_mem _
    · subst r
      have h1 : (⟨π * d.sigma, hrN⟩ : ↥(normalizer (h.J : Set H))) =
          ⟨π, h.toHyp52.S_le_normalizer (mem_inf.mp hπ).1⟩ *
            ⟨d.sigma, h.toHyp52.S_le_normalizer d.sigma_mem_S⟩ := rfl
      rw [h1, map_mul, (rho_eq_one_iff (h := h) (mem_inf.mp hπ).1).mpr hπ, one_mul]
      exact mem_zpowers _
  refine (card_le_of_le hle).trans ?_
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by norm_num) (by
    rw [pow_two, ← map_mul, show (⟨d.sigma, h.toHyp52.S_le_normalizer d.sigma_mem_S⟩ :
        ↥(normalizer (h.J : Set H))) * ⟨d.sigma, h.toHyp52.S_le_normalizer d.sigma_mem_S⟩ = 1
      from Subtype.ext d.sigma_mul_self, map_one])

theorem card_elem_R0 {X : Subgroup H} (hX : X ≤ d.R0) (hX2 : ∀ x ∈ X, x * x = 1) :
    Nat.card X ≤ 8 := by
  have hXN : X ≤ normalizer (h.J : Set H) :=
    hX.trans (d.R0_le_S.trans h.toHyp52.S_le_normalizer)
  have h1 := Seven.card_eq_card_rhoImg_mul hXN
  obtain ⟨β, hP⟩ := d.pres
  have h3 : Nat.card ↥(X ⊓ coreActionKernel h.J) ≤ 4 :=
    hP.card_le_four (fun w hw => mem_inf.mpr ⟨d.R0_le_S (hX (mem_inf.mp hw).1),
      (mem_inf.mp hw).2⟩) (fun w hw => hX2 w (mem_inf.mp hw).1)
  rw [h1]
  calc _ ≤ 2 * 4 := Nat.mul_le_mul (d.card_rhoImg_R0_le hX) h3
    _ = 8 := by norm_num

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
