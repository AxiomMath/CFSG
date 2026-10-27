module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCRho
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCTrans

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem fzc_rho_norm_R (hs : FzCSteps t L S x₁ x₂ lam rho) {x : G} (hx : x ∈ fzR t x₁ x₂) :
    rho * x * rho⁻¹ ∈ fzR t x₁ x₂ := by
  exact fzc_conj_mem_R hs (fzc_rho_mem_N hs) hx

theorem fzc_lam_norm_R (hs : FzCSteps t L S x₁ x₂ lam rho) {x : G} (hx : x ∈ fzR t x₁ x₂) :
    lam * x * lam⁻¹ ∈ fzR t x₁ x₂ := by
  exact fzc_conj_mem_R hs (fzc_lam_mem_N hs) hx

private theorem fzc_rho_inv_norm_R (hs : FzCSteps t L S x₁ x₂ lam rho) {x : G}
    (hx : x ∈ fzR t x₁ x₂) : rho⁻¹ * x * rho ∈ fzR t x₁ x₂ := by
  have h3 : rho ^ 3 = 1 := fzc_rho_cube hs
  have h2 : rho ^ 2 = rho⁻¹ := by
    have h : rho ^ 2 * rho = 1 := by rw [← pow_succ, h3]
    exact eq_inv_of_mul_eq_one_left h
  have h2inv : (rho ^ 2)⁻¹ = rho := by
    have h : rho ^ 2 * rho = 1 := by rw [← pow_succ, h3]
    exact inv_eq_of_mul_eq_one_right h
  have heq : rho⁻¹ * x * rho = rho * (rho * x * rho⁻¹) * rho⁻¹ := by
    calc rho⁻¹ * x * rho = rho ^ 2 * x * rho := by rw [← h2]
      _ = rho ^ 2 * x * (rho ^ 2)⁻¹ := by rw [h2inv]
      _ = (rho * rho) * x * (rho * rho)⁻¹ := by rw [pow_two]
      _ = rho * (rho * x * rho⁻¹) * rho⁻¹ := by group
  rw [heq]
  exact fzc_rho_norm_R hs (fzc_rho_norm_R hs hx)

private theorem fzc_rho_mem_normalizer_R (hs : FzCSteps t L S x₁ x₂ lam rho) :
    rho ∈ Subgroup.normalizer ((fzR t x₁ x₂ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact fzc_rho_norm_R hs hh
  · intro hh
    have heq : h = rho⁻¹ * (rho * h * rho⁻¹) * rho := by group
    rw [heq]
    exact fzc_rho_inv_norm_R hs hh

private theorem fzc_comm_le_R (hs : FzCSteps t L S x₁ x₂ lam rho) :
    ⁅fzR t x₁ x₂, zpowers rho⁆ ≤ fzR t x₁ x₂ :=
  (Subgroup.le_normalizer_iff_commutator_le_left).mp
    (Subgroup.zpowers_le.mpr (fzc_rho_mem_normalizer_R hs))

theorem fzc_cent_R_rho (hs : FzCSteps t L S x₁ x₂ lam rho) :
    fzR t x₁ x₂ ⊓ centralizer ({rho} : Set G) = twoCore t := by
  apply le_antisymm
  · intro r hr
    have hcomm : rho * r = r * rho :=
      (Subgroup.mem_centralizer_singleton_iff.mp hr.2).symm
    obtain ⟨f, hf, hfeq⟩ := fzc_R_act_t hs hr.1
    have hconj : rho * (t * f) * rho⁻¹ = t * (rho * f * rho⁻¹) := by
      calc rho * (t * f) * rho⁻¹ = (rho * t * rho⁻¹) * (rho * f * rho⁻¹) := by group
        _ = t * (rho * f * rho⁻¹) := by rw [fzc_rho_cent_t hs]
    have hleft : rho * (t * f) * rho⁻¹ = t * f := by
      rw [← hfeq]
      have hrr : rho * r * rho⁻¹ = r := by rw [hcomm]; group
      have hri : rho * r⁻¹ * rho⁻¹ = r⁻¹ := by
        calc rho * r⁻¹ * rho⁻¹ = (rho * r * rho⁻¹)⁻¹ := by group
          _ = r⁻¹ := by rw [hrr]
      calc rho * (r * t * r⁻¹) * rho⁻¹
          = (rho * r * rho⁻¹) * (rho * t * rho⁻¹) * (rho * r⁻¹ * rho⁻¹) := by group
        _ = r * t * r⁻¹ := by rw [hrr, fzc_rho_cent_t hs, hri]
    have hf_eq : f = rho * f * rho⁻¹ := by
      exact mul_left_cancel (hleft.symm.trans hconj)
    have hf1 : f = 1 := fzc_rho_fpf_four hs hf hf_eq.symm
    have hrt : r * t * r⁻¹ = t := by rw [hfeq, hf1, mul_one]
    rw [← hs.ctx.cent_rho]
    refine ⟨?_, hr.2⟩
    have hmem : r ∈ fzR t x₁ x₂ ⊓ invCent t := by
      refine ⟨hr.1, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hrt)
    rwa [fzc_cent_R_t hs] at hmem
  · intro k hk
    have hk' : k ∈ ctxW t x₁ x₂ ⊓ centralizer ({rho} : Set G) := by
      rw [hs.ctx.cent_rho]; exact hk
    exact ⟨fzc_W_le_R hs hk'.1, hk'.2⟩

theorem fzc_R_eq_comm_W (hs : FzCSteps t L S x₁ x₂ lam rho) {r : G}
    (hr : r ∈ fzR t x₁ x₂) :
    ∃ c ∈ ⁅fzR t x₁ x₂, zpowers rho⁆, ∃ w ∈ ctxW t x₁ x₂, r = c * w := by
  obtain ⟨f, hf, hfeq⟩ := fzc_R_act_t hs hr
  obtain ⟨ζ, hζ, hζeq⟩ := fzc_exists_comm_four hs hf
  obtain ⟨r', hr', hr'eq⟩ := fzc_R_orbit_t hs hζ
  have haR : rho * r' * rho⁻¹ ∈ fzR t x₁ x₂ := fzc_rho_norm_R hs hr'
  have hr'ζ : r' * ζ = ζ * r' := fzc_R_cent_four hs hr' hζ
  have hrinv : r'⁻¹ * t * r' = t * ζ⁻¹ := by
    have hrt : r' * t = t * ζ * r' := by
      calc r' * t = r' * t * r'⁻¹ * r' := by group
        _ = (t * ζ) * r' := by rw [hr'eq]
    have h : r'⁻¹ * t * r' * ζ = t := by
      calc r'⁻¹ * t * r' * ζ = r'⁻¹ * (t * (r' * ζ)) := by group
        _ = r'⁻¹ * (t * (ζ * r')) := by rw [hr'ζ]
        _ = r'⁻¹ * (r' * t) := by rw [hrt]; group
        _ = t := by group
    calc r'⁻¹ * t * r' = r'⁻¹ * t * r' * ζ * ζ⁻¹ := by group
      _ = t * ζ⁻¹ := by rw [h]
  have hconj_a : (rho * r' * rho⁻¹) * t * (rho * r' * rho⁻¹)⁻¹ =
      t * (rho * ζ * rho⁻¹) := by
    have hrho_inv_t : rho⁻¹ * t * rho = t := by
      calc rho⁻¹ * t * rho = rho⁻¹ * (rho * t * rho⁻¹) * rho := by
            rw [fzc_rho_cent_t hs]
        _ = t := by group
    calc (rho * r' * rho⁻¹) * t * (rho * r' * rho⁻¹)⁻¹
        = rho * (r' * (rho⁻¹ * t * rho) * r'⁻¹) * rho⁻¹ := by group
      _ = rho * (r' * t * r'⁻¹) * rho⁻¹ := by rw [hrho_inv_t]
      _ = rho * (t * ζ) * rho⁻¹ := by rw [hr'eq]
      _ = (rho * t * rho⁻¹) * (rho * ζ * rho⁻¹) := by group
      _ = t * (rho * ζ * rho⁻¹) := by rw [fzc_rho_cent_t hs]
  have hζinv : ζ⁻¹ ∈ fourGrp x₁ x₂ := Subgroup.inv_mem _ hζ
  have hcent_zeta : (rho * r' * rho⁻¹) * ζ⁻¹ * (rho * r' * rho⁻¹)⁻¹ = ζ⁻¹ := by
    have hcz : (rho * r' * rho⁻¹) * ζ⁻¹ = ζ⁻¹ * (rho * r' * rho⁻¹) :=
      fzc_R_cent_four hs haR hζinv
    rw [hcz]; group
  have hc_act : (rho * r' * rho⁻¹ * r'⁻¹) * t * (rho * r' * rho⁻¹ * r'⁻¹)⁻¹ =
      t * f := by
    calc (rho * r' * rho⁻¹ * r'⁻¹) * t * (rho * r' * rho⁻¹ * r'⁻¹)⁻¹
        = (rho * r' * rho⁻¹) * (r'⁻¹ * t * r') * (rho * r' * rho⁻¹)⁻¹ := by group
      _ = (rho * r' * rho⁻¹) * (t * ζ⁻¹) * (rho * r' * rho⁻¹)⁻¹ := by rw [hrinv]
      _ = ((rho * r' * rho⁻¹) * t * (rho * r' * rho⁻¹)⁻¹) *
            ((rho * r' * rho⁻¹) * ζ⁻¹ * (rho * r' * rho⁻¹)⁻¹) := by group
      _ = (t * (rho * ζ * rho⁻¹)) * ζ⁻¹ := by rw [hconj_a, hcent_zeta]
      _ = t * f := by rw [mul_assoc, hζeq]
  have hc_comm : rho * r' * rho⁻¹ * r'⁻¹ ∈ ⁅fzR t x₁ x₂, zpowers rho⁆ := by
    have hmem : ⁅r', rho⁆ ∈ ⁅fzR t x₁ x₂, zpowers rho⁆ :=
      Subgroup.commutator_mem_commutator hr' (Subgroup.mem_zpowers rho)
    have heq : rho * r' * rho⁻¹ * r'⁻¹ = ⁅r', rho⁆⁻¹ := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact Subgroup.inv_mem _ hmem
  have hcR : rho * r' * rho⁻¹ * r'⁻¹ ∈ fzR t x₁ x₂ :=
    Subgroup.mul_mem _ haR (Subgroup.inv_mem _ hr')
  have hwW : (rho * r' * rho⁻¹ * r'⁻¹)⁻¹ * r ∈ ctxW t x₁ x₂ := by
    rw [← fzc_cent_R_t hs]
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hcR) hr, ?_⟩
    have hw_act : ((rho * r' * rho⁻¹ * r'⁻¹)⁻¹ * r) * t *
        ((rho * r' * rho⁻¹ * r'⁻¹)⁻¹ * r)⁻¹ = t := by
      calc ((rho * r' * rho⁻¹ * r'⁻¹)⁻¹ * r) * t *
            ((rho * r' * rho⁻¹ * r'⁻¹)⁻¹ * r)⁻¹
          = (rho * r' * rho⁻¹ * r'⁻¹)⁻¹ * (r * t * r⁻¹) *
              (rho * r' * rho⁻¹ * r'⁻¹) := by group
        _ = (rho * r' * rho⁻¹ * r'⁻¹)⁻¹ * (t * f) *
              (rho * r' * rho⁻¹ * r'⁻¹) := by rw [hfeq]
        _ = t := by rw [← hc_act]; group
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hw_act)
  exact ⟨rho * r' * rho⁻¹ * r'⁻¹, hc_comm, (rho * r' * rho⁻¹ * r'⁻¹)⁻¹ * r, hwW,
    by group⟩

theorem fzc_Q_eq (hs : FzCSteps t L S x₁ x₂ lam rho) : fzQ t x₁ x₂ rho = fzR t x₁ x₂ := by
  apply le_antisymm
  · rw [fzQ]
    exact sup_le (fzc_W_le_R hs) (fzc_comm_le_R hs)
  · intro r hr
    obtain ⟨c, hc, w, hw, rfl⟩ := fzc_R_eq_comm_W hs hr
    rw [fzQ]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hw)

theorem fzc_base_le_comm (hs : FzCSteps t L S x₁ x₂ lam rho) :
    baseGrp x₁ x₂ ≤ ⁅fzR t x₁ x₂, zpowers rho⁆ := by
  rw [← hs.ctx.comm_rho]
  exact Subgroup.commutator_mono (fzc_W_le_R hs) le_rfl

theorem fzc_R_eq_PK (hs : FzCSteps t L S x₁ x₂ lam rho) :
    fzR t x₁ x₂ = fzP t x₁ x₂ rho ⊔ twoCore t := by
  have hP : fzP t x₁ x₂ rho = ⁅fzR t x₁ x₂, zpowers rho⁆ := by
    rw [fzP, fzc_Q_eq hs]
  apply le_antisymm
  · intro r hr
    obtain ⟨c, hc, w, hw, rfl⟩ := fzc_R_eq_comm_W hs hr
    rw [hP]
    have hw' : w ∈ ⁅fzR t x₁ x₂, zpowers rho⁆ ⊔ twoCore t := by
      rw [ctxW] at hw
      exact sup_le le_sup_right ((fzc_base_le_comm hs).trans le_sup_left) hw
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) hw'
  · refine sup_le ?_ ?_
    · rw [hP]
      exact fzc_comm_le_R hs
    · exact (le_sup_left : twoCore t ≤ ctxW t x₁ x₂).trans (fzc_W_le_R hs)

end CFSG.OddStandard.SmallF3.FritzII
