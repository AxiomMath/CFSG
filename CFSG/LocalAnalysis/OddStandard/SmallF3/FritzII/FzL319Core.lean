module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Triple
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319ShapeG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319CanonA

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fzl_319_of_data {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (D : Fz319Data t tau lam rho Z E W Q R T P) (hC : FzClassSpecA) (hnc : ¬ FzCanon T W)
    {x₁ x₂ : G} (hx₁ : x₁ ∈ E) (hx₂ : x₂ ∈ E) (hE : E = closure {x₁, x₂})
    (hl : lam * x₁ * lam⁻¹ = x₂) :
    ∃ a₁₂ a₂₂ a₃₂ : G, FzSpShape t x₁ x₂ lam T a₁₂ a₂₂ a₃₂ := by
  rcases hC D.cT D.cS D.cL D.validTriple with h | h
  · exact D.shape_sp hx₁ hx₂ hl (h (D.φ ⟨x₁, D.pf.EP hx₁⟩) (D.validX hx₁ hx₂ hE hl))
  · exact absurd (D.canon_of_autW h) hnc

theorem fzl_319_of_str {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) {P : Subgroup G} (hPd : P = ⁅Q, zpowers rho⁆)
    (hTN : T ≤ normalizer (W : Set G)) (hodd : ¬ 2 ∣ T.relIndex (normalizer (W : Set G)))
    (hns : ¬ FzSylow T) (φ₀ : ↥P ≃* SylSL3_4) (hN : FzNormSpec) (hC : FzClassSpecA)
    {x₁ x₂ : G} (hx₁ : x₁ ∈ E) (hx₂ : x₂ ∈ E) (hE : E = closure {x₁, x₂})
    (hl : lam * x₁ * lam⁻¹ = x₂) :
    ∃ a₁₂ a₂₂ a₃₂ : G, FzSpShape t x₁ x₂ lam T a₁₂ a₂₂ a₃₂ := by
  have hnc : ¬ FzCanon T W := fun hc => hns (fzl_sylow_of_canon hTN h.pgroup_T hodd hc)
  have htP : t ∉ P := fun ht =>
    hnc (fzl_canon_of_phiQ h (fzl_phiQ_eq_W h (hPd ▸ ht)))
  have hPf := fzl_pfacts h hPd htP
  let φ₁ : ↥P ≃* FzUT := φ₀.trans L23.sylLCongr
  let hρn : rho ∈ normalizer (P : Set G) := fzl_rho_nrm hPf.nrm_P_rho h.rho_ord
  let rhoBar : MulAut FzUT := fzConjAut φ₁ rho hρn
  have hrhoBar_coe : ∀ y : FzUT,
      ((φ₁.symm (rhoBar y) : ↥P) : G) = rho * ((φ₁.symm y : ↥P) : G) * rho⁻¹ :=
    fun y => fzConjAut_coe φ₁ rho hρn y
  have hrhoBar : ∀ y : FzUT, rhoBar y = φ₁ ⟨rho * ((φ₁.symm y : ↥P) : G) * rho⁻¹,
      hPf.nrm_P_rho (φ₁.symm y) (φ₁.symm y).2⟩ := by
    intro y
    apply φ₁.symm.injective
    apply Subtype.ext
    simp only [MulEquiv.symm_apply_apply]
    exact hrhoBar_coe y
  have h3 : ∀ x, rhoBar (rhoBar (rhoBar x)) = x := by
    intro x
    apply φ₁.symm.injective
    apply Subtype.ext
    rw [hrhoBar_coe (rhoBar (rhoBar x)), hrhoBar_coe (rhoBar x), hrhoBar_coe x]
    have hr3 : rho * rho * rho = 1 := by rw [← pow_three', h.rho_ord]
    calc rho * (rho * (rho * ((φ₁.symm x : ↥P) : G) * rho⁻¹) * rho⁻¹) * rho⁻¹
        = (rho * rho * rho) * ((φ₁.symm x : ↥P) : G) * (rho * rho * rho)⁻¹ := by group
      _ = ((φ₁.symm x : ↥P) : G) := by rw [hr3]; group
  have hfpf : ∀ x, x ≠ 1 → rhoBar x ≠ x := by
    intro x hx1 hfix
    apply hx1
    have hp : ((φ₁.symm x : ↥P) : G) = 1 := by
      apply hPf.rho_fpf _ (φ₁.symm x).2
      have h2 : ((φ₁.symm (rhoBar x) : ↥P) : G) = ((φ₁.symm x : ↥P) : G) := by rw [hfix]
      rw [hrhoBar_coe x] at h2
      exact h2
    have hp1 : φ₁.symm x = 1 := Subtype.ext hp
    have hx : x = 1 := by
      have hc := congrArg φ₁ hp1
      simpa using hc
    exact hx
  obtain ⟨β, hβ⟩ := hN rhoBar h3 hfpf
  let φ : ↥P ≃* FzUT := φ₁.trans β
  have rho_conj : ∀ p : ↥P, φ ⟨rho * p * rho⁻¹, hPf.nrm_P_rho p p.2⟩ = fzRho0 (φ p) := by
    intro p
    have hp : φ₁ ⟨rho * p * rho⁻¹, hPf.nrm_P_rho p p.2⟩ = rhoBar (φ₁ p) := by
      have hh := hrhoBar (φ₁ p)
      rw [show (φ₁.symm (φ₁ p) : ↥P) = p from MulEquiv.symm_apply_apply φ₁ p] at hh
      exact hh.symm
    change β (φ₁ ⟨rho * p * rho⁻¹, hPf.nrm_P_rho p p.2⟩) = fzRho0 (β (φ₁ p))
    rw [hp]
    exact hβ (φ₁ p)
  let D : Fz319Data t tau lam rho Z E W Q R T P :=
    { str := h, pf := hPf, φ := φ, rho_conj := rho_conj }
  exact fzl_319_of_data D hC hnc hx₁ hx₂ hE hl

end CFSG.OddStandard.SmallF3.FritzII
