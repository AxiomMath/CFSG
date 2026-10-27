module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Spec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316P2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

variable {G : Type} [Group G]

theorem fzl_nrm_of_mem {P T : Subgroup G} (h : ∀ g ∈ T, ∀ p ∈ P, g * p * g⁻¹ ∈ P) {g : G}
    (hg : g ∈ T) : g ∈ normalizer (P : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h g hg x hx
  · intro hx
    have hg' : g⁻¹ ∈ T := T.inv_mem hg
    have hx' := h g⁻¹ hg' (g * x * g⁻¹) hx
    simpa [mul_assoc] using hx'

theorem fzl_rho_nrm {P : Subgroup G} {rho : G} (h : ∀ p ∈ P, rho * p * rho⁻¹ ∈ P)
    (h3 : rho ^ 3 = 1) : rho ∈ normalizer (P : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h x hx
  · intro hx
    have h1 : rho * (rho * x * rho⁻¹) * rho⁻¹ ∈ P := h _ hx
    have h2 : rho * (rho * (rho * x * rho⁻¹) * rho⁻¹) * rho⁻¹ ∈ P := h _ h1
    have heq : rho * (rho * (rho * x * rho⁻¹) * rho⁻¹) * rho⁻¹ = x := by
      have h3' : rho * rho * rho = 1 := by
        rw [show rho * rho * rho = rho ^ 3 by rw [pow_succ, pow_succ, pow_one]]
        exact h3
      calc rho * (rho * (rho * x * rho⁻¹) * rho⁻¹) * rho⁻¹
          = rho * rho * rho * x * (rho * rho * rho)⁻¹ := by
            simp only [mul_assoc, mul_inv_rev]
        _ = x := by rw [h3']; simp
    rwa [heq] at h2

private theorem fzl_conj_mem {P : Subgroup G} {g x : G} (hg : g ∈ normalizer (P : Set G))
    (hx : x ∈ P) : g * x * g⁻¹ ∈ P :=
  (Subgroup.mem_set_normalizer_iff.mp hg x).mp hx

private theorem fzl_conj_inv_mem {P : Subgroup G} {g x : G} (hg : g ∈ normalizer (P : Set G))
    (hx : x ∈ P) : g⁻¹ * x * g ∈ P :=
  by simpa only [inv_inv] using fzl_conj_mem (Subgroup.inv_mem _ hg) hx

noncomputable def fzConjAut {P : Subgroup G} (φ : ↥P ≃* FzUT) (g : G)
    (hg : g ∈ normalizer (P : Set G)) : MulAut FzUT where
  toFun x := φ ⟨g * ((φ.symm x : ↥P) : G) * g⁻¹, fzl_conj_mem hg (φ.symm x).2⟩
  invFun x := φ ⟨g⁻¹ * ((φ.symm x : ↥P) : G) * g, fzl_conj_inv_mem hg (φ.symm x).2⟩
  left_inv x := by
    apply φ.symm.injective
    simp only [MulEquiv.symm_apply_apply, Subtype.coe_mk]
    apply Subtype.ext
    simp only [Subtype.coe_mk]
    group
  right_inv x := by
    apply φ.symm.injective
    simp only [MulEquiv.symm_apply_apply, Subtype.coe_mk]
    apply Subtype.ext
    simp only [Subtype.coe_mk]
    group
  map_mul' x y := by
    apply φ.symm.injective
    rw [map_mul]
    simp only [MulEquiv.symm_apply_apply, Subtype.coe_mk]
    apply Subtype.ext
    simp only [Subtype.coe_mk, Subgroup.coe_mul, map_mul, MulEquiv.symm_apply_apply]
    group

theorem fzConjAut_coe {P : Subgroup G} (φ : ↥P ≃* FzUT) (g : G) (hg : g ∈ normalizer (P : Set G))
    (x : FzUT) :
    ((φ.symm ((fzConjAut φ g hg) x) : ↥P) : G) = g * ((φ.symm x : ↥P) : G) * g⁻¹ := by
  change ((φ.symm (φ ⟨g * ((φ.symm x : ↥P) : G) * g⁻¹,
      fzl_conj_mem hg (φ.symm x).2⟩) : ↥P) : G) = g * ((φ.symm x : ↥P) : G) * g⁻¹
  rw [MulEquiv.symm_apply_apply]

structure Fz319Data (t tau lam rho : G) (Z E W Q R T P : Subgroup G) where
  str : FzStr t tau lam rho Z E W Q R T
  pf : FzPFacts t tau rho E W Q T P
  φ : ↥P ≃* FzUT
  rho_conj : ∀ p : ↥P, φ ⟨rho * p * rho⁻¹, pf.nrm_P_rho p p.2⟩ = fzRho0 (φ p)

namespace Fz319Data

variable {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
  (D : Fz319Data t tau lam rho Z E W Q R T P)

include D

theorem t_mem : t ∈ T := D.str.RT (D.str.QR (D.str.WQ D.str.t_mem))

theorem tau_mem : tau ∈ T := D.str.RT D.str.tau_R

theorem lam_mem : lam ∈ T := D.str.lam_T

theorem nrm_of_mem {g : G} (hg : g ∈ T) : g ∈ normalizer (P : Set G) :=
  fzl_nrm_of_mem D.pf.nrm_P hg

theorem rho_nrm : rho ∈ normalizer (P : Set G) := fzl_rho_nrm D.pf.nrm_P_rho D.str.rho_ord

noncomputable def cT : MulAut FzUT := fzConjAut D.φ t (D.nrm_of_mem D.t_mem)

noncomputable def cS : MulAut FzUT := fzConjAut D.φ tau (D.nrm_of_mem D.tau_mem)

noncomputable def cL : MulAut FzUT := fzConjAut D.φ lam (D.nrm_of_mem D.lam_mem)

noncomputable def cR : MulAut FzUT := fzConjAut D.φ rho D.rho_nrm

theorem cT_coe (x : FzUT) :
    ((D.φ.symm ((D.cT) x) : ↥P) : G) = t * ((D.φ.symm x : ↥P) : G) * t⁻¹ :=
  fzConjAut_coe D.φ t _ x

theorem cS_coe (x : FzUT) :
    ((D.φ.symm ((D.cS) x) : ↥P) : G) = tau * ((D.φ.symm x : ↥P) : G) * tau⁻¹ :=
  fzConjAut_coe D.φ tau _ x

theorem cL_coe (x : FzUT) :
    ((D.φ.symm ((D.cL) x) : ↥P) : G) = lam * ((D.φ.symm x : ↥P) : G) * lam⁻¹ :=
  fzConjAut_coe D.φ lam _ x

theorem cR_coe (x : FzUT) :
    ((D.φ.symm ((D.cR) x) : ↥P) : G) = rho * ((D.φ.symm x : ↥P) : G) * rho⁻¹ :=
  fzConjAut_coe D.φ rho _ x

theorem cR_apply (x : FzUT) : (D.cR) x = fzRho0 x := by
  have h1 : (D.cR) x = D.φ ⟨rho * ((D.φ.symm x : ↥P) : G) * rho⁻¹,
      D.pf.nrm_P_rho (D.φ.symm x) (D.φ.symm x).2⟩ := by
    apply D.φ.symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply Subtype.ext
    rw [D.cR_coe]
  rw [h1, D.rho_conj (D.φ.symm x), D.φ.apply_symm_apply x]

end Fz319Data

end CFSG.OddStandard.SmallF3.FritzII
