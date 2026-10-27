module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35e

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem fzl_R_comm (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    ∀ r ∈ fzR t x₁ x₂, ∀ r' ∈ fzR t x₁ x₂, ⁅r, r'⁆ ∈ ctxW t x₁ x₂ := by
  intro r hr r' hr'
  obtain ⟨hrN2, hfrK8⟩ := (fzl_R_mem_iff h hK hF r).mp hr
  obtain ⟨hr'N2, hfr'K8⟩ := (fzl_R_mem_iff h hK hF r').mp hr'
  have hcommN2 : ⁅r, r'⁆ ∈ fzN2 t x₁ x₂ := by
    rw [commutatorElement_def]
    exact (fzN2 t x₁ x₂).mul_mem
      ((fzN2 t x₁ x₂).mul_mem ((fzN2 t x₁ x₂).mul_mem hrN2 hr'N2)
        ((fzN2 t x₁ x₂).inv_mem hrN2))
      ((fzN2 t x₁ x₂).inv_mem hr'N2)
  refine (fzl_W_mem_iff hF ⁅r, r'⁆).mpr ⟨hcommN2, ?_⟩
  have hsub : (⟨⁅r, r'⁆, hcommN2⟩ : ↥(fzN2 t x₁ x₂)) =
      ⁅(⟨r, hrN2⟩ : ↥(fzN2 t x₁ x₂)), ⟨r', hr'N2⟩⁆ := by
    apply Subtype.ext
    rfl
  rw [hsub, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (fzl_K8_comm _ hfrK8 _ hfr'K8)

theorem fzl_R_sq (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    ∀ r ∈ fzR t x₁ x₂, r ^ 2 ∈ ctxW t x₁ x₂ := by
  intro r hr
  obtain ⟨hrN2, hfrK8⟩ := (fzl_R_mem_iff h hK hF r).mp hr
  have hsqN2 : r ^ 2 ∈ fzN2 t x₁ x₂ := (fzN2 t x₁ x₂).pow_mem hrN2 2
  refine (fzl_W_mem_iff hF (r ^ 2)).mpr ⟨hsqN2, ?_⟩
  have hsub : (⟨r ^ 2, hsqN2⟩ : ↥(fzN2 t x₁ x₂)) =
      (⟨r, hrN2⟩ : ↥(fzN2 t x₁ x₂)) ^ 2 := by
    apply Subtype.ext
    rfl
  rw [hsub, map_pow, fzl_K8_sq (f ⟨r, hrN2⟩) hfrK8]

theorem fzl_R_Z (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    ∀ r ∈ fzR t x₁ x₂, ∀ z ∈ fourGrp x₁ x₂, r * z * r⁻¹ = z := by
  refine fzl_cent_of_normal_two_group (R := fzR t x₁ x₂) (Z := fourGrp x₁ x₂)
    (rho := rho) (fzl_R_isPGroup t x₁ x₂) (fzl_rho_Z h).2.2.1 ?_ ?_ ?_ ?_
    (fzl_card_Z h) (fun z hz => fzl_Z_sq_eq_one h hz) (fzl_rho_Z h).2.2.2
  · intro r hr
    exact fzl_R_normal t x₁ x₂ rho (fzl_rho_Z h).1 r hr
  · intro z hz z' hz'
    exact congrArg Subtype.val (isMulCommutative_iff.mp h.abelian_W
      ⟨z, fzl_Z_le_W h hz⟩ ⟨z', fzl_Z_le_W h hz'⟩)
  · intro r hr z hz
    exact fzl_conj_Z h hK (fzl_R_le_N2 t x₁ x₂ hr) hz
  · intro z hz
    exact fzl_conj_Z h hK (fzl_rho_Z h).1 hz

theorem fzl_tau_R (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) : tau ∈ fzR t x₁ x₂ := by
  refine (fzl_R_mem_iff h hK hF tau).mpr ⟨(fzl_tau_facts h hK).1, ?_⟩
  rw [fzl_f_tau h hK hF (fzl_rho_Z h).1 (fzl_tau_facts h hK).1]
  exact fzl_kappa_facts.1

end CFSG.OddStandard.SmallF3.FritzII
