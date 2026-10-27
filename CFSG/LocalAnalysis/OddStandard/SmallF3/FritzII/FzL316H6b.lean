module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35e

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem fzl_Q_le_R (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    fzQ t x₁ x₂ rho ≤ fzR t x₁ x₂ := by
  intro g hg
  obtain ⟨hgN2, hfgK4⟩ := (fzl_Q_mem_iff h hK hF g).mp hg
  exact (fzl_R_mem_iff h hK hF g).mpr ⟨hgN2, fzl_K4_le_K8 hfgK4⟩

theorem fzl_Q_nrm (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    ∀ g ∈ fzN2 t x₁ x₂, ∀ q ∈ fzQ t x₁ x₂ rho, g * q * g⁻¹ ∈ fzQ t x₁ x₂ rho := by
  intro g hg q hq
  obtain ⟨hqN2, hfqK4⟩ := (fzl_Q_mem_iff h hK hF q).mp hq
  have hconjN2 : g * q * g⁻¹ ∈ fzN2 t x₁ x₂ :=
    (fzN2 t x₁ x₂).mul_mem ((fzN2 t x₁ x₂).mul_mem hg hqN2)
      ((fzN2 t x₁ x₂).inv_mem hg)
  refine (fzl_Q_mem_iff h hK hF (g * q * g⁻¹)).mpr ⟨hconjN2, ?_⟩
  have hsub : (⟨g * q * g⁻¹, hconjN2⟩ : ↥(fzN2 t x₁ x₂)) =
      (⟨g, hg⟩ : ↥(fzN2 t x₁ x₂)) * ⟨q, hqN2⟩ * (⟨g, hg⟩ : ↥(fzN2 t x₁ x₂))⁻¹ := by
    apply Subtype.ext
    rfl
  rw [hsub, map_mul, map_mul, map_inv]
  exact fzl_K4_normal.conj_mem (f ⟨q, hqN2⟩) hfqK4 (f ⟨g, hg⟩)

theorem fzl_tau_notin_Q (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    tau ∉ fzQ t x₁ x₂ rho := by
  intro htauQ
  obtain ⟨htauN2, hftauK4⟩ := (fzl_Q_mem_iff h hK hF tau).mp htauQ
  have hftau := fzl_f_tau h hK hF (fzl_rho_Z h).1 htauN2
  rw [hftau] at hftauK4
  exact fzl_kappa_facts.2.1 hftauK4

theorem fzl_tau_Q (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    ∀ q ∈ fzQ t x₁ x₂ rho, ⁅tau, q⁆ ∈ ctxW t x₁ x₂ := by
  intro q hq
  obtain ⟨hqN2, _⟩ := (fzl_Q_mem_iff h hK hF q).mp hq
  have htauN2 : tau ∈ fzN2 t x₁ x₂ := (fzl_tau_facts h hK).1
  have hrhoN2 : rho ∈ fzN2 t x₁ x₂ := (fzl_rho_Z h).1
  have hcommN2 : ⁅tau, q⁆ ∈ fzN2 t x₁ x₂ := by
    rw [commutatorElement_def]
    exact (fzN2 t x₁ x₂).mul_mem
      ((fzN2 t x₁ x₂).mul_mem ((fzN2 t x₁ x₂).mul_mem htauN2 hqN2)
        ((fzN2 t x₁ x₂).inv_mem htauN2))
      ((fzN2 t x₁ x₂).inv_mem hqN2)
  refine (fzl_W_mem_iff hF ⁅tau, q⁆).mpr ⟨hcommN2, ?_⟩
  have hsub : (⟨⁅tau, q⁆, hcommN2⟩ : ↥(fzN2 t x₁ x₂)) =
      ⁅(⟨tau, htauN2⟩ : ↥(fzN2 t x₁ x₂)), ⟨q, hqN2⟩⁆ := by
    apply Subtype.ext
    rfl
  rw [hsub, map_commutatorElement, fzl_f_tau h hK hF hrhoN2 htauN2]
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (fzl_kappa_facts.2.2.2 (f ⟨q, hqN2⟩)).symm

theorem fzl_lam_Q (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    ∃ n ∈ fzQ t x₁ x₂ rho, ⁅lam, n⁆ ∉ ctxW t x₁ x₂ := by
  have hrhoN2 : rho ∈ fzN2 t x₁ x₂ := (fzl_rho_Z h).1
  have hlamN2 : lam ∈ fzN2 t x₁ x₂ := (fzl_lam_Z h).1
  have hfr := fzl_f_rho h hK hF hrhoN2
  have hfl := fzl_f_lam h hK hF hrhoN2 hlamN2
  obtain ⟨v, hvK4, hvne⟩ := fzl_lam_image (f ⟨rho, hrhoN2⟩) (f ⟨lam, hlamN2⟩)
    hfr.1 hfr.2 hfl.1 hfl.2
  obtain ⟨n, hn⟩ := hF.surj v
  refine ⟨(n : G), ?_, ?_⟩
  · rw [fzl_Q_mem_iff h hK hF]
    exact ⟨n.2, show f n ∈ fzlK4 from by rw [hn]; exact hvK4⟩
  · intro hmem
    obtain ⟨hcommN2, hf1⟩ := (fzl_W_mem_iff hF ⁅lam, (n : G)⁆).mp hmem
    have hsub : (⟨⁅lam, (n : G)⁆, hcommN2⟩ : ↥(fzN2 t x₁ x₂)) =
        ⁅(⟨lam, hlamN2⟩ : ↥(fzN2 t x₁ x₂)), n⁆ := by
      apply Subtype.ext
      rfl
    rw [hsub, map_commutatorElement, hn, commutatorElement_def] at hf1
    exact hvne hf1

end CFSG.OddStandard.SmallF3.FritzII
