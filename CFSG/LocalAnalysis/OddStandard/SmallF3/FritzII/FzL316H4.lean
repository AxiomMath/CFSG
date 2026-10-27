module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H2b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35d

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma fzl_f_eq_one_of_mem_W {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4}
    (hF : FzF t x₁ x₂ f) {w : G} (hw : w ∈ fzN2 t x₁ x₂) (hwW : w ∈ ctxW t x₁ x₂) :
    f ⟨w, hw⟩ = 1 := by
  rw [← MonoidHom.mem_ker, hF.ker, Subgroup.mem_subgroupOf]
  exact hwW

private lemma fzl_baseGrp_le_L (h : Ctx t L S x₁ x₂ lam rho tau) :
    baseGrp x₁ x₂ ≤ L := by
  have h1 : baseGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := by
    rw [baseGrp, wreathGrp]
    exact Subgroup.closure_mono (by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      tauto)
  exact h1.trans (by rw [← h.inf_eq]; exact inf_le_right)

theorem fzl_f_rho (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) (hr : rho ∈ fzN2 t x₁ x₂) :
    f ⟨rho, hr⟩ ^ 3 = 1 ∧ f ⟨rho, hr⟩ ≠ 1 := by
  have hrho := fzl_rho_Z h
  constructor
  · have h3 : (⟨rho, hr⟩ : ↥(fzN2 t x₁ x₂)) ^ 3 = 1 := by
      ext
      simpa using hrho.2.2.1
    rw [← map_pow, h3, map_one]
  · intro h1
    have hrhoW : rho ∈ ctxW t x₁ x₂ := (fzl_W_mem_iff hF rho).2 ⟨hr, h1⟩
    have hzZ : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hzW : x₁ ^ 2 ∈ ctxW t x₁ x₂ := fzl_Z_le_W h hzZ
    haveI : IsMulCommutative (ctxW t x₁ x₂) := h.abelian_W
    have hcomm : rho * x₁ ^ 2 = x₁ ^ 2 * rho :=
      congrArg Subtype.val
        (mul_comm' (⟨rho, hrhoW⟩ : ctxW t x₁ x₂) ⟨x₁ ^ 2, hzW⟩)
    exact hrho.2.2.2 (x₁ ^ 2) hzZ (fzl_z1_ne_z2 h).2.1 (by rw [hcomm]; group)

theorem fzl_f_lam (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) (hr : rho ∈ fzN2 t x₁ x₂)
    (hl : lam ∈ fzN2 t x₁ x₂) :
    f ⟨lam, hl⟩ ^ 2 = 1 ∧ f ⟨lam, hl⟩ * f ⟨rho, hr⟩ * (f ⟨lam, hl⟩)⁻¹ = (f ⟨rho, hr⟩)⁻¹ := by
  have hlam := fzl_lam_Z h
  have hlr := fzl_lam_rho h
  constructor
  · have h2 : (⟨lam, hl⟩ : ↥(fzN2 t x₁ x₂)) ^ 2 = 1 := by
      ext
      simpa using hlam.2.2.1
    rw [← map_pow, h2, map_one]
  · have hkey : (⟨lam, hl⟩ : ↥(fzN2 t x₁ x₂)) * ⟨rho, hr⟩ * ⟨lam, hl⟩⁻¹ = ⟨rho, hr⟩⁻¹ := by
      ext
      simpa using hlr.1
    calc f ⟨lam, hl⟩ * f ⟨rho, hr⟩ * (f ⟨lam, hl⟩)⁻¹
        = f ((⟨lam, hl⟩ : ↥(fzN2 t x₁ x₂)) * ⟨rho, hr⟩ * ⟨lam, hl⟩⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = f (⟨rho, hr⟩⁻¹) := by rw [hkey]
      _ = (f ⟨rho, hr⟩)⁻¹ := map_inv f ⟨rho, hr⟩

theorem fzl_f_tau (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) (hr : rho ∈ fzN2 t x₁ x₂)
    (ht : tau ∈ fzN2 t x₁ x₂) : f ⟨tau, ht⟩ = fzlKappa := by
  have hfr := fzl_f_rho h hK hF hr
  have htau2W : tau ^ 2 ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_left h.tau_sq_mem
  have htau2N2 : tau ^ 2 ∈ fzN2 t x₁ x₂ :=
    (Subgroup.le_normalizer : ctxW t x₁ x₂ ≤ fzN2 t x₁ x₂) htau2W
  have hc2 : f ⟨tau, ht⟩ ^ 2 = 1 := by
    have h2 : (⟨tau, ht⟩ : ↥(fzN2 t x₁ x₂)) ^ 2 = ⟨tau ^ 2, htau2N2⟩ := by
      ext
      rfl
    rw [← map_pow, h2]
    exact fzl_f_eq_one_of_mem_W hF htau2N2 htau2W
  have hc1 : f ⟨tau, ht⟩ ≠ 1 := by
    intro h1
    have htauW : tau ∈ ctxW t x₁ x₂ := (fzl_W_mem_iff hF tau).2 ⟨ht, h1⟩
    have hWle : ctxW t x₁ x₂ ≤ twoCore t ⊔ L :=
      sup_le le_sup_left ((fzl_baseGrp_le_L h).trans le_sup_right)
    exact h.tau_not_mem (hWle htauW)
  have hca : f ⟨tau, ht⟩ * f ⟨rho, hr⟩ = f ⟨rho, hr⟩ * f ⟨tau, ht⟩ := by
    have h1 : (⟨tau, ht⟩ : ↥(fzN2 t x₁ x₂)) * ⟨rho, hr⟩ =
        ⟨rho, hr⟩ * ⟨tau, ht⟩ := by
      ext
      simpa using h.tau_rho
    calc f ⟨tau, ht⟩ * f ⟨rho, hr⟩
        = f ((⟨tau, ht⟩ : ↥(fzN2 t x₁ x₂)) * ⟨rho, hr⟩) := by rw [map_mul]
      _ = f (⟨rho, hr⟩ * ⟨tau, ht⟩) := by rw [h1]
      _ = f ⟨rho, hr⟩ * f ⟨tau, ht⟩ := by rw [map_mul]
  exact fzl_tau_image (f ⟨rho, hr⟩) (f ⟨tau, ht⟩) hfr.1 hfr.2 hc2 hc1 hca

end CFSG.OddStandard.SmallF3.FritzII
