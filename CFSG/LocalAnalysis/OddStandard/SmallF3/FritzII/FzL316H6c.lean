module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H6a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35g

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma fzl_conj_t_of_image_eq (h : Ctx t L S x₁ x₂ lam rho tau)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) {q : G}
    (hqN2 : q ∈ fzN2 t x₁ x₂) (c : ↥(fzN2 t x₁ x₂))
    (hct : (c : G) * t * (c : G)⁻¹ = t) (hfc : f ⟨q, hqN2⟩ = f c) : q * t * q⁻¹ = t := by
  have hcN2 : (c : G) ∈ fzN2 t x₁ x₂ := c.2
  have hwN2 : q * (c : G)⁻¹ ∈ fzN2 t x₁ x₂ :=
    (fzN2 t x₁ x₂).mul_mem hqN2 ((fzN2 t x₁ x₂).inv_mem hcN2)
  have hfw : f ⟨q * (c : G)⁻¹, hwN2⟩ = 1 := by
    have hsub : (⟨q * (c : G)⁻¹, hwN2⟩ : ↥(fzN2 t x₁ x₂)) = ⟨q, hqN2⟩ * c⁻¹ := by
      ext
      rfl
    rw [hsub, map_mul, map_inv, hfc]
    exact mul_inv_cancel (f c)
  have hwW : q * (c : G)⁻¹ ∈ ctxW t x₁ x₂ :=
    (fzl_W_mem_iff hF _).2 ⟨hwN2, hfw⟩
  have hwt : (q * (c : G)⁻¹) * t * (q * (c : G)⁻¹)⁻¹ = t := by
    have hcomm := (fzl_t_facts h).2.2.1 _ hwW
    calc (q * (c : G)⁻¹) * t * (q * (c : G)⁻¹)⁻¹
        = (t * (q * (c : G)⁻¹)) * (q * (c : G)⁻¹)⁻¹ := by rw [hcomm]
      _ = t := by group
  calc q * t * q⁻¹
      = (q * (c : G)⁻¹) * ((c : G) * t * (c : G)⁻¹) * (q * (c : G)⁻¹)⁻¹ := by group
    _ = (q * (c : G)⁻¹) * t * (q * (c : G)⁻¹)⁻¹ := by rw [hct]
    _ = t := hwt

theorem fzl_rho_QW (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    ∀ q ∈ fzQ t x₁ x₂ rho, rho * q * rho⁻¹ * q⁻¹ ∈ ctxW t x₁ x₂ → q ∈ ctxW t x₁ x₂ := by
  intro q hqQ hcomm
  obtain ⟨hqN2, hfqK4⟩ := (fzl_Q_mem_iff h hK hF q).mp hqQ
  have hrN2 : rho ∈ fzN2 t x₁ x₂ := (fzl_rho_Z h).1
  have hcommN2 : rho * q * rho⁻¹ * q⁻¹ ∈ fzN2 t x₁ x₂ :=
    (fzN2 t x₁ x₂).mul_mem
      ((fzN2 t x₁ x₂).mul_mem
        ((fzN2 t x₁ x₂).mul_mem hrN2 hqN2) ((fzN2 t x₁ x₂).inv_mem hrN2))
      ((fzN2 t x₁ x₂).inv_mem hqN2)
  have hf1 : f ⟨rho * q * rho⁻¹ * q⁻¹, hcommN2⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hF.ker, Subgroup.mem_subgroupOf]
    exact hcomm
  have harg : (⟨rho * q * rho⁻¹ * q⁻¹, hcommN2⟩ : ↥(fzN2 t x₁ x₂)) =
      (⟨rho, hrN2⟩ : ↥(fzN2 t x₁ x₂)) * ⟨q, hqN2⟩ * (⟨rho, hrN2⟩)⁻¹ * ⟨q, hqN2⟩⁻¹ := by
    ext
    rfl
  have hfprod : f ((⟨rho, hrN2⟩ : ↥(fzN2 t x₁ x₂)) * ⟨q, hqN2⟩ *
      (⟨rho, hrN2⟩)⁻¹ * ⟨q, hqN2⟩⁻¹) = 1 := by
    rw [← harg]
    exact hf1
  have hvfix : f ⟨rho, hrN2⟩ * f ⟨q, hqN2⟩ * (f ⟨rho, hrN2⟩)⁻¹ = f ⟨q, hqN2⟩ := by
    have h3 : (f ⟨rho, hrN2⟩ * f ⟨q, hqN2⟩ * (f ⟨rho, hrN2⟩)⁻¹) * (f ⟨q, hqN2⟩)⁻¹ = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hfprod
      exact hfprod
    exact mul_inv_eq_one.mp h3
  have hfr := fzl_f_rho h hK hF hrN2
  have hq1 : f ⟨q, hqN2⟩ = 1 :=
    fzl_K4_fpf (f ⟨rho, hrN2⟩) hfr.1 hfr.2 (f ⟨q, hqN2⟩) hfqK4 hvfix
  exact (fzl_W_mem_iff hF q).2 ⟨hqN2, hq1⟩

theorem fzl_rho_Q (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    ∀ q ∈ fzQ t x₁ x₂ rho, rho * q * rho⁻¹ = q → q = 1 ∨ q = t := by
  intro q hqQ hfix
  have hcommW : rho * q * rho⁻¹ * q⁻¹ ∈ ctxW t x₁ x₂ := by
    rw [hfix]
    simpa using (ctxW t x₁ x₂).one_mem
  have hqW : q ∈ ctxW t x₁ x₂ := fzl_rho_QW h hK hF q hqQ hcommW
  have hq_comm : rho * q = q * rho := mul_inv_eq_iff_eq_mul.mp hfix
  have hqC : q ∈ Subgroup.centralizer ({rho} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hq_comm.symm
  have hqP : q ∈ twoCore t := by
    have : q ∈ ctxW t x₁ x₂ ⊓ Subgroup.centralizer ({rho} : Set G) := ⟨hqW, hqC⟩
    rwa [h.cent_rho] at this
  exact fzl_twoCore_cases h hK q hqP

theorem fzl_Q_t (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    ∀ n ∈ fzQ t x₁ x₂ rho, n ∉ ctxW t x₁ x₂ → n * t * n⁻¹ ≠ t := by
  intro n hnQ hnW hnt
  obtain ⟨hnN2, hfnK4⟩ := (fzl_Q_mem_iff h hK hF n).mp hnQ
  have hfn1 : f ⟨n, hnN2⟩ ≠ 1 := fun h1 =>
    hnW ((fzl_W_mem_iff hF n).2 ⟨hnN2, h1⟩)
  have hrN2 : rho ∈ fzN2 t x₁ x₂ := (fzl_rho_Z h).1
  have hrt : rho * t * rho⁻¹ = t := (fzl_rho_Z h).2.1
  have hfr : f ⟨rho, hrN2⟩ ^ 3 = 1 ∧ f ⟨rho, hrN2⟩ ≠ 1 := fzl_f_rho h hK hF hrN2
  have hnpN2 : rho * n * rho⁻¹ ∈ fzN2 t x₁ x₂ :=
    (fzN2 t x₁ x₂).mul_mem ((fzN2 t x₁ x₂).mul_mem hrN2 hnN2)
      ((fzN2 t x₁ x₂).inv_mem hrN2)
  have hrt_inv : rho⁻¹ * t * rho = t := by
    have h := congrArg (fun x => rho⁻¹ * x * rho) hrt
    rw [show rho⁻¹ * (rho * t * rho⁻¹) * rho = t by group] at h
    exact h.symm
  have hnp_t : (rho * n * rho⁻¹) * t * (rho * n * rho⁻¹)⁻¹ = t := by
    calc (rho * n * rho⁻¹) * t * (rho * n * rho⁻¹)⁻¹
        = rho * (n * (rho⁻¹ * t * rho) * n⁻¹) * rho⁻¹ := by group
      _ = rho * (n * t * n⁻¹) * rho⁻¹ := by rw [hrt_inv]
      _ = rho * t * rho⁻¹ := by rw [hnt]
      _ = t := hrt
  have hnp_f : f ⟨rho * n * rho⁻¹, hnpN2⟩ =
      f ⟨rho, hrN2⟩ * f ⟨n, hnN2⟩ * (f ⟨rho, hrN2⟩)⁻¹ := by
    have hsub : (⟨rho * n * rho⁻¹, hnpN2⟩ : ↥(fzN2 t x₁ x₂)) =
        (⟨rho, hrN2⟩ : ↥(fzN2 t x₁ x₂)) * ⟨n, hnN2⟩ * (⟨rho, hrN2⟩)⁻¹ := by
      ext
      rfl
    rw [hsub, map_mul, map_mul, map_inv]
  have horbit := fzl_K4_orbit (f ⟨rho, hrN2⟩) hfr.1 hfr.2 (f ⟨n, hnN2⟩) hfnK4 hfn1
  have hcentral : ∀ q ∈ fzQ t x₁ x₂ rho, q * t * q⁻¹ = t := by
    intro q hqQ
    obtain ⟨hqN2, hfqK4⟩ := (fzl_Q_mem_iff h hK hF q).mp hqQ
    rcases horbit.2.2 (f ⟨q, hqN2⟩) hfqK4 with h1 | h1 | h1 | h1
    · have hqW : q ∈ ctxW t x₁ x₂ := (fzl_W_mem_iff hF q).2 ⟨hqN2, h1⟩
      have hcomm := (fzl_t_facts h).2.2.1 q hqW
      calc q * t * q⁻¹ = (t * q) * q⁻¹ := by rw [hcomm]
        _ = t := by group
    · exact fzl_conj_t_of_image_eq h hF hqN2 ⟨n, hnN2⟩ hnt h1
    · have hc3 : f ⟨q, hqN2⟩ = f (⟨rho * n * rho⁻¹, hnpN2⟩ : ↥(fzN2 t x₁ x₂)) := by
        rw [hnp_f]
        exact h1
      exact fzl_conj_t_of_image_eq h hF hqN2 ⟨rho * n * rho⁻¹, hnpN2⟩ hnp_t hc3
    · have hw4N2 : n * (rho * n * rho⁻¹) ∈ fzN2 t x₁ x₂ :=
        (fzN2 t x₁ x₂).mul_mem hnN2 hnpN2
      have hc4_t : (n * (rho * n * rho⁻¹)) * t * (n * (rho * n * rho⁻¹))⁻¹ = t := by
        calc n * (rho * n * rho⁻¹) * t * (n * (rho * n * rho⁻¹))⁻¹
            = n * ((rho * n * rho⁻¹) * t * (rho * n * rho⁻¹)⁻¹) * n⁻¹ := by group
          _ = n * t * n⁻¹ := by rw [hnp_t]
          _ = t := hnt
      have hc4_f : f ⟨q, hqN2⟩ = f ⟨n * (rho * n * rho⁻¹), hw4N2⟩ := by
        have hsub : (⟨n * (rho * n * rho⁻¹), hw4N2⟩ : ↥(fzN2 t x₁ x₂)) =
            (⟨n, hnN2⟩ : ↥(fzN2 t x₁ x₂)) * ⟨rho * n * rho⁻¹, hnpN2⟩ := by
          ext
          rfl
        rw [hsub, map_mul, hnp_f]
        exact h1
      exact fzl_conj_t_of_image_eq h hF hqN2 ⟨n * (rho * n * rho⁻¹), hw4N2⟩ hc4_t hc4_f
  have hQ_Z : ∀ q ∈ fzQ t x₁ x₂ rho, ∀ z ∈ fourGrp x₁ x₂, q * z * q⁻¹ = z := by
    intro q hqQ z hz
    obtain ⟨hqN2, hfqK4⟩ := (fzl_Q_mem_iff h hK hF q).mp hqQ
    exact fzl_R_Z h hK q
      ((fzl_R_mem_iff h hK hF q).mpr ⟨hqN2, fzl_K4_le_K8 hfqK4⟩) z hz
  have hn_sup : n ∈ ctxW t x₁ x₂ ⊔ zpowers tau :=
    fzl_ker_le h hK hnN2 hnt (hQ_Z n hnQ)
  have hle : zpowers tau ≤
      Subgroup.normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (fzl_tau_facts h hK).1
  have hn_mul : n ∈ (ctxW t x₁ x₂ : Set G) * (zpowers tau : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (ctxW t x₁ x₂) (zpowers tau) hle]
    exact hn_sup
  rw [Set.mem_mul] at hn_mul
  obtain ⟨w, hwW, z, hzτ, hwz⟩ := hn_mul
  have hwN2 : w ∈ fzN2 t x₁ x₂ := Subgroup.le_normalizer hwW
  have hzN2 : z ∈ fzN2 t x₁ x₂ :=
    Subgroup.zpowers_le.mpr (fzl_tau_facts h hK).1 hzτ
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hzτ
  have hw1 : f ⟨w, hwN2⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hF.ker, Subgroup.mem_subgroupOf]
    exact hwW
  have hfn : f ⟨n, hnN2⟩ = fzlKappa ^ i := by
    have hsub : (⟨n, hnN2⟩ : ↥(fzN2 t x₁ x₂)) =
        (⟨w, hwN2⟩ : ↥(fzN2 t x₁ x₂)) * ⟨z, hzN2⟩ := by
      ext
      exact hwz.symm
    have hz_tau : (⟨z, hzN2⟩ : ↥(fzN2 t x₁ x₂)) =
        (⟨tau, (fzl_tau_facts h hK).1⟩ : ↥(fzN2 t x₁ x₂)) ^ i := by
      ext
      exact hi.symm
    rw [hsub, map_mul, hw1, one_mul, hz_tau, map_zpow,
      fzl_f_tau h hK hF (fzl_rho_Z h).1 (fzl_tau_facts h hK).1]
    rfl
  have hki : fzlKappa ^ i = 1 ∨ fzlKappa ^ i = fzlKappa := by
    have hkappa_ne : fzlKappa ≠ 1 := fun hc => fzl_kappa_facts.2.1 (hc ▸ fzlK4.one_mem)
    have hord : orderOf fzlKappa = 2 := orderOf_eq_prime fzl_kappa_facts.2.2.1 hkappa_ne
    have hmod : fzlKappa ^ (i % (2 : ℤ)) = fzlKappa ^ i := by
      simpa [hord] using zpow_mod_orderOf fzlKappa i
    rcases Int.emod_two_eq_zero_or_one i with hi0 | hi1
    · left
      rw [← hmod, hi0, zpow_zero]
    · right
      rw [← hmod, hi1, zpow_one]
  rcases hki with hk1 | hkκ
  · exact hfn1 (hk1 ▸ hfn)
  · exact fzl_kappa_facts.2.1 (hkκ ▸ hfn ▸ hfnK4)

end CFSG.OddStandard.SmallF3.FritzII
