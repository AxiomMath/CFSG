module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbA17b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma zpowers_rho_normalizes_D8 (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ k ∈ zpowers rho, ∀ h ∈ closure ({t, om} : Set G),
      k * h * k⁻¹ ∈ closure ({t, om} : Set G) := by
  have hrho_cent : rho ∈ centralizer ((closure ({t, om} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact ((Subgroup.mem_centralizer_iff.mp ((ctx13_T_facts hc).1 hh)) rho rfl).symm
  have hle : zpowers rho ≤
      centralizer ((closure ({t, om} : Set G) : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hrho_cent
  intro k hk h hh
  have hcomm : h * k = k * h :=
    (Subgroup.mem_centralizer_iff.mp (hle hk)) h hh
  rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  exact hh

theorem l17_P_inf_zpowers_rho (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxP t tau x₁ x₂ rho ⊓ zpowers rho = ⊥ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxR⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hk⟩ := l17_P_pgroup hc ⟨x, hxP⟩
    have hx2 : x ^ 2 ^ k = 1 := by
      have hval := congrArg Subtype.val hk
      simpa using hval
    have hdvd2 : orderOf x ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hx2
    have hdvd3 : orderOf x ∣ 3 := by
      rw [← hc.ord_rho]
      exact orderOf_dvd_of_mem_zpowers hxR
    have hcop : Nat.Coprime 3 (2 ^ k) :=
      Nat.prime_two.coprime_pow_of_not_dvd (by norm_num)
    have h1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvd2
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  · exact bot_le

theorem l17_CP_rho (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ x ∈ ctxP t tau x₁ x₂ rho, x * rho = rho * x → x = 1 := by
  intro x hxP hxcomm
  have hxK : x ∈ ctxK t tau x₁ x₂ rho := (Subgroup.mem_inf.mp hxP).1
  have hxC : x ∈ centralizer ({rho} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hxcomm.symm
  have hxCK : x ∈ ctxK t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := ⟨hxK, hxC⟩
  rw [hc.CK_rho] at hxCK
  obtain ⟨d, hdD, r, hrR, hxdr⟩ :=
    (mem_sup_iff_of_normalizes (zpowers_rho_normalizes_D8 hc)).mp hxCK
  have hdC : d ∈ centralizer ({rho} : Set G) := (ctx13_T_facts hc).1 hdD
  have hdr : Commute d r := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hrR
    have hdrho : Commute d rho :=
      ((Subgroup.mem_centralizer_iff.mp hdC) rho rfl).symm
    rw [← hj]
    exact hdrho.zpow_right j
  have hd8 : d ^ 8 = 1 := by
    have h := pow_card_eq_one' (G := ↥(closure ({t, om} : Set G))) (x := ⟨d, hdD⟩)
    rw [(ctx13_T_facts hc).2.2] at h
    simpa using congrArg Subtype.val h
  have hx8 : x ^ 8 = r ^ 8 := by
    rw [hxdr, hdr.mul_pow 8, hd8, one_mul]
  have hr8mem : r ^ 8 ∈ ctxP t tau x₁ x₂ rho ⊓ zpowers rho := by
    refine ⟨?_, pow_mem hrR 8⟩
    rw [← hx8]
    exact pow_mem hxP 8
  have hr8 : r ^ 8 = 1 := by
    rw [l17_P_inf_zpowers_rho hc] at hr8mem
    exact Subgroup.mem_bot.mp hr8mem
  have hr_dvd3 : orderOf r ∣ 3 := by
    rw [← hc.ord_rho]
    exact orderOf_dvd_of_mem_zpowers hrR
  have hr_dvd8 : orderOf r ∣ 8 := orderOf_dvd_iff_pow_eq_one.mpr hr8
  have hr1 : r = 1 := by
    have h := Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 3 8) hr_dvd3 hr_dvd8
    exact orderOf_eq_one_iff.mp h
  have hxd : x = d := by rw [hxdr, hr1, mul_one]
  have hdP : d ∈ ctxP t tau x₁ x₂ rho := by rw [← hxd]; exact hxP
  have hdD8P : d ∈ closure ({t, om} : Set G) ⊓ ctxP t tau x₁ x₂ rho := ⟨hdD, hdP⟩
  rw [l17_D8_inf_P hc] at hdD8P
  have hd1 : d = 1 := Subgroup.mem_bot.mp hdD8P
  rw [hxd, hd1]

theorem l17_P_inf_N (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxP t tau x₁ x₂ rho ⊓
      (ctxK t tau x₁ x₂ rho ⊓ normalizer ((zpowers rho : Subgroup G) : Set G)) = ⊥ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxKN⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxK, hxN⟩ := Subgroup.mem_inf.mp hxKN
    have hmem : x * rho * x⁻¹ ∈ zpowers rho :=
      (Subgroup.mem_normalizer_iff.mp hxN rho).mp (Subgroup.mem_zpowers rho)
    have hcommmem : x * rho * x⁻¹ * rho⁻¹ ∈ zpowers rho :=
      Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.mem_zpowers rho))
    have hrhoK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc).2.2.2.2
    have hxinP : rho * x⁻¹ * rho⁻¹ ∈ ctxP t tau x₁ x₂ rho :=
      (l17_P_normal hc).2 rho hrhoK x⁻¹ (Subgroup.inv_mem _ hxP)
    have hcommP : x * rho * x⁻¹ * rho⁻¹ ∈ ctxP t tau x₁ x₂ rho := by
      simpa only [mul_assoc] using Subgroup.mul_mem _ hxP hxinP
    have hbot : x * rho * x⁻¹ * rho⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← l17_P_inf_zpowers_rho hc]
      exact ⟨hcommP, hcommmem⟩
    have hc1 : x * rho * x⁻¹ * rho⁻¹ = 1 := Subgroup.mem_bot.mp hbot
    have h1 : x * rho * x⁻¹ = rho := by
      calc x * rho * x⁻¹ = x * rho * x⁻¹ * rho⁻¹ * rho := by group
        _ = 1 * rho := by rw [hc1]
        _ = rho := by group
    have hxcomm : x * rho = rho * x := by
      calc x * rho = (x * rho * x⁻¹) * x := by group
        _ = rho * x := by rw [h1]
    exact Subgroup.mem_bot.mpr (l17_CP_rho hc x hxP hxcomm)
  · exact bot_le

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
