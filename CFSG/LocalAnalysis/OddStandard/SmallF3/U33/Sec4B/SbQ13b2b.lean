module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem mem_zpowers_of_sq {z x : G} (hz : z * z = 1) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  by_cases hz1 : z = 1
  · left
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [hz1] at hk
    simpa using hk.symm
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hz2 : z ^ 2 = 1 := by simpa [pow_two] using hz
    have hord : orderOf z = 2 := orderOf_eq_prime (p := 2) hz2 hz1
    have h2 : (orderOf z : ℤ) = 2 := by rw [hord]; norm_num
    have hkm : z ^ (k % 2) = x := by
      have h' := zpow_mod_orderOf z k
      rw [h2] at h'
      exact h'.trans hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left; rw [h0, zpow_zero] at hkm; exact hkm.symm
    · right; rw [h1, zpow_one] at hkm; exact hkm.symm

theorem q13b_cent_V_le_O (h : Q13Om t L S x₁ x₂ lam rho tau om) {u : G}
    (hu : u ∈ ctxU t tau x₁ x₂ lam) (hc : ∀ v ∈ fourGrp x₁ x₂, u * v = v * u) :
    u ∈ ctxO t tau x₁ x₂ := by
  have hlamM : lam ∈ ctxM t tau x₁ x₂ := (q13a_mem_M h).2.2.2.1
  have hnorm : ∀ k ∈ zpowers lam, ∀ a ∈ ctxO t tau x₁ x₂, k * a * k⁻¹ ∈ ctxO t tau x₁ x₂ :=
    fun k hk a ha => (p0_normal_O t tau x₁ x₂).2 k (Subgroup.zpowers_le.mpr hlamM hk) a ha
  obtain ⟨o, ho, w, hw, how⟩ := (mem_sup_iff_of_normalizes hnorm).mp hu
  rcases mem_zpowers_of_sq (q13a_lam_mul_self h) hw with hw1 | hwl
  · rw [hw1, mul_one] at how
    exact how.symm ▸ ho
  · exfalso
    have hcent_u : u ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun v hv => (hc v hv).symm)
    have hOcent : ∀ o ∈ ctxO t tau x₁ x₂, ∀ v ∈ fourGrp x₁ x₂, o * v = v * o := by
      intro o ho v hv
      rw [c13_O_cent h.c11] at ho
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ho).2 v hv).symm
    have hcent_o : o ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun v hv => (hOcent o ho v hv).symm)
    have hcent_lam : lam ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      have hlam_eq : lam = o⁻¹ * u := by rw [how, hwl]; group
      rw [hlam_eq]
      exact mul_mem (inv_mem hcent_o) hcent_u
    have hx1V : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hcen : x₁ ^ 2 * lam = lam * x₁ ^ 2 :=
      Subgroup.mem_centralizer_iff.mp hcent_lam (x₁ ^ 2) hx1V
    have hlamx1 : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by rw [← hcen]; group
    have hconj : lam * x₁ ^ 2 * lam⁻¹ = x₂ ^ 2 := by
      rw [← conj_pow, h.c11.wreath.conj_x₁]
    have hx12eq : x₁ ^ 2 = x₂ ^ 2 := hlamx1.symm.trans hconj
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      have hx2sq : x₂ ^ 2 = x₁ ^ 2 * (x₁ * x₂) ^ 2 := WreathRel.x₂_sq h.c11.wreath
      have heq : x₁ ^ 2 = x₁ ^ 2 * (x₁ * x₂) ^ 2 := hx12eq.trans hx2sq
      have h1 : x₁ ^ 2 * 1 = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by simpa using heq
      exact (mul_left_cancel h1).symm
    exact WreathRel.sq_x₁x₂_ne_one h.c11.wreath hz1

theorem q13b_inv_sub_N (h : Q13Om t L S x₁ x₂ lam rho tau om) {K : Subgroup G}
    (hKN : K ≤ ctxN tau x₁ x₂) (hK : ∀ q ∈ ctxQ t tau x₁ x₂ rho, ∀ k ∈ K, q * k * q⁻¹ ∈ K) :
    K ≤ fourGrp x₁ x₂ ∨ ctxN tau x₁ x₂ ≤ K := by
  by_cases hKV : K ≤ fourGrp x₁ x₂
  · exact Or.inl hKV
  · right
    have hex : ∃ k ∈ K, k ∉ fourGrp x₁ x₂ := by
      by_contra hcon
      push_neg at hcon
      exact hKV hcon
    obtain ⟨k, hkK, hkV⟩ := hex
    have hkN : k ∈ ctxN tau x₁ x₂ := hKN hkK
    have htauk : tau * k ∈ fourGrp x₁ x₂ := by
      rcases l12_N_cases h.c11.toCtx10.toCtx4 hkN with h1 | h1
      · exact absurd h1 hkV
      · exact h1
    have htau2 : tau * tau = 1 := q13a_tau_mul_self h
    have hclaim : ∀ w ∈ fourGrp x₁ x₂, tau * w ∈ K := by
      intro w hw
      have hwv : w * (tau * k)⁻¹ ∈ fourGrp x₁ x₂ := mul_mem hw (inv_mem htauk)
      have hmem : tau * (w * (tau * k)⁻¹) ∈ tau • (fourGrp x₁ x₂ : Set G) := by
        rw [Set.mem_smul_set]
        exact ⟨w * (tau * k)⁻¹, hwv, rfl⟩
      rw [← q13a_tauQ h] at hmem
      obtain ⟨q, hq, hqeq⟩ := hmem
      have hconjv : q * (tau * k) * q⁻¹ = tau * k := by
        have hcv := q13a_V_central h (tau * k) htauk q hq
        rw [← hcv]; group
      have hqk : q * k * q⁻¹ = tau * w := by
        have hk_eq : k = tau * (tau * k) := by rw [← mul_assoc, htau2, one_mul]
        rw [hk_eq]
        calc q * (tau * (tau * k)) * q⁻¹
            = (q * tau * q⁻¹) * (q * (tau * k) * q⁻¹) := by group
          _ = (tau * (w * (tau * k)⁻¹)) * (tau * k) := by rw [hqeq, hconjv]
          _ = tau * w := by group
      rw [← hqk]
      exact hK q hq k hkK
    have htauK : tau ∈ K := by
      have h1 := hclaim 1 (one_mem _)
      simpa using h1
    have hVK : fourGrp x₁ x₂ ≤ K := by
      intro w hw
      have htw : tau * w ∈ K := hclaim w hw
      have h2 : tau * (tau * w) = w := by rw [← mul_assoc, htau2, one_mul]
      have h3 : tau * (tau * w) ∈ K := K.mul_mem htauK htw
      rwa [h2] at h3
    intro n hn
    rcases l12_N_cases h.c11.toCtx10.toCtx4 hn with hnv | htnv
    · exact hVK hnv
    · have htnK : tau * n ∈ K := hVK htnv
      have h2 : tau * (tau * n) = n := by rw [← mul_assoc, htau2, one_mul]
      have h3 : tau * (tau * n) ∈ K := K.mul_mem htauK htnK
      rwa [h2] at h3

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
