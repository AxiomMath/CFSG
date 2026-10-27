module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbA17e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC17

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma mul_eq_of_conj_eq {g w : G} (h : g * w * g⁻¹ = w) : g * w = w * g := by
  have := congrArg (fun y => y * g) h
  simpa [mul_assoc] using this

theorem l17_no_order_eight (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) {w : G}
    (hw : w ∈ ctxP t tau x₁ x₂ rho) (hw4 : w ^ 4 = (x₁ * x₂) ^ 2)
    (hg : (t * lam) * w * (t * lam)⁻¹ = w) : False := by
  obtain ⟨hg2, -, hgy, -⟩ := l17_g_facts hc.toCtx13
  obtain ⟨-, hVsq⟩ := l17_V_elem hc.toCtx13
  obtain ⟨-, hz_ne, -⟩ := l17_yz_ne hc.toCtx13
  have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hz2 : ((x₁ * x₂) ^ 2) ^ 2 = 1 := hVsq _ hzV
  have hw8 : w ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, hw4]
    exact hz2
  have hw8ord : orderOf w = 8 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnot : ¬ w ^ 2 ^ 2 = 1 := fun h => hz_ne (hw4 ▸ h)
    have hfin : w ^ 2 ^ (2 + 1) = 1 := by simpa using hw8
    have := orderOf_eq_prime_pow (p := 2) (n := 2) hnot hfin
    simpa using this
  obtain ⟨v₁, hv1Q, hv1sq, hv1notV, hgv1_conj⟩ := l17_v1 hc.toCtx13
  have hv1P : v₁ ∈ ctxP t tau x₁ x₂ rho := l17_Q_le_P hc.toCtx13 hv1Q
  have hv1_not_zp : v₁ ∉ zpowers w := by
    intro hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
    have h2 : w ^ (k * 2) = 1 := by
      rw [zpow_mul, hk]
      simpa using hv1sq
    have hdvd : (8 : ℤ) ∣ k * 2 := by
      have h := (orderOf_dvd_iff_zpow_eq_one (x := w) (i := k * 2)).mpr h2
      rwa [hw8ord] at h
    have h4dvd : (4 : ℤ) ∣ k := by
      have h' : ((4 : ℤ) * 2) ∣ k * 2 := by simpa using hdvd
      exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).mp h'
    obtain ⟨j, hj⟩ := h4dvd
    refine hv1notV ?_
    have hzpow : w ^ (4 : ℤ) = (x₁ * x₂) ^ 2 := by simpa using hw4
    have hv1z : v₁ = ((x₁ * x₂) ^ 2) ^ j := by
      rw [← hk, hj, zpow_mul, hzpow]
    rw [hv1z]
    exact Subgroup.zpow_mem _ hzV j
  have hcomm_wv1_gen : ∀ a ∈ zpowers w, ∀ b ∈ zpowers v₁, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hc1 : Commute w v₁ := (Subgroup.mem_centralizer_iff.mp hw.2 v₁ hv1Q).symm
    exact (hc1.zpow_zpow i j).eq
  have hcomm_wv1 : ∀ x ∈ zpowers w, x * v₁ = v₁ * x :=
    fun x hx => hcomm_wv1_gen x hx v₁ (Subgroup.mem_zpowers v₁)
  have hT1card : Nat.card ↥(zpowers w ⊔ zpowers v₁) = 16 := by
    have h := card_sup_zpowers_of_commute (T := zpowers w) (lam := v₁) hv1sq hv1_not_zp
      hcomm_wv1
    rw [Nat.card_zpowers, hw8ord] at h
    norm_num at h
    exact h
  have hT1_le_P : zpowers w ⊔ zpowers v₁ ≤ ctxP t tau x₁ x₂ rho :=
    sup_le (Subgroup.zpowers_le.mpr hw) (Subgroup.zpowers_le.mpr hv1P)
  have hg_not_P : t * lam ∉ ctxP t tau x₁ x₂ rho := by
    intro hgP
    have hgC : t * lam ∈ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := hgP.2
    have hx2Q : x₁ ^ 2 ∈ ctxQ t tau x₁ x₂ rho :=
      hc.base_le_Q (pow_mem (Subgroup.subset_closure (by simp)) 2)
    have hcomm : x₁ ^ 2 * (t * lam) = (t * lam) * x₁ ^ 2 :=
      Subgroup.mem_centralizer_iff.mp hgC _ hx2Q
    have hone : (t * lam) * x₁ ^ 2 * (t * lam)⁻¹ = x₁ ^ 2 := by
      rw [← hcomm]; group
    have heq : x₁ ^ 2 * (x₁ * x₂) ^ 2 = x₁ ^ 2 * 1 := by rw [← hgy, hone, mul_one]
    exact hz_ne (mul_left_cancel heq)
  have hg_not_T1 : t * lam ∉ zpowers w ⊔ zpowers v₁ := fun h => hg_not_P (hT1_le_P h)
  have hgw : w * (t * lam) = (t * lam) * w := (mul_eq_of_conj_eq hg).symm
  have hgv1 : v₁ * (t * lam) = (t * lam) * v₁ := (mul_eq_of_conj_eq hgv1_conj).symm
  have hcomm_g_T1 : ∀ x ∈ zpowers w ⊔ zpowers v₁, x * (t * lam) = (t * lam) * x := by
    have hle : zpowers w ⊔ zpowers v₁ ≤ centralizer ({(t * lam)} : Set G) := by
      refine sup_le ?_ ?_
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hgw)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hgv1)
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hg2' : (t * lam) ^ 2 = 1 := by rw [pow_two]; exact hg2
  have hBcard : Nat.card ↥((zpowers w ⊔ zpowers v₁) ⊔ zpowers (t * lam)) = 32 := by
    have h := card_sup_zpowers_of_commute (T := zpowers w ⊔ zpowers v₁) (lam := t * lam)
      hg2' hg_not_T1 hcomm_g_T1
    rw [hT1card] at h
    norm_num at h
    exact h
  have hT1_comm : IsMulCommutative ↥(zpowers w ⊔ zpowers v₁) :=
    isMulCommutative_sup_of_commute (P := zpowers w) (Q := zpowers v₁) hcomm_wv1_gen
      inferInstance inferInstance
  have hB_comm : IsMulCommutative ↥((zpowers w ⊔ zpowers v₁) ⊔ zpowers (t * lam)) := by
    refine isMulCommutative_sup_of_commute (P := zpowers w ⊔ zpowers v₁)
      (Q := zpowers (t * lam)) ?_ hT1_comm inferInstance
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hca : Commute a (t * lam) := hcomm_g_T1 a ha
    exact (hca.zpow_right k).eq
  obtain ⟨htS, -, -, hlamS⟩ := l17_T_le_sylow hc
  have hB_le_sylow : (zpowers w ⊔ zpowers v₁) ⊔ zpowers (t * lam) ≤ 𝒮 := by
    refine sup_le (hT1_le_P.trans (l17_P_le_sylow hc)) ?_
    exact Subgroup.zpowers_le.mpr (Subgroup.mul_mem 𝒮 htS hlamS)
  have hB_2 : IsPGroup 2 ↥((zpowers w ⊔ zpowers v₁) ⊔ zpowers (t * lam)) :=
    hc.sylow.2.1.to_le hB_le_sylow
  have hB_le_cent : ((zpowers w ⊔ zpowers v₁) ⊔ zpowers (t * lam)) ≤
      centralizer ({(t * lam)} : Set G) := by
    refine (Subgroup.le_centralizer_iff_isMulCommutative.mpr hB_comm).trans ?_
    exact Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  obtain ⟨h, hh⟩ := l17_tlam_conj hc.toCtx13
  have hAc : ((zpowers w ⊔ zpowers v₁) ⊔ zpowers (t * lam)) ≤
      centralizer ({(h * t * h⁻¹)} : Set G) := by
    rw [hh]
    exact hB_le_cent
  have hbound := c17_card_abelian_ord_eight_le (hc := hc.toCtx13.toCtx11.toCtx10) (g := h)
    hAc hB_comm hB_2 (w := w)
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers w))) hw8ord
  rw [hBcard] at hbound
  omega

theorem l17_exp_four (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ x ∈ ctxP t tau x₁ x₂ rho, x ^ 4 = 1 := by
  intro x hx
  by_contra hne
  obtain ⟨w, hwP, hw4, hgw⟩ := l17_exists_w hc ⟨x, hx, hne⟩
  exact l17_no_order_eight hc hwP hw4 hgw

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
