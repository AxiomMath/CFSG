module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL47A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.M12ListA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.M12ListB2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem fourGrp_le_baseGrp (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [fourGrp]
  refine (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg
  · rw [hg]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
  · rw [hg]
    exact Subgroup.pow_mem _
      (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) 2

private theorem baseGrp_le_m12Grp (x₁ x₂ lam tau : G) :
    baseGrp x₁ x₂ ≤ m12Grp x₁ x₂ lam tau := by
  rw [baseGrp]
  refine (Subgroup.closure_le (K := m12Grp x₁ x₂ lam tau)).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg
  · rw [hg]
    exact Subgroup.subset_closure (by simp)
  · rw [hg]
    exact Subgroup.subset_closure (by simp)

private theorem fourGrp_le_m12Grp (x₁ x₂ lam tau : G) :
    fourGrp x₁ x₂ ≤ m12Grp x₁ x₂ lam tau :=
  le_trans (fourGrp_le_baseGrp x₁ x₂) (baseGrp_le_m12Grp x₁ x₂ lam tau)

private theorem zpowers_t_commute_S (h : Ctx t L S x₁ x₂ lam rho tau) {p : G}
    (hp : p ∈ zpowers t) {g : G} (hg : g ∈ S) : p * g = g * p := by
  have hc : Commute t g := (mem_invCent_iff.mp (h.le_invCent hg)).symm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  rw [← hk]
  exact hc.zpow_left k

private theorem baseGrp_le_centralizer_x₁_sq (h : Ctx t L S x₁ x₂ lam rho tau) :
    baseGrp x₁ x₂ ≤ centralizer ({x₁ ^ 2} : Set G) := by
  haveI : IsMulCommutative ↥(baseGrp x₁ x₂) := h.wreath.baseGrp_eq.1
  have hx₁sq : x₁ ^ 2 ∈ baseGrp x₁ x₂ :=
    Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : baseGrp x₁ x₂)
    (⟨x₁ ^ 2, hx₁sq⟩ : baseGrp x₁ x₂))

private theorem x₂_sq_ne_x₁_sq (h : Ctx t L S x₁ x₂ lam rho tau) : x₂ ^ 2 ≠ x₁ ^ 2 := by
  intro heq
  have hmem : x₂ ^ 2 ∈ zpowers x₁ ⊓ zpowers x₂ := by
    refine ⟨?_, npow_mem_zpowers x₂ 2⟩
    rw [heq]
    exact npow_mem_zpowers x₁ 2
  rw [h.wreath.inf_eq_bot, Subgroup.mem_bot] at hmem
  have hdvd : orderOf x₂ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hmem
  rw [h.wreath.ord_x₂] at hdvd
  norm_num at hdvd

private theorem lam_conj_x₁_sq (h : Ctx t L S x₁ x₂ lam rho tau) :
    lam * x₁ ^ 2 * lam⁻¹ = x₂ ^ 2 := by
  rw [← conj_pow (a := lam) (b := x₁) (i := 2), h.wreath.conj_x₁]

private theorem lam_not_mem_centralizer (h : Ctx t L S x₁ x₂ lam rho tau) :
    lam ∉ centralizer ({x₁ ^ 2} : Set G) := by
  intro hc
  have hx : lam * x₁ ^ 2 = x₁ ^ 2 * lam := Subgroup.mem_centralizer_singleton_iff.mp hc
  have h1 : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by
    rw [hx, mul_assoc, mul_inv_cancel, mul_one]
  have h2 := lam_conj_x₁_sq h
  exact x₂_sq_ne_x₁_sq h (h2 ▸ h1)

private theorem lam_tau_not_mem_centralizer (h : Ctx t L S x₁ x₂ lam rho tau) :
    lam * tau ∉ centralizer ({x₁ ^ 2} : Set G) := by
  intro hc
  have htauC : tau ∈ centralizer ({x₁ ^ 2} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (tau_commute_y h)
  have hlamC : lam ∈ centralizer ({x₁ ^ 2} : Set G) := by
    have hh := Subgroup.mul_mem (centralizer ({x₁ ^ 2} : Set G)) hc
      (Subgroup.inv_mem (centralizer ({x₁ ^ 2} : Set G)) htauC)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at hh
  exact lam_not_mem_centralizer h hlamC

theorem lemma4_7c_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) : Lemma4_7cConcl t S x₁ x₂ tau := by
  intro Y hY hy
  obtain ⟨hYS, hYea, hYcard⟩ := hY
  haveI : IsMulCommutative ↥Y := hYea.1
  have hYsq : ∀ x ∈ Y, x ^ 2 = 1 := hYea.2
  have htY : t ∈ Y := t_mem_of_isE16 h h43 h44 ⟨hYS, hYea, hYcard⟩
  have hzY : (x₁ * x₂) ^ 2 ∈ Y := z_mem_of_isE16 h h43 h44 ⟨hYS, hYea, hYcard⟩
  have hM : M12Rel x₁ x₂ lam tau := m12Rel_of_ctx h h44
  have hFA : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := fourGrp_le_baseGrp x₁ x₂
  have hFAM : fourGrp x₁ x₂ ≤ m12Grp x₁ x₂ lam tau := fourGrp_le_m12Grp x₁ x₂ lam tau
  have hAL : baseGrp x₁ x₂ ≤ L := by
    rw [baseGrp]
    refine (Subgroup.closure_le (K := L)).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact (generators_mem_L h.toCtx0).1
    · exact (generators_mem_L h.toCtx0).2.1
  have hYcent : Y ≤ centralizer ({x₁ ^ 2} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : Y) (⟨x₁ ^ 2, hy⟩ : Y))
  have hcentzp : centralizer ((zpowers (x₁ ^ 2) : Subgroup G) : Set G) =
      centralizer ({x₁ ^ 2} : Set G) := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_closure _
  have hSc : S ⊓ centralizer ({x₁ ^ 2} : Set G) =
      zpowers t ⊔ (baseGrp x₁ x₂ ⊔ zpowers tau) := by
    have hQ : zpowers (x₁ ^ 2) ≤ m12Grp x₁ x₂ lam tau := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
    have h1 := centralizer_S_inf h h43 h44 (Q := zpowers (x₁ ^ 2)) hQ
    rw [hcentzp, hM.centralizer_x₁_sq.1] at h1
    exact h1
  have hpart1 : Y ≤ zpowers t ⊔ (baseGrp x₁ x₂ ⊔ zpowers tau) := by
    rw [← hSc]
    exact le_inf hYS hYcent
  refine ⟨hpart1, ?_⟩
  let E : Subgroup G := closure ({t, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G)
  have hEeq : E = zpowers t ⊔ fourGrp x₁ x₂ := by
    refine le_antisymm ?_ ?_
    · rw [show E = closure ({t, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) from rfl]
      refine (Subgroup.closure_le (K := zpowers t ⊔ fourGrp x₁ x₂)).mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg | hg
      · rw [hg]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
      · rw [hg]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      · rw [hg]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
      · rw [fourGrp]
        refine (Subgroup.closure_le (K := E)).mpr ?_
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with hg | hg
        · rw [hg]
          exact Subgroup.subset_closure (by simp)
        · rw [hg]
          exact Subgroup.subset_closure (by simp)
  have hEcard : Nat.card E = 8 := by
    rw [hEeq]
    have hcomm : ∀ p ∈ zpowers t, ∀ f ∈ fourGrp x₁ x₂, p * f = f * p := by
      intro p hp f hf
      exact zpowers_t_commute_S h hp (m12Grp_le_S h (hFAM hf))
    have hinf : zpowers t ⊓ fourGrp x₁ x₂ = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨hxzt, hxF⟩ := Subgroup.mem_inf.mp hx
      have hx' : x ∈ zpowers t ⊓ m12Grp x₁ x₂ lam tau := ⟨hxzt, hFAM hxF⟩
      rw [(S_eq_prod_of h h43 h44).2] at hx'
      exact Subgroup.mem_bot.mp hx'
    rw [card_sup_of_commute hcomm hinf, Nat.card_zpowers, h.hyp.ord_t,
      (h.wreath.fourGrp_eq_omega).2.2]
  have hE_le_Y : E ≤ Y := by
    rw [show E = closure ({t, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) from rfl]
    refine (Subgroup.closure_le (K := Y)).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg
    · rw [hg]
      exact htY
    · rw [hg]
      exact hy
    · rw [hg]
      exact hzY
  have hE_ne_Y : E ≠ Y := by
    intro hEq
    have hcard : Nat.card E = Nat.card Y := by rw [hEq]
    rw [hEcard, hYcard] at hcard
    norm_num at hcard
  have hE_lt_Y : E < Y := lt_of_le_of_ne hE_le_Y hE_ne_Y
  have hssub : (E : Set G) ⊂ (Y : Set G) := SetLike.coe_ssubset_coe.mpr hE_lt_Y
  obtain ⟨w, hwY, hwE⟩ := Set.exists_of_ssubset hssub
  obtain ⟨w', hw'Y, hw'M, hw'E⟩ :
      ∃ w', w' ∈ Y ∧ w' ∈ m12Grp x₁ x₂ lam tau ∧ w' ∉ E := by
    rcases mem_m12Grp_or_mul h h43 h44 (hYS hwY) with hwM | htwM
    · exact ⟨w, hwY, hwM, hwE⟩
    · refine ⟨t * w, Y.mul_mem htY hwY, htwM, ?_⟩
      intro htwe
      apply hwE
      have hw_eq : w = t * (t * w) := by rw [← mul_assoc, t_mul_self h.hyp, one_mul]
      rw [hw_eq]
      exact E.mul_mem (Subgroup.subset_closure (by simp)) htwe
  have hw'C : w' ∈ centralizer ({x₁ ^ 2} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm' (⟨w', hw'Y⟩ : Y) (⟨x₁ ^ 2, hy⟩ : Y))
  have hw0C : ∀ a ∈ baseGrp x₁ x₂, a ∈ centralizer ({x₁ ^ 2} : Set G) :=
    fun a ha => baseGrp_le_centralizer_x₁_sq h ha
  obtain ⟨w₀, hw₀A, hcase⟩ := hM.coset_cases w' hw'M
  have hw'_eq : ∃ a ∈ baseGrp x₁ x₂, w' = a * tau := by
    rcases hcase with h1 | h1 | h1 | h1
    · exfalso
      apply hw'E
      have hw0sq : w₀ ^ 2 = 1 := by rw [← h1]; exact hYsq w' hw'Y
      have hw0F : w₀ ∈ fourGrp x₁ x₂ := by
        rw [(h.wreath.fourGrp_eq_omega).1]
        exact Subgroup.subset_closure ⟨hw₀A, hw0sq⟩
      rw [h1, hEeq]
      exact Subgroup.mem_sup_right hw0F
    · exact ⟨w₀, hw₀A, h1⟩
    · exfalso
      have hmem : lam ∈ centralizer ({x₁ ^ 2} : Set G) := by
        have hh := Subgroup.mul_mem (centralizer ({x₁ ^ 2} : Set G))
          (Subgroup.inv_mem (centralizer ({x₁ ^ 2} : Set G)) (hw0C w₀ hw₀A)) hw'C
        rw [h1] at hh
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at hh
      exact lam_not_mem_centralizer h hmem
    · exfalso
      have hmem : lam * tau ∈ centralizer ({x₁ ^ 2} : Set G) := by
        have hh := Subgroup.mul_mem (centralizer ({x₁ ^ 2} : Set G))
          (Subgroup.inv_mem (centralizer ({x₁ ^ 2} : Set G)) (hw0C w₀ hw₀A)) hw'C
        rw [h1] at hh
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at hh
      exact lam_tau_not_mem_centralizer h hmem
  obtain ⟨a, ha, hweq⟩ := hw'_eq
  have haτY : a * tau ∈ Y := hweq ▸ hw'Y
  let D : Subgroup G := closure ({t, x₁ ^ 2, (x₁ * x₂) ^ 2, a * tau} : Set G)
  have hED : E ≤ D := by
    rw [show E = closure ({t, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) from rfl,
      show D = closure ({t, x₁ ^ 2, (x₁ * x₂) ^ 2, a * tau} : Set G) from rfl]
    refine Subgroup.closure_mono ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    tauto
  have hDY : D ≤ Y := by
    rw [show D = closure ({t, x₁ ^ 2, (x₁ * x₂) ^ 2, a * tau} : Set G) from rfl]
    refine (Subgroup.closure_le (K := Y)).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg | hg
    · rw [hg]
      exact htY
    · rw [hg]
      exact hy
    · rw [hg]
      exact hzY
    · rw [hg]
      exact haτY
  have haτ_notE : a * tau ∉ E := by
    intro hmem
    rw [hEeq] at hmem
    have hcomm : ∀ p ∈ zpowers t, ∀ f ∈ fourGrp x₁ x₂, p * f = f * p := by
      intro p hp f hf
      exact zpowers_t_commute_S h hp (m12Grp_le_S h (hFAM hf))
    obtain ⟨p, hp, f, hf, hpf⟩ := (mem_sup_iff_of_commute hcomm).mp hmem
    have hpP : p ∈ twoCore t := by rw [h43]; exact hp
    have hfL : f ∈ L := hAL (hFA hf)
    have haL : a ∈ L := hAL ha
    have htau_eq : tau = a⁻¹ * p * f := by
      have h1 : tau = a⁻¹ * (a * tau) := by group
      rw [hpf, ← mul_assoc] at h1
      exact h1
    apply h.tau_not_mem
    rw [htau_eq]
    exact Subgroup.mul_mem (twoCore t ⊔ L)
      (Subgroup.mul_mem (twoCore t ⊔ L)
        (Subgroup.mem_sup_right (Subgroup.inv_mem L haL))
        (Subgroup.mem_sup_left hpP))
      (Subgroup.mem_sup_right hfL)
  have hED_ne : E ≠ D := by
    intro hEq
    have : a * tau ∈ E := by
      rw [hEq]
      exact Subgroup.subset_closure (by simp)
    exact haτ_notE this
  have hE_lt_D : E < D := lt_of_le_of_ne hED hED_ne
  have hD_eq_Y : D = Y := by
    by_contra hne
    have hDYlt : D < Y := lt_of_le_of_ne hDY hne
    have hgt : 8 < Nat.card D := by
      have hh := Subgroup.card_lt_of_lt hE_lt_D
      rwa [hEcard] at hh
    have hlt : Nat.card D < 16 := by
      have hh := Subgroup.card_lt_of_lt hDYlt
      rwa [hYcard] at hh
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hED
    rw [hEcard] at hm
    omega
  exact ⟨a, ha, haτY, hD_eq_Y.symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
