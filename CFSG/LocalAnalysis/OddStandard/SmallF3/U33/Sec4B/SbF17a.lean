module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbD17Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC414Grp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARem

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l17_mem_O (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t ∈ ctxO t tau x₁ x₂ ∧ tau ∈ ctxO t tau x₁ x₂ ∧ om ∈ ctxO t tau x₁ x₂ := by
  have hCOle : ctxCO t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ := inf_le_left
  have ht : t ∈ ctxCO t tau x₁ x₂ rho := by
    rw [hc.CO_eq]; exact Subgroup.subset_closure (by simp)
  have hom : om ∈ ctxCO t tau x₁ x₂ rho := by
    rw [hc.CO_eq]; exact Subgroup.subset_closure (by simp)
  have htau : tau ∈ ctxCO t tau x₁ x₂ rho := by
    have h : tau ∈ ctxCO t tau x₁ x₂ rho ⊓
        centralizer (((ctxCO t tau x₁ x₂ rho : Subgroup G)) : Set G) := by
      rw [hc.CO_center]; exact Subgroup.mem_zpowers tau
    exact (Subgroup.mem_inf.mp h).1
  exact ⟨hCOle ht, hCOle htau, hCOle hom⟩

theorem l17_Q_le_O (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ := by
  have hQR : ctxQ t tau x₁ x₂ rho ≤ ctxR t tau x₁ x₂ := by
    rw [hc.R_eq]; exact le_sup_left
  exact hQR.trans hc.R_le_O

theorem l17_card_V (hc : Ctx13 t L S x₁ x₂ lam rho tau om) : Nat.card (fourGrp x₁ x₂) = 4 := by
  exact (hc.wreath.fourGrp_eq_omega).2.2

theorem l17_V_le_Y (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    fourGrp x₁ x₂ ≤ ctxYq t tau x₁ x₂ rho := by
  have hVQ : fourGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho :=
    hc.phi_Q.1.trans (Subgroup.map_subtype_le (frattini ↥(ctxQ t tau x₁ x₂ rho)))
  intro v hv
  rw [mem_ctxYq_iff hc.q_iso]
  exact ⟨hVQ hv, (hc.wreath.fourGrp_eq_omega).2.1.2 v hv⟩

theorem l17_Q_sq_mem (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ q ∈ ctxQ t tau x₁ x₂ rho, q ^ 2 ∈ fourGrp x₁ x₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥(ctxQ t tau x₁ x₂ rho)) :=
    ⟨IsPGroup.of_card (n := 6) (by rw [IsZ4Z4E4.card hc.q_iso]; norm_num)⟩
  intro q hq
  rw [← hc.phi_Q']
  exact Subgroup.mem_map.mpr
    ⟨(⟨q, hq⟩ : ↥(ctxQ t tau x₁ x₂ rho)) ^ 2,
      pth_power_mem_frattini_of_isPGroup (p := 2) _, rfl⟩

theorem l17_T_le_sylow (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    t ∈ 𝒮 ∧ tau ∈ 𝒮 ∧ om ∈ 𝒮 ∧ lam ∈ 𝒮 := by
  obtain ⟨htO, htauO, homO⟩ := l17_mem_O hc.toCtx13
  have hO : ctxO t tau x₁ x₂ ≤ ctxU t tau x₁ x₂ lam := le_sup_left
  have hlamU : lam ∈ ctxU t tau x₁ x₂ lam :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)
  exact ⟨hc.U_le (hO htO), hc.U_le (hO htauO), hc.U_le (hO homO), hc.U_le hlamU⟩

theorem l17_le_sylow (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxQ t tau x₁ x₂ rho ≤ 𝒮 ∧ ctxYq t tau x₁ x₂ rho ≤ 𝒮 ∧ S ≤ 𝒮 ∧ ctxR t tau x₁ x₂ ≤ 𝒮 := by
  have hQO : ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ := l17_Q_le_O hc.toCtx13
  have hOU : ctxO t tau x₁ x₂ ≤ ctxU t tau x₁ x₂ lam := le_sup_left
  have hQS : ctxQ t tau x₁ x₂ rho ≤ 𝒮 := hQO.trans (hOU.trans hc.U_le)
  exact ⟨hQS, ctxYq_le_ctxQ.trans hQS, hc.S_le_U.trans hc.U_le,
    hc.R_le_O.trans (hOU.trans hc.U_le)⟩

theorem l17_card_sylow (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) : Nat.card 𝒮 = 2 ^ 12 := by
  have hfac : (3 * 2 ^ 12).factorization 2 = 12 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3),
      Nat.factorization_pow_self Nat.prime_two]
  rw [card_eq_of_isSylowIn hc.sylow, hc.card_K, hfac]

theorem l17_mem_K (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t ∈ ctxK t tau x₁ x₂ rho ∧ tau ∈ ctxK t tau x₁ x₂ rho ∧ om ∈ ctxK t tau x₁ x₂ rho ∧
      lam ∈ ctxK t tau x₁ x₂ rho ∧ rho ∈ ctxK t tau x₁ x₂ rho := by
  obtain ⟨htO, htauO, homO⟩ := l17_mem_O hc
  have hOM : ctxO t tau x₁ x₂ ≤ ctxM t tau x₁ x₂ := by
    rw [hc.M_eq]; exact le_sup_left
  have hclM : closure ({rho, lam} : Set G) ≤ ctxM t tau x₁ x₂ := by
    rw [hc.M_eq]; exact le_sup_right
  exact ⟨hc.M_le_K (hOM htO), hc.M_le_K (hOM htauO), hc.M_le_K (hOM homO),
    hc.M_le_K (hclM (Subgroup.subset_closure (by simp))),
    hc.M_le_K (hclM (Subgroup.subset_closure (by simp)))⟩

theorem l17_K_normalizes_Y (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ k ∈ ctxK t tau x₁ x₂ rho, ∀ y ∈ ctxYq t tau x₁ x₂ rho,
      k * y * k⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  intro k hk y hy
  have hkY : k ∈ Subgroup.normalizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    hc.K_le.2.2 (hc.K_le.2.1 (hc.K_le.1 hk))
  exact (Subgroup.mem_normalizer_iff.mp hkY y).mp hy

theorem l17_tlam_conj (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∃ h : G, h * t * h⁻¹ = t * lam := by
  have hlamL : lam ∈ L := by
    have hW : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
    exact (Subgroup.mem_inf.mp (hc.inf_eq ▸ hW)).2
  have hlam2 : lam * lam = 1 := by
    have h := pow_orderOf_eq_one lam
    rw [hc.wreath.ord_lam] at h
    simpa [pow_two] using h
  have hlam_ne : lam ≠ 1 := by
    intro h
    have h2 : orderOf lam = orderOf (1 : G) := by rw [h]
    rw [hc.wreath.ord_lam, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨c, hcL, hcz⟩ := hc.invol_L lam hlamL hlam2 hlam_ne
  have hct : c * t * c⁻¹ = t := by
    have hcomm : c * t = t * c := S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp hcL)
    rw [hcomm]; group
  have htmem : t * (x₁ * x₂) ^ 2 ∈ conjIn (Subgroup.normalizer (S : Set G)) t := by
    rw [Ctx4.fusion_tz hc.toCtx11.toCtx10.toCtx4]
    exact ⟨(x₁ * x₂) ^ 2, Subgroup.mem_zpowers _, rfl⟩
  obtain ⟨n, _, hn⟩ := htmem
  refine ⟨c * n, ?_⟩
  calc (c * n) * t * (c * n)⁻¹ = c * (n * t * n⁻¹) * c⁻¹ := by group
    _ = c * (t * (x₁ * x₂) ^ 2) * c⁻¹ := by rw [hn]
    _ = (c * t * c⁻¹) * (c * (x₁ * x₂) ^ 2 * c⁻¹) := by group
    _ = t * lam := by rw [hct, hcz]

theorem l17_R_eq (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxR t tau x₁ x₂ = ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) := by
  rw [hc.R_eq]
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [ctxX, Subgroup.closure_le]
    rintro g (hg : g ∈ ({t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (hc.base_le_Q (pow_mem (Subgroup.subset_closure (by simp)) 2))
    · exact Subgroup.mem_sup_left (hc.base_le_Q
        (pow_mem (Subgroup.mul_mem _
          (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) 2))
  · refine sup_le le_sup_left ?_
    rw [Subgroup.closure_le]
    rintro g (hg : g ∈ ({t, tau} : Set G))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem l17_R_normalizes_Q (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ r ∈ ctxR t tau x₁ x₂, ∀ q ∈ ctxQ t tau x₁ x₂ rho, r * q * r⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
  intro r hr q hq
  exact hc.normal_Q.2 r
    (hc.R_le_O.trans (Subgroup.map_subtype_le (pCore 2 (ctxM t tau x₁ x₂))) hr) q hq

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
