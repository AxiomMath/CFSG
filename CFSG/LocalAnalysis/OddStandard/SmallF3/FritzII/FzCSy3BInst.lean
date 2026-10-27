module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrDef

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho q : G}

private theorem fzc_sy3_c_conj_t (h : Ctx0 t L S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hqt : q ^ 2 = t) :
    q * lam * t * (q * lam)⁻¹ = t := by
  have hq : q * t * q⁻¹ = t := by
    rw [← hqt]
    simp only [pow_two]
    group
  have hl : lam * t * lam⁻¹ = t := by
    rw [fzc_sy3_lam_t h hK hqt]
    group
  calc q * lam * t * (q * lam)⁻¹ = q * (lam * t * lam⁻¹) * q⁻¹ := by group
    _ = q * t * q⁻¹ := by rw [hl]
    _ = t := hq

private theorem fzc_sy3_c_sq (h : Ctx0 t L S x₁ x₂ lam rho) (hK : twoCore t = zpowers q)
    (hqt : q ^ 2 = t) : (q * lam) ^ 2 = t := by
  rw [pow_two]
  have hql := fzc_sy3_q_lam h hK
  have hl := fzc_sy3_lam_sq h
  calc (q * lam) * (q * lam) = q * (lam * q) * lam := by group
    _ = q * (q * lam) * lam := by rw [← hql]
    _ = q * q * (lam * lam) := by group
    _ = q ^ 2 * (lam * lam) := by rw [pow_two]
    _ = q ^ 2 * 1 := by rw [hl]
    _ = t := by rw [hqt, mul_one]

private theorem fzc_sy3_c_conj_E (h : Ctx0 t L S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) :
    ∀ e ∈ baseGrp x₁ x₂, q * lam * e * (q * lam)⁻¹ ∈ baseGrp x₁ x₂ := by
  intro e he
  have hle : lam * e * lam⁻¹ ∈ baseGrp x₁ x₂ := fzc_sy3_lam_E h e he
  have hqe : q * (lam * e * lam⁻¹) * q⁻¹ = lam * e * lam⁻¹ := by
    rw [fzc_sy3_q_comm_W h hK _ (Subgroup.mem_sup_right hle)]
    group
  have heq : q * lam * e * (q * lam)⁻¹ = lam * e * lam⁻¹ := by
    calc q * lam * e * (q * lam)⁻¹ = q * (lam * e * lam⁻¹) * q⁻¹ := by group
      _ = lam * e * lam⁻¹ := hqe
  rw [heq]
  exact hle

private theorem fzc_sy3_c_x₁ (h : Ctx0 t L S x₁ x₂ lam rho) (hK : twoCore t = zpowers q) :
    q * lam * x₁ * (q * lam)⁻¹ = x₂ := by
  have hqx₂ : q * x₂ * q⁻¹ = x₂ := by
    rw [fzc_sy3_q_comm_W h hK x₂
      (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))]
    group
  calc q * lam * x₁ * (q * lam)⁻¹ = q * (lam * x₁ * lam⁻¹) * q⁻¹ := by group
    _ = q * x₂ * q⁻¹ := by rw [h.wreath.conj_x₁]
    _ = x₂ := hqx₂

private theorem fzc_sy3_c_x₂ (h : Ctx0 t L S x₁ x₂ lam rho) (hK : twoCore t = zpowers q) :
    q * lam * x₂ * (q * lam)⁻¹ = x₁ := by
  have hqx₁ : q * x₁ * q⁻¹ = x₁ := by
    rw [fzc_sy3_q_comm_W h hK x₁
      (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))]
    group
  calc q * lam * x₂ * (q * lam)⁻¹ = q * (lam * x₂ * lam⁻¹) * q⁻¹ := by group
    _ = q * x₁ * q⁻¹ := by rw [fzc_sy3_lam_x₂ h]
    _ = x₁ := hqx₁

private theorem fzc_sy3_P_t' (h : Ctx0 t L S x₁ x₂ lam rho)
    (hq : FzCQFacts t S x₁ x₂ lam rho) (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4)
    (hqt : q ^ 2 = t) (ht : t ∈ fzP t x₁ x₂ rho) :
    ∀ p ∈ fzP t x₁ x₂ rho, p * t * p⁻¹ * t ∈ fourGrp x₁ x₂ := by
  intro p hp
  obtain ⟨f, hfZ, hpt⟩ := hq.R_act_t p (fzc_sy3_P_le_R hq hp)
  have hfE : f ∈ baseGrp x₁ x₂ := S4A.pt_four_le_base x₁ x₂ hfZ
  have hft : t * f = f * t := S4A.pt_comm_base h t h.hyp.mem_twoCore f hfE
  have htt : t * t = 1 := by rw [← pow_two]; exact fzc_sy2_t_sq h
  have hftt : t * f * t = f := by
    calc t * f * t = (t * f) * t := by group
      _ = (f * t) * t := by rw [hft]
      _ = f * (t * t) := by group
      _ = f := by rw [htt, mul_one]
  rw [hpt, hftt]
  exact hfZ

private theorem fzc_sy3_U_nrm_E (h : Ctx0 t L S x₁ x₂ lam rho)
    (hq : FzCQFacts t S x₁ x₂ lam rho) (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4)
    (hqt : q ^ 2 = t) (ht : t ∈ fzP t x₁ x₂ rho) :
    ∀ u ∈ fzP t x₁ x₂ rho ⊔ zpowers (q * lam), ∀ e ∈ baseGrp x₁ x₂,
      u * e * u⁻¹ ∈ baseGrp x₁ x₂ := by
  intro u hu e he
  have hcE := fzc_sy3_c_conj_E h hK e he
  rcases fzc_sy3_U_cos h hq hK hqt ht u hu with huP | huP
  · exact fzc_sy3_R_nrm_E h hq hK hq4 hqt u (fzc_sy3_P_le_R hq huP) e he
  · obtain ⟨p, hp, rfl⟩ : ∃ p ∈ fzP t x₁ x₂ rho, u = p * (q * lam) :=
      ⟨u * (q * lam)⁻¹, huP, by group⟩
    have heq : p * (q * lam) * e * (p * (q * lam))⁻¹ =
        p * ((q * lam) * e * (q * lam)⁻¹) * p⁻¹ := by group
    rw [heq]
    exact fzc_sy3_R_nrm_E h hq hK hq4 hqt p (fzc_sy3_P_le_R hq hp) _ hcE

private theorem fzc_sy3_U_conj_t (h : Ctx0 t L S x₁ x₂ lam rho)
    (hq : FzCQFacts t S x₁ x₂ lam rho) (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4)
    (hqt : q ^ 2 = t) (ht : t ∈ fzP t x₁ x₂ rho) :
    ∀ u ∈ fzP t x₁ x₂ rho ⊔ zpowers (q * lam), u * t * u⁻¹ * t ∈ baseGrp x₁ x₂ := by
  intro u hu
  have hct : q * lam * t * (q * lam)⁻¹ = t := fzc_sy3_c_conj_t h hK hqt
  rcases fzc_sy3_U_cos h hq hK hqt ht u hu with huP | huP
  · exact S4A.pt_four_le_base x₁ x₂ (fzc_sy3_P_t' h hq hK hq4 hqt ht u huP)
  · obtain ⟨p, hp, rfl⟩ : ∃ p ∈ fzP t x₁ x₂ rho, u = p * (q * lam) :=
      ⟨u * (q * lam)⁻¹, huP, by group⟩
    have heq : p * (q * lam) * t * (p * (q * lam))⁻¹ * t = p * t * p⁻¹ * t := by
      calc p * (q * lam) * t * (p * (q * lam))⁻¹ * t
          = p * ((q * lam) * t * (q * lam)⁻¹) * p⁻¹ * t := by group
        _ = p * t * p⁻¹ * t := by rw [hct]
    rw [heq]
    exact S4A.pt_four_le_base x₁ x₂ (fzc_sy3_P_t' h hq hK hq4 hqt ht p hp)

theorem fzc_sy3_str (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    FzCSy3bStr x₁ x₂ t a (rho * a * rho⁻¹) (q * lam) (baseGrp x₁ x₂ ⊔ zpowers t)
      ((baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a) (fzP t x₁ x₂ rho)
      (((baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a) ⊔ zpowers (q * lam))
      (((baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a) ⊔ zpowers (rho * a * rho⁻¹ * (q * lam)))
      (fzP t x₁ x₂ rho ⊔ zpowers (q * lam)) := by
  have hbP : rho * a * rho⁻¹ ∈ fzP t x₁ x₂ rho := hq.rho_norm_P a ha
  have hbNotin := fzc_sy3_b_notin h hq hK hq4 hqt ht ha hat
  have hbW : rho * a * rho⁻¹ ∉ baseGrp x₁ x₂ ⊔ zpowers t := fun h' =>
    hbNotin (Subgroup.mem_sup_left h')
  have habP : a * (rho * a * rho⁻¹) ∈ fzP t x₁ x₂ rho :=
    (fzP t x₁ x₂ rho).mul_mem ha hbP
  have habW : a * (rho * a * rho⁻¹) ∉ baseGrp x₁ x₂ ⊔ zpowers t := by
    intro h'
    apply hbNotin
    have e : rho * a * rho⁻¹ = a⁻¹ * (a * (rho * a * rho⁻¹)) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right
      ((Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers a)))
      (Subgroup.mem_sup_left h')
  have hcNotin : q * lam ∉ fzP t x₁ x₂ rho := by
    intro hc
    have hqR : q ∈ fzR t x₁ x₂ := hq.W_le_R (fzc_sy3_q_mem_W hK)
    have hlamR : lam ∈ fzR t x₁ x₂ := by
      have e : lam = q⁻¹ * (q * lam) := by group
      rw [e]
      exact (fzR t x₁ x₂).mul_mem ((fzR t x₁ x₂).inv_mem hqR)
        (fzc_sy3_P_le_R hq hc)
    exact hq.lam_not_mem_R hlamR
  obtain ⟨hsp1, hsp2, hsp3⟩ := fzc_sy3_sp h hq hK hq4 hqt ht ha hat
  refine { comm := h.wreath.comm
           ord₁ := h.wreath.ord_x₁
           ord₂ := h.wreath.ord_x₂
           inf := h.wreath.inf_eq_bot
           t_sq := fzc_sy2_t_sq h
           t_notin := fzc_sy2_t_notin_E h
           t_comm₁ := S4A.pt_comm_base h t h.hyp.mem_twoCore x₁
             (Subgroup.subset_closure (by simp))
           t_comm₂ := S4A.pt_comm_base h t h.hyp.mem_twoCore x₂
             (Subgroup.subset_closure (by simp))
           Wp_eq := rfl
           F_eq := rfl
           P_eq := fzc_sy3_P_gen h hq hK hq4 hqt ht ha hat
           M₂_eq := rfl
           M₃_eq := rfl
           U_eq := rfl
           nrm_E := fzc_sy3_U_nrm_E h hq hK hq4 hqt ht
           conj_t := fzc_sy3_U_conj_t h hq hK hq4 hqt ht
           P_E := fun p hp e he =>
             fzc_sy3_R_E h hq hK hq4 hqt p (fzc_sy3_P_le_R hq hp) e he
           P_t := fzc_sy3_P_t' h hq hK hq4 hqt ht
           b_sq := fzc_sy3_P_sq h hq hK hq4 hqt ht _ hbP hbW
           ab_sq := fzc_sy3_P_sq h hq hK hq4 hqt ht _ habP habW
           c_sq := fzc_sy3_c_sq h hK hqt
           ac_sq := fzc_sy3_ac_sq h hq hK hq4 hqt ht ha hat
           b_a := fzc_sy3_R_comm h hq hK hq4 hqt _
             (fzc_sy3_P_le_R hq hbP) _ (fzc_sy3_P_le_R hq ha)
           c_a := fzc_sy3_c_a h hq hK hq4 hqt ht ha hat
           c_b := fzc_sy3_c_b h hq hK hq4 hqt ht ha hat
           a_notin := fzc_sy3_a_notin h hat
           b_notin := hbNotin
           c_notin := hcNotin
           sp_ab := hsp1
           sp_a := hsp2
           sp_b := hsp3
           c_x₁ := fzc_sy3_c_x₁ h hK
           c_x₂ := fzc_sy3_c_x₂ h hK
           a_x := fzc_sy3_a_x h hq hK hq4 hqt ht ha hat
           a_t := hat
           e₀ := fzc_sy3_a_e0 h hq hK hq4 hqt ht ha hat }

end CFSG.OddStandard.SmallF3.FritzII
