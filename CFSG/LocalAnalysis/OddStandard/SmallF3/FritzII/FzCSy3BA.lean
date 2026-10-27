module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3E

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho q : G}

private lemma fzc_sy3_z_mem_fourGrp : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ :=
  Subgroup.subset_closure (by simp)

private lemma fzc_sy3_x₁_mem_base : x₁ ∈ baseGrp x₁ x₂ :=
  Subgroup.subset_closure (by simp)

private lemma fzc_sy3_x₂_mem_base : x₂ ∈ baseGrp x₁ x₂ :=
  Subgroup.subset_closure (by simp)

theorem fzc_sy3_a_x (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    (a * x₁ * a⁻¹ = x₁ ^ 3 ∧ a * x₂ * a⁻¹ = x₂ ^ 3) ∨
      (a * x₁ * a⁻¹ = x₁ * x₂ ^ 2 ∧ a * x₂ * a⁻¹ = x₁ ^ 2 * x₂) := by
  have htt : t * t = 1 := by rw [← pow_two]; exact fzc_sy2_t_sq h
  set e : G := q⁻¹ * a * q * a⁻¹ with he_def
  have heE : e ∈ baseGrp x₁ x₂ := by
    rw [he_def]
    have hKP := fzc_sy3_K_P h hq hK hq4 hqt ht q⁻¹ (inv_mem (mem_zpowers q)) a ha
    simpa using hKP
  have hqe : q⁻¹ * a * q = e * a := by rw [he_def]; group
  have ha2Wp : a ^ 2 ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
    rw [pow_two]
    exact fzc_sy3_R_sq h hq hK hq4 hqt a (fzc_sy3_P_le_R hq ha)
  have ha2W : a ^ 2 ∈ ctxW t x₁ x₂ := fzc_sy3_Wp_le_W h ha2Wp
  have hqa2 : q⁻¹ * a ^ 2 * q = a ^ 2 := by
    have hcomm : q * a ^ 2 = a ^ 2 * q := fzc_sy3_q_comm_W h hK (a ^ 2) ha2W
    calc q⁻¹ * a ^ 2 * q = q⁻¹ * (q * a ^ 2) := by rw [hcomm]; group
      _ = a ^ 2 := by group
  have hae : a * e * a⁻¹ = e⁻¹ := by
    have hsq1 : (q⁻¹ * a * q) ^ 2 = q⁻¹ * a ^ 2 * q := by rw [pow_two, pow_two]; group
    have hsq2 : (e * a) ^ 2 = e * (a * e * a⁻¹) * a ^ 2 := by rw [pow_two, pow_two]; group
    have heq : q⁻¹ * a ^ 2 * q = e * (a * e * a⁻¹) * a ^ 2 := by
      have h1 : (q⁻¹ * a * q) ^ 2 = (e * a) ^ 2 := by rw [hqe]
      rw [← hsq1, h1, hsq2]
    rw [hqa2] at heq
    have h1 : e * (a * e * a⁻¹) = 1 := by
      have h2 : (1 : G) * a ^ 2 = e * (a * e * a⁻¹) * a ^ 2 := by
        rw [one_mul]; exact heq
      exact (mul_right_cancel h2).symm
    exact mul_eq_one_iff_eq_inv'.mp h1
  have he2 : e ^ 2 = (x₁ * x₂) ^ 2 := by
    have h1 : q⁻¹ * (q⁻¹ * a * q) * q = e ^ 2 * a := by
      rw [hqe]
      have hqec : q⁻¹ * e * q = e := by
        have hcomm : q * e = e * q := fzc_sy3_q_comm_W h hK e (mem_sup_right heE)
        calc q⁻¹ * e * q = q⁻¹ * (q * e) := by rw [hcomm]; group
          _ = e := by group
      calc q⁻¹ * (e * a) * q = (q⁻¹ * e * q) * (q⁻¹ * a * q) := by group
        _ = e * (e * a) := by rw [hqec, hqe]
        _ = e ^ 2 * a := by rw [pow_two]; group
    have hq2 : q⁻¹ * (q⁻¹ * a * q) * q = t * a * t := by
      have hqq : q⁻¹ * (q⁻¹ * a * q) * q = (q * q)⁻¹ * a * (q * q) := by
        rw [mul_inv_rev]; group
      rw [hqq, show q * q = t by rw [← pow_two]; exact hqt,
        inv_eq_of_mul_eq_one_right htt]
    have heqt : t * a * t = e ^ 2 * a := by rw [← hq2, h1]
    have h2 : t * a * t * a⁻¹ = (x₁ * x₂) ^ 2 := by
      calc t * a * t * a⁻¹ = t * (a * t * a⁻¹) := by group
        _ = t * (t * (x₁ * x₂) ^ 2) := by rw [hat]
        _ = (x₁ * x₂) ^ 2 := by rw [← mul_assoc, htt, one_mul]
    have h3 : e ^ 2 = t * a * t * a⁻¹ := by
      have h' : t * a * t * a⁻¹ = e ^ 2 * a * a⁻¹ := by rw [← heqt]
      rw [h']; group
    rw [h3, h2]
  have hg1 : a * x₁ * a⁻¹ * x₁⁻¹ ∈ fourGrp x₁ x₂ :=
    fzc_sy3_R_E h hq hK hq4 hqt a (fzc_sy3_P_le_R hq ha) x₁ fzc_sy3_x₁_mem_base
  have hg2 : a * x₂ * a⁻¹ * x₂⁻¹ ∈ fourGrp x₁ x₂ :=
    fzc_sy3_R_E h hq hK hq4 hqt a (fzc_sy3_P_le_R hq ha) x₂ fzc_sy3_x₂_mem_base
  have hgs : a * x₂ * a⁻¹ * x₂⁻¹ = lam * (a * x₁ * a⁻¹ * x₁⁻¹) * lam⁻¹ := by
    have hdW' : lam * a * lam⁻¹ * a⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t :=
      fzc_sy3_lam_a_Wp h hq hK hq4 hqt ht ha hat
    have hdW : lam * a * lam⁻¹ * a⁻¹ ∈ ctxW t x₁ x₂ := fzc_sy3_Wp_le_W h hdW'
    have hax2W : a * x₂ * a⁻¹ ∈ ctxW t x₁ x₂ :=
      Subgroup.mem_sup_right (fzc_sy3_R_nrm_E h hq hK hq4 hqt a (fzc_sy3_P_le_R hq ha) x₂
        fzc_sy3_x₂_mem_base)
    have hcomm : (lam * a * lam⁻¹ * a⁻¹) * (a * x₂ * a⁻¹) =
        (a * x₂ * a⁻¹) * (lam * a * lam⁻¹ * a⁻¹) :=
      fzc_sy2_W_comm h _ hdW _ hax2W
    have h1 : lam * (a * x₁ * a⁻¹ * x₁⁻¹) * lam⁻¹ =
        (lam * a * lam⁻¹) * x₂ * (lam * a * lam⁻¹)⁻¹ * x₂⁻¹ := by
      rw [show lam * (a * x₁ * a⁻¹ * x₁⁻¹) * lam⁻¹ =
          (lam * a * lam⁻¹) * (lam * x₁ * lam⁻¹) * (lam * a * lam⁻¹)⁻¹ *
            (lam * x₁ * lam⁻¹)⁻¹ by group, h.wreath.conj_x₁]
    have hla : lam * a * lam⁻¹ = (lam * a * lam⁻¹ * a⁻¹) * a := by group
    rw [h1, hla]
    rw [show (lam * a * lam⁻¹ * a⁻¹) * a * x₂ * ((lam * a * lam⁻¹ * a⁻¹) * a)⁻¹ * x₂⁻¹ =
        (lam * a * lam⁻¹ * a⁻¹) * (a * x₂ * a⁻¹) * (lam * a * lam⁻¹ * a⁻¹)⁻¹ * x₂⁻¹
          by group, hcomm]
    group
  exact fzc_sy3_ax (g := a) (s := lam) (e := e)
    h.wreath.comm h.wreath.ord_x₁ h.wreath.ord_x₂ h.wreath.inf_eq_bot
    h.wreath.conj_x₁ (fzc_sy3_lam_x₂ h) hg1 hg2 hgs heE he2 hae

theorem fzc_sy3_a_e0 (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    a ^ 2 * t = x₁ * x₂ ^ 3 ∨ a ^ 2 * t = x₁ ^ 3 * x₂ := by
  have htt : t * t = 1 := by rw [← pow_two]; exact fzc_sy2_t_sq h
  have hg := fzc_sy3_a_x h hq hK hq4 hqt ht ha hat
  have he0E : a ^ 2 * t ∈ baseGrp x₁ x₂ :=
    fzc_sy3_P_sq h hq hK hq4 hqt ht a ha (fzc_sy3_a_notin h hat)
  have hEab : ∀ u ∈ baseGrp x₁ x₂, ∀ v ∈ baseGrp x₁ x₂, u * v = v * u :=
    fun u hu v hv => fzc_sy2_W_comm h u (mem_sup_right hu) v (mem_sup_right hv)
  have htE : ∀ u ∈ baseGrp x₁ x₂, t * u = u * t :=
    fun u hu => S4A.pt_comm_base h t h.hyp.mem_twoCore u hu
  have hz : a * (a ^ 2 * t) * a⁻¹ * (a ^ 2 * t)⁻¹ = (x₁ * x₂) ^ 2 := by
    have h1 : a * (a ^ 2 * t) * a⁻¹ = (a ^ 2 * t) * (x₁ * x₂) ^ 2 := by
      calc a * (a ^ 2 * t) * a⁻¹ = a ^ 2 * (a * t * a⁻¹) := by group
        _ = a ^ 2 * (t * (x₁ * x₂) ^ 2) := by rw [hat]
        _ = (a ^ 2 * t) * (x₁ * x₂) ^ 2 := by group
    rw [h1]
    have hzE : (x₁ * x₂) ^ 2 ∈ ctxW t x₁ x₂ :=
      mem_sup_right (S4A.pt_four_le_base x₁ x₂ fzc_sy3_z_mem_fourGrp)
    have he0W : a ^ 2 * t ∈ ctxW t x₁ x₂ := mem_sup_right he0E
    rw [fzc_sy2_W_comm h _ he0W _ hzE]
    group
  set e'' : G := a * (lam * a * lam⁻¹) with he''_def
  have he''E : e'' ∈ baseGrp x₁ x₂ := by
    rw [he''_def]
    have h1 : a * (lam * a * lam⁻¹) = a * (lam * a * lam⁻¹ * a) * a⁻¹ := by group
    rw [h1]
    exact fzc_sy3_R_nrm_E h hq hK hq4 hqt a (fzc_sy3_P_le_R hq ha) _
      (fzc_sy3_lam_a_E h hq hK hq4 hqt ht ha hat)
  have hfix : a * (lam * e'' * lam⁻¹) * a⁻¹ = e'' := by
    have hl2 : lam * lam = 1 := fzc_sy3_lam_sq h
    have hl2i : lam⁻¹ * lam⁻¹ = 1 := by rw [← mul_inv_rev, hl2, inv_one]
    have h1 : lam * e'' * lam⁻¹ = (lam * a * lam⁻¹) * a := by
      rw [he''_def]
      rw [show lam * (a * (lam * a * lam⁻¹)) * lam⁻¹ =
          (lam * a * lam⁻¹) * (lam * lam) * a * (lam⁻¹ * lam⁻¹) by group, hl2, hl2i]
      group
    rw [h1]
    rw [he''_def]
    group
  have hae'' : a * e'' * a⁻¹ = e''⁻¹ := by
    have h := fzc_sy3_e2 (g := a) (s := lam) (e := e'')
      h.wreath.comm h.wreath.ord_x₁ h.wreath.ord_x₂ h.wreath.inf_eq_bot
      h.wreath.conj_x₁ (fzc_sy3_lam_x₂ h) hg he''E hfix
    have h1 : a * e'' * a⁻¹ * e''⁻¹ = (e'' ^ 2)⁻¹ := mul_eq_one_iff_eq_inv'.mp h
    have h2 : a * e'' * a⁻¹ = (e'' ^ 2)⁻¹ * e'' := by rw [← h1]; group
    rw [h2]; group
  have haie'' : a⁻¹ * e'' * a = e''⁻¹ := by
    have h1 : a * e''⁻¹ * a⁻¹ = e'' := by
      calc a * e''⁻¹ * a⁻¹ = (a * e'' * a⁻¹)⁻¹ := by group
        _ = (e''⁻¹)⁻¹ := by rw [hae'']
        _ = e'' := by group
    calc a⁻¹ * e'' * a = a⁻¹ * (a * e''⁻¹ * a⁻¹) * a := by rw [h1]
      _ = e''⁻¹ := by group
  have hla : lam * a * lam⁻¹ = a⁻¹ * e'' := by rw [he''_def]; group
  have hse : lam * (a ^ 2 * t) * lam⁻¹ = (a ^ 2 * t)⁻¹ := by
    have hlt : lam * t * lam⁻¹ = t := by rw [fzc_sy3_lam_t h hK hqt]; group
    have h1 : lam * (a ^ 2 * t) * lam⁻¹ = (lam * a * lam⁻¹) ^ 2 * t := by
      rw [show lam * (a ^ 2 * t) * lam⁻¹ =
          (lam * a * lam⁻¹) ^ 2 * (lam * t * lam⁻¹) by simp only [pow_two]; group, hlt]
    rw [h1, hla, pow_two]
    have h2 : (a⁻¹ * e'') * (a⁻¹ * e'') = e''⁻¹ * (a ^ 2)⁻¹ * e'' := by
      calc (a⁻¹ * e'') * (a⁻¹ * e'') = (a⁻¹ * e'' * a) * ((a ^ 2)⁻¹ * e'') := by group
        _ = e''⁻¹ * (a ^ 2)⁻¹ * e'' := by rw [haie'', mul_assoc]
    have h3 : (a ^ 2)⁻¹ = t * (a ^ 2 * t)⁻¹ := by
      have h : a ^ 2 = (a ^ 2 * t) * t := by rw [mul_assoc, htt, mul_one]
      calc (a ^ 2)⁻¹ = ((a ^ 2 * t) * t)⁻¹ := by rw [← h]
        _ = t⁻¹ * (a ^ 2 * t)⁻¹ := by rw [mul_inv_rev]
        _ = t * (a ^ 2 * t)⁻¹ := by rw [inv_eq_of_mul_eq_one_right htt]
    rw [h2, h3]
    have hstep : e''⁻¹ * (t * (a ^ 2 * t)⁻¹) * e'' * t = (a ^ 2 * t)⁻¹ := by
      have hcomm1 : e''⁻¹ * t = t * e''⁻¹ := (htE e''⁻¹ (inv_mem he''E)).symm
      have hab : e''⁻¹ * (a ^ 2 * t)⁻¹ * e'' = (a ^ 2 * t)⁻¹ := by
        rw [hEab e''⁻¹ (inv_mem he''E) (a ^ 2 * t)⁻¹ (inv_mem he0E)]
        group
      calc e''⁻¹ * (t * (a ^ 2 * t)⁻¹) * e'' * t
          = (e''⁻¹ * t) * (a ^ 2 * t)⁻¹ * e'' * t := by group
        _ = (t * e''⁻¹) * (a ^ 2 * t)⁻¹ * e'' * t := by rw [hcomm1]
        _ = t * (e''⁻¹ * (a ^ 2 * t)⁻¹ * e'') * t := by group
        _ = t * (a ^ 2 * t)⁻¹ * t := by rw [hab]
        _ = (a ^ 2 * t)⁻¹ := by rw [htE (a ^ 2 * t)⁻¹ (inv_mem he0E), mul_assoc, htt, mul_one]
    exact hstep
  exact fzc_sy3_e0 (g := a) (s := lam) (e := a ^ 2 * t) h.wreath.comm h.wreath.ord_x₁
    h.wreath.ord_x₂ h.wreath.inf_eq_bot h.wreath.conj_x₁ (fzc_sy3_lam_x₂ h) hg he0E hz hse

end CFSG.OddStandard.SmallF3.FritzII
