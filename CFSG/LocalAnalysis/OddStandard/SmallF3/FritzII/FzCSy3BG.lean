module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BL

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Stage1.Thm6.Sec13

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho q : G}

private theorem fzc_sy3_c_b_eq (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    q * lam * (rho * a * rho⁻¹) * (q * lam)⁻¹ =
      (rho⁻¹ * ((lam * a * lam⁻¹ * a⁻¹) * (q * a * q⁻¹ * a⁻¹)) * rho) *
        (rho⁻¹ * a * rho) := by
  set d : G := lam * a * lam⁻¹ * a⁻¹ with hd
  set k : G := q * a * q⁻¹ * a⁻¹ with hk
  have hdWp : d ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
    rw [hd]; exact fzc_sy3_lam_a_Wp h hq hK hq4 hqt ht ha hat
  have hdW : d ∈ ctxW t x₁ x₂ := fzc_sy3_Wp_le_W h hdWp
  have hq_rho : q * rho = rho * q := (fzc_sy3_q_rho h hK).symm
  have hqri : q * rho⁻¹ = rho⁻¹ * q := by
    have hh := congrArg (fun x => rho⁻¹ * x * rho⁻¹) hq_rho
    simpa [mul_assoc] using hh.symm
  have hqri2 : rho * q⁻¹ = q⁻¹ * rho := by
    have hh := congrArg (fun x => q⁻¹ * x * q⁻¹) hq_rho
    simpa [mul_assoc] using hh
  have hqd : q * d = d * q := fzc_sy3_q_comm_W h hK d hdW
  have hla : lam * a * lam⁻¹ = d * a := by rw [hd]; group
  have hqa : q * a * q⁻¹ = k * a := by rw [hk]; group
  have hlam_rhoi : lam * rho⁻¹ * lam⁻¹ = rho := by
    have hh := congrArg (fun x => x⁻¹) h.lam_rho
    simpa [mul_inv_rev, inv_inv, mul_assoc] using hh
  calc q * lam * (rho * a * rho⁻¹) * (q * lam)⁻¹
      = q * (lam * rho * a * rho⁻¹ * lam⁻¹) * q⁻¹ := by
        simp only [mul_inv_rev, inv_inv]; group
    _ = q * ((lam * rho * lam⁻¹) * (lam * a * lam⁻¹) * (lam * rho⁻¹ * lam⁻¹)) * q⁻¹ := by
        rw [show lam * rho * a * rho⁻¹ * lam⁻¹
              = (lam * rho * lam⁻¹) * (lam * a * lam⁻¹) * (lam * rho⁻¹ * lam⁻¹) by group]
    _ = q * (rho⁻¹ * (d * a) * rho) * q⁻¹ := by rw [h.lam_rho, hlam_rhoi, hla]
    _ = q * rho⁻¹ * (d * a) * rho * q⁻¹ := by group
    _ = rho⁻¹ * (q * d) * a * rho * q⁻¹ := by rw [hqri]; group
    _ = rho⁻¹ * (d * q) * a * rho * q⁻¹ := by rw [hqd]
    _ = rho⁻¹ * d * (q * a) * (rho * q⁻¹) := by group
    _ = rho⁻¹ * d * (q * a) * (q⁻¹ * rho) := by rw [hqri2]
    _ = rho⁻¹ * d * (q * a * q⁻¹) * rho := by group
    _ = rho⁻¹ * d * (k * a) * rho := by rw [hqa]
    _ = (rho⁻¹ * (d * k) * rho) * (rho⁻¹ * a * rho) := by rw [hd, hk]; group

theorem fzc_sy3_a_norm (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t) {a : G}
    (ha : a ∈ fzP t x₁ x₂ rho) :
    a * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho) ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
  have haP : a ∈ ⁅fzR t x₁ x₂, zpowers rho⁆ := by rw [← fzc_sy3_P_eq hq]; exact ha
  exact fzc_sy3_norm (R := fzR t x₁ x₂) (N := baseGrp x₁ x₂ ⊔ zpowers t)
    ((fzc_sy3_Wp_le_W h).trans hq.W_le_R) (fzc_sy3_R_Wp h hq hK hq4 hqt) hq.rho_norm_R
    (fzc_sy3_rho_Wp h) (fzc_sy3_R_comm h hq hK hq4 hqt) (fzc_sy3_rho3 h) a haP

theorem fzc_sy3_b_notin (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    rho * a * rho⁻¹ ∉ (baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a := by
  intro hb
  have haR : a ∈ fzR t x₁ x₂ := fzc_sy3_P_le_R hq ha
  have haa : a * a ∈ baseGrp x₁ x₂ ⊔ zpowers t := fzc_sy3_R_sq h hq hK hq4 hqt a haR
  have haN : ∀ w ∈ baseGrp x₁ x₂ ⊔ zpowers t,
      a * w * a⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t := fzc_sy3_R_Wp h hq hK hq4 hqt a haR
  obtain ⟨u, hu, hbq | hbq⟩ :=
    (mem_sup_zpowers_sq (N := baseGrp x₁ x₂ ⊔ zpowers t) (s := a) haa haN).1 hb
  · refine fzc_sy3_a_notin h hat ?_
    have haeq : a = rho⁻¹ * u * rho := by rw [← hbq]; group
    rw [haeq, fzc_sy3_rho_inv_conj h u]
    exact fzc_sy3_rho_Wp h _ (fzc_sy3_rho_Wp h u hu)
  · refine fzc_sy3_a_notin h hat (fzc_sy3_rho_PWp h hq hK hq4 hqt ht a ha ?_)
    have hcomm : rho * a * rho⁻¹ * a⁻¹ = u := by rw [hbq]; group
    rw [hcomm]; exact hu

theorem fzc_sy3_P_gen (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    fzP t x₁ x₂ rho = ((baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a) ⊔ zpowers (rho * a * rho⁻¹) := by
  have haR : a ∈ fzR t x₁ x₂ := fzc_sy3_P_le_R hq ha
  have hbP : rho * a * rho⁻¹ ∈ fzP t x₁ x₂ rho := hq.rho_norm_P a ha
  have hbR : rho * a * rho⁻¹ ∈ fzR t x₁ x₂ := fzc_sy3_P_le_R hq hbP
  have hWpP : baseGrp x₁ x₂ ⊔ zpowers t ≤ fzP t x₁ x₂ rho := fzc_sy3_Wp_le_P h hq ht
  have hFmem : a * a ∈ baseGrp x₁ x₂ ⊔ zpowers t := fzc_sy3_R_sq h hq hK hq4 hqt a haR
  have hN₁ : ∀ w ∈ baseGrp x₁ x₂ ⊔ zpowers t,
      a * w * a⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t := fzc_sy3_R_Wp h hq hK hq4 hqt a haR
  have hbFmem : (rho * a * rho⁻¹) * (rho * a * rho⁻¹) ∈
      (baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a :=
    Subgroup.mem_sup_left (fzc_sy3_R_sq h hq hK hq4 hqt (rho * a * rho⁻¹) hbR)
  have hb_norm : ∀ f ∈ (baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a,
      (rho * a * rho⁻¹) * f * (rho * a * rho⁻¹)⁻¹ ∈
        (baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a := by
    intro f hf
    obtain ⟨u, hu, hf | hf⟩ :=
      (mem_sup_zpowers_sq (N := baseGrp x₁ x₂ ⊔ zpowers t) (s := a) hFmem hN₁).1 hf
    · rw [hf]
      exact Subgroup.mem_sup_left (fzc_sy3_R_Wp h hq hK hq4 hqt (rho * a * rho⁻¹) hbR u hu)
    · have hb1 : (rho * a * rho⁻¹) * u * (rho * a * rho⁻¹)⁻¹ ∈
          baseGrp x₁ x₂ ⊔ zpowers t :=
        fzc_sy3_R_Wp h hq hK hq4 hqt (rho * a * rho⁻¹) hbR u hu
      have hb2 : (rho * a * rho⁻¹) * a * (rho * a * rho⁻¹)⁻¹ * a⁻¹ ∈
          baseGrp x₁ x₂ ⊔ zpowers t :=
        fzc_sy3_R_comm h hq hK hq4 hqt (rho * a * rho⁻¹) hbR a haR
      rw [hf, show (rho * a * rho⁻¹) * (u * a) * (rho * a * rho⁻¹)⁻¹ =
          ((rho * a * rho⁻¹) * u * (rho * a * rho⁻¹)⁻¹) *
            ((rho * a * rho⁻¹) * a * (rho * a * rho⁻¹)⁻¹ * a⁻¹) * a by group]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mem_sup_left hb1) (Subgroup.mem_sup_left hb2))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
  have hcardF : Nat.card ↥((baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a) =
      2 * Nat.card ↥(baseGrp x₁ x₂ ⊔ zpowers t) :=
    card_sup_zpowers_sq (N := baseGrp x₁ x₂ ⊔ zpowers t) (s := a) hFmem hN₁
      (fzc_sy3_a_notin h hat)
  have hcardFb : Nat.card ↥(((baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a) ⊔
      zpowers (rho * a * rho⁻¹)) =
      2 * Nat.card ↥((baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a) :=
    card_sup_zpowers_sq (N := (baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a)
      (s := rho * a * rho⁻¹) hbFmem hb_norm (fzc_sy3_b_notin h hq hK hq4 hqt ht ha hat)
  have hKP : ((baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a) ⊔ zpowers (rho * a * rho⁻¹) ≤
      fzP t x₁ x₂ rho := sup_le (sup_le hWpP (zpowers_le.2 ha)) (zpowers_le.2 hbP)
  have hcards : Nat.card ↥(fzP t x₁ x₂ rho) =
      Nat.card ↥(((baseGrp x₁ x₂ ⊔ zpowers t) ⊔ zpowers a) ⊔
        zpowers (rho * a * rho⁻¹)) := by
    rw [fzc_sy3_card_P h hq hK hq4 hqt ht, hcardFb, hcardF, fzc_sy3_card_Wp h]
  exact (Subgroup.eq_of_le_of_card_ge hKP (le_of_eq hcards)).symm

theorem fzc_sy3_c_a (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    q * lam * a * (q * lam)⁻¹ * a⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
  set d : G := lam * a * lam⁻¹ * a⁻¹ with hd
  set k : G := q * a * q⁻¹ * a⁻¹ with hk
  have hdWp : d ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
    rw [hd]; exact fzc_sy3_lam_a_Wp h hq hK hq4 hqt ht ha hat
  have hkE : k ∈ baseGrp x₁ x₂ := by
    rw [hk]; exact fzc_sy3_K_P h hq hK hq4 hqt ht q (Subgroup.mem_zpowers q) a ha
  have hdW : d ∈ ctxW t x₁ x₂ := fzc_sy3_Wp_le_W h hdWp
  have hqd : q * d * q⁻¹ = d := by
    rw [fzc_sy3_q_comm_W h hK d hdW]; group
  have heq : q * lam * a * (q * lam)⁻¹ * a⁻¹ = (q * d * q⁻¹) * k := by
    rw [hd, hk]; group
  rw [heq, hqd]
  exact Subgroup.mul_mem _ hdWp (Subgroup.mem_sup_left hkE)

theorem fzc_sy3_c_b (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    q * lam * (rho * a * rho⁻¹) * (q * lam)⁻¹ * (a * (rho * a * rho⁻¹))⁻¹ ∈
      baseGrp x₁ x₂ ⊔ zpowers t := by
  set b : G := rho * a * rho⁻¹ with hb
  set bp : G := rho⁻¹ * a * rho with hbp
  set w1 : G := rho⁻¹ * ((lam * a * lam⁻¹ * a⁻¹) * (q * a * q⁻¹ * a⁻¹)) * rho with hw1
  have haR : a ∈ fzR t x₁ x₂ := fzc_sy3_P_le_R hq ha
  have hbP : b ∈ fzP t x₁ x₂ rho := by rw [hb]; exact hq.rho_norm_P a ha
  have hbR : b ∈ fzR t x₁ x₂ := fzc_sy3_P_le_R hq hbP
  have hbpP : bp ∈ fzP t x₁ x₂ rho := by
    rw [hbp, fzc_sy3_rho_inv_conj h a]; exact hq.rho_norm_P _ hbP
  have hbpR : bp ∈ fzR t x₁ x₂ := fzc_sy3_P_le_R hq hbpP
  have hdWp : lam * a * lam⁻¹ * a⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t :=
    fzc_sy3_lam_a_Wp h hq hK hq4 hqt ht ha hat
  have hkE : q * a * q⁻¹ * a⁻¹ ∈ baseGrp x₁ x₂ :=
    fzc_sy3_K_P h hq hK hq4 hqt ht q (Subgroup.mem_zpowers q) a ha
  have hdkWp : (lam * a * lam⁻¹ * a⁻¹) * (q * a * q⁻¹ * a⁻¹) ∈
      baseGrp x₁ x₂ ⊔ zpowers t :=
    Subgroup.mul_mem _ hdWp (Subgroup.mem_sup_left hkE)
  have hw1Wp : w1 ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
    rw [hw1, fzc_sy3_rho_inv_conj h ((lam * a * lam⁻¹ * a⁻¹) * (q * a * q⁻¹ * a⁻¹))]
    exact fzc_sy3_rho_Wp h _ (fzc_sy3_rho_Wp h _ hdkWp)
  have hcb : q * lam * b * (q * lam)⁻¹ = w1 * bp := by
    rw [hb, hw1]
    exact fzc_sy3_c_b_eq h hq hK hq4 hqt ht ha hat
  have hbase : a * b * bp ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
    rw [hb, hbp]; exact fzc_sy3_a_norm h hq hK hq4 hqt ha
  have habR : a * b ∈ fzR t x₁ x₂ := (fzR t x₁ x₂).mul_mem haR hbR
  have h1 : (a * b)⁻¹ * (a * b * bp) * (a * b) ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
    simpa using fzc_sy3_R_Wp h hq hK hq4 hqt (a * b)⁻¹ ((fzR t x₁ x₂).inv_mem habR)
      (a * b * bp) hbase
  have h2 : ((a * b) * (a * b))⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t :=
    (baseGrp x₁ x₂ ⊔ zpowers t).inv_mem (fzc_sy3_R_sq h hq hK hq4 hqt (a * b) habR)
  have hbp_eq : bp = (a * b)⁻¹ * (a * b * bp) := by group
  rw [hcb, hbp_eq]
  rw [show w1 * ((a * b)⁻¹ * (a * b * bp)) * (a * b)⁻¹ =
      w1 * ((a * b)⁻¹ * (a * b * bp) * (a * b)) * ((a * b) * (a * b))⁻¹ by group]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw1Wp h1) h2

end CFSG.OddStandard.SmallF3.FritzII
