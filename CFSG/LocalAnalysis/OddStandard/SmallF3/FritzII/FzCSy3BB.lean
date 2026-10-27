module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BG

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Stage1.Thm6.Sec13

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho q : G}

theorem fzc_sy3_ac_sq (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    (a * (q * lam)) ^ 2 * t ∈ baseGrp x₁ x₂ := by
  set d : G := lam * a * lam⁻¹ * a⁻¹ with hd
  set k : G := q * a * q⁻¹ * a⁻¹ with hk
  have ht2 : t * t = 1 := by rw [← pow_two]; exact fzc_sy2_t_sq h
  have hdWp : d ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
    rw [hd]; exact fzc_sy3_lam_a_Wp h hq hK hq4 hqt ht ha hat
  have hkE : k ∈ baseGrp x₁ x₂ := by
    rw [hk]; exact fzc_sy3_K_P h hq hK hq4 hqt ht q (Subgroup.mem_zpowers q) a ha
  have hdW : d ∈ ctxW t x₁ x₂ := fzc_sy3_Wp_le_W h hdWp
  have hqd : q * d = d * q := fzc_sy3_q_comm_W h hK d hdW
  have hlam_a : lam * a * lam⁻¹ = d * a := by rw [hd]; group
  have hlam_q : lam * q * lam = q := by
    rw [← fzc_sy3_q_lam h hK, mul_assoc, fzc_sy3_lam_sq h, mul_one]
  have hqa : q * a * q⁻¹ = k * a := by rw [hk]; group
  have hident : (a * (q * lam)) ^ 2 * t = a * (d * k) * a := by
    calc (a * (q * lam)) ^ 2 * t
        = a * (q * (lam * a * lam⁻¹) * (lam * q * lam)) * t := by
          simp only [pow_two]; group
      _ = a * (q * (d * a) * q) * t := by rw [hlam_a, hlam_q]
      _ = a * (d * (k * a) * t) * t := by
          rw [show q * (d * a) * q = d * (k * a) * t by
            calc q * (d * a) * q = (q * d) * a * q := by group
              _ = (d * q) * a * q := by rw [hqd]
              _ = d * (q * a * q⁻¹) * (q * q) := by group
              _ = d * (k * a) * (q * q) := by rw [hqa]
              _ = d * (k * a) * t := by rw [← pow_two, hqt]]
      _ = a * (d * k) * a := by
          rw [show a * (d * (k * a) * t) * t = a * (d * k) * a * (t * t) by group,
            ht2, mul_one]
  rw [hident]
  have hda2 : d * a ^ 2 ∈ baseGrp x₁ x₂ := by
    rw [show d * a ^ 2 = lam * a * lam⁻¹ * a by rw [hd]; group]
    exact fzc_sy3_lam_a_E h hq hK hq4 hqt ht ha hat
  have hta2inv : t * (a ^ 2)⁻¹ ∈ baseGrp x₁ x₂ := by
    have hh := (baseGrp x₁ x₂).inv_mem
      (fzc_sy3_P_sq h hq hK hq4 hqt ht a ha (fzc_sy3_a_notin h hat))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2] at hh
    exact hh
  have htd : t * d ∈ baseGrp x₁ x₂ := by
    have htE : t * (d * a ^ 2) = (d * a ^ 2) * t :=
      S4A.pt_comm_base h t h.hyp.mem_twoCore _ hda2
    have heq : t * d = (d * a ^ 2) * (t * (a ^ 2)⁻¹) := by
      calc t * d = t * (d * a ^ 2 * (a ^ 2)⁻¹) := by group
        _ = t * (d * a ^ 2) * (a ^ 2)⁻¹ := by group
        _ = (d * a ^ 2) * t * (a ^ 2)⁻¹ := by rw [htE]
        _ = (d * a ^ 2) * (t * (a ^ 2)⁻¹) := by group
    rw [heq]
    exact mul_mem hda2 hta2inv
  have htdk : t * (d * k) ∈ baseGrp x₁ x₂ := by
    rw [← mul_assoc]; exact mul_mem htd hkE
  have haR : a ∈ fzR t x₁ x₂ := fzc_sy3_P_le_R hq ha
  have htadka : t * (a * (d * k) * a⁻¹) ∈ baseGrp x₁ x₂ :=
    fzc_sy3_R_tE h hq hK hq4 hqt a haR (d * k) htdk
  have hta2 : t * a ^ 2 ∈ baseGrp x₁ x₂ := by
    have hh := fzc_sy3_P_sq h hq hK hq4 hqt ht a ha (fzc_sy3_a_notin h hat)
    rwa [fzc_sy3_t_comm_Et h hh] at hh
  have hfinal : (a * (d * k) * a⁻¹) * a ^ 2 ∈ baseGrp x₁ x₂ :=
    fzc_sy3_tE_mul h htadka hta2
  rw [show a * (d * k) * a = (a * (d * k) * a⁻¹) * a ^ 2 by group]
  exact hfinal

private theorem fzc_sy3_sp_e0Z (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    a ^ 2 * t ∉ fourGrp x₁ x₂ := by
  intro hZ
  have haR : a ∈ fzR t x₁ x₂ := fzc_sy3_P_le_R hq ha
  have hcomm : a * (a ^ 2 * t) * a⁻¹ = a ^ 2 * t := by
    rw [hq.R_cent_fourGrp a haR (a ^ 2 * t) hZ]; group
  have h1 : a * (a ^ 2 * t) * a⁻¹ = (a ^ 2 * t) * ((x₁ * x₂) ^ 2) := by
    calc a * (a ^ 2 * t) * a⁻¹ = a ^ 2 * (a * t * a⁻¹) := by group
      _ = a ^ 2 * (t * (x₁ * x₂) ^ 2) := by rw [hat]
      _ = (a ^ 2 * t) * (x₁ * x₂) ^ 2 := by group
  rw [hcomm] at h1
  exact fzc_sy3_z_ne_one h
    (mul_left_cancel (a := a ^ 2 * t) (show (a ^ 2 * t) * 1 = (a ^ 2 * t) * (x₁ * x₂) ^ 2 by
      rw [mul_one, ← h1])).symm

private theorem fzc_sy3_sp_norm (h : Ctx0 t L S x₁ x₂ lam rho)
    (hq : FzCQFacts t S x₁ x₂ lam rho) (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4)
    (hqt : q ^ 2 = t) (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    (a ^ 2 * t) * (rho * (a ^ 2 * t) * rho⁻¹) * (rho⁻¹ * (a ^ 2 * t) * rho) = 1 := by
  set e0 : G := a ^ 2 * t with he0
  set s : G := rho * e0 * rho⁻¹ with hs
  set s' : G := rho⁻¹ * e0 * rho with hs'
  have he0E : e0 ∈ baseGrp x₁ x₂ := by
    rw [he0]; exact fzc_sy3_P_sq h hq hK hq4 hqt ht a ha (fzc_sy3_a_notin h hat)
  have hsE : s ∈ baseGrp x₁ x₂ := by rw [hs]; exact fzc_sy2_rho_nrm_E h e0 he0E
  have hs'E : s' ∈ baseGrp x₁ x₂ := by
    rw [hs', fzc_sy3_rho_inv_conj h e0]; exact fzc_sy2_rho_nrm_E h _ hsE
  have hEc : ∀ e ∈ baseGrp x₁ x₂, ∀ f ∈ baseGrp x₁ x₂, e * f = f * e := by
    intro e he f hf
    exact congrArg Subtype.val (isMulCommutative_iff.mp (h.wreath.baseGrp_eq).1 ⟨e, he⟩ ⟨f, hf⟩)
  have hmE : e0 * s * s' ∈ baseGrp x₁ x₂ := mul_mem (mul_mem he0E hsE) hs'E
  have hs'eq : rho * s * rho⁻¹ = s' := by rw [hs, hs', fzc_sy3_rho_inv_conj h e0]
  have he0eq : rho * s' * rho⁻¹ = e0 := by rw [hs']; group
  have hfix : rho * (e0 * s * s') * rho⁻¹ = e0 * s * s' := by
    have hconj : rho * (e0 * s * s') * rho⁻¹ = s * s' * e0 := by
      calc rho * (e0 * s * s') * rho⁻¹ =
          (rho * e0 * rho⁻¹) * (rho * s * rho⁻¹) * (rho * s' * rho⁻¹) := by group
        _ = s * s' * e0 := by rw [← hs, hs'eq, he0eq]
    rw [hconj]
    calc s * s' * e0 = e0 * (s * s') := hEc (s * s') (mul_mem hsE hs'E) e0 he0E
      _ = e0 * s * s' := by group
  have hmC : e0 * s * s' ∈ Subgroup.centralizer ({rho} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (e0 * s * s') * rho = (rho * (e0 * s * s') * rho⁻¹) * rho := by rw [hfix]
      _ = rho * (e0 * s * s') := by group
  have hmem : e0 * s * s' ∈ ctxW t x₁ x₂ ⊓ Subgroup.centralizer ({rho} : Set G) :=
    ⟨Subgroup.mem_sup_right hmE, hmC⟩
  rw [h.cent_rho] at hmem
  have hbot : e0 * s * s' ∈ twoCore t ⊓ baseGrp x₁ x₂ := ⟨hmem, hmE⟩
  rw [S4A.pt_inf_base h, Subgroup.mem_bot] at hbot
  exact hbot

theorem fzc_sy3_sp (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    a ^ 2 * ((rho * a * rho⁻¹) ^ 2)⁻¹ ∉ fourGrp x₁ x₂ ∧
      a ^ 2 * ((a * (rho * a * rho⁻¹)) ^ 2)⁻¹ ∉ fourGrp x₁ x₂ ∧
      (rho * a * rho⁻¹) ^ 2 * ((a * (rho * a * rho⁻¹)) ^ 2)⁻¹ ∉ fourGrp x₁ x₂ := by
  have ht2 : t * t = 1 := by rw [← pow_two]; exact fzc_sy2_t_sq h
  have hEc : ∀ e ∈ baseGrp x₁ x₂, ∀ f ∈ baseGrp x₁ x₂, e * f = f * e := by
    intro e he f hf
    exact congrArg Subtype.val (isMulCommutative_iff.mp (h.wreath.baseGrp_eq).1 ⟨e, he⟩ ⟨f, hf⟩)
  have htE : ∀ e ∈ baseGrp x₁ x₂, t * e = e * t :=
    fun e he => S4A.pt_comm_base h t h.hyp.mem_twoCore e he
  set e0 : G := a ^ 2 * t with he0
  set b : G := rho * a * rho⁻¹ with hb
  set bp : G := rho⁻¹ * a * rho with hbp
  set s : G := rho * e0 * rho⁻¹ with hs
  set s' : G := rho⁻¹ * e0 * rho with hs'
  set zeta : G := (a * b) ^ 2 * bp ^ 2 with hzeta_def
  have he0E : e0 ∈ baseGrp x₁ x₂ := by
    rw [he0]; exact fzc_sy3_P_sq h hq hK hq4 hqt ht a ha (fzc_sy3_a_notin h hat)
  have he0Z : e0 ∉ fourGrp x₁ x₂ := by
    rw [he0]; exact fzc_sy3_sp_e0Z h hq hK hq4 hqt ht ha hat
  have hsE : s ∈ baseGrp x₁ x₂ := by rw [hs]; exact fzc_sy2_rho_nrm_E h e0 he0E
  have hs'E : s' ∈ baseGrp x₁ x₂ := by
    rw [hs', fzc_sy3_rho_inv_conj h e0]; exact fzc_sy2_rho_nrm_E h _ hsE
  have hnorm : e0 * s * s' = 1 := by
    rw [he0, hs, hs']; exact fzc_sy3_sp_norm h hq hK hq4 hqt ht ha hat
  have ha2 : a ^ 2 = e0 * t := by rw [he0, mul_assoc, ht2, mul_one]
  have hb2 : b ^ 2 = s * t := by
    have e1 : b ^ 2 = rho * a ^ 2 * rho⁻¹ := by rw [hb]; simp only [pow_two]; group
    rw [e1, ha2]
    calc rho * (e0 * t) * rho⁻¹ = (rho * e0 * rho⁻¹) * (rho * t * rho⁻¹) := by group
      _ = s * t := by rw [← hs, fzc_sy2_rho_t h]
  have hbp2 : bp ^ 2 = s' * t := by
    have e1 : bp ^ 2 = rho⁻¹ * a ^ 2 * rho := by rw [hbp]; simp only [pow_two]; group
    rw [e1, ha2]
    calc rho⁻¹ * (e0 * t) * rho = (rho⁻¹ * e0 * rho) * (rho⁻¹ * t * rho) := by group
      _ = s' * t := by
          have htr : rho⁻¹ * t * rho = t := by
            rw [fzc_sy3_rho_inv_conj h t, fzc_sy2_rho_t h]
            exact fzc_sy2_rho_t h
          rw [← hs', htr]
  have hbP : b ∈ fzP t x₁ x₂ rho := by rw [hb]; exact hq.rho_norm_P a ha
  have hbR : b ∈ fzR t x₁ x₂ := fzc_sy3_P_le_R hq hbP
  have hbpP : bp ∈ fzP t x₁ x₂ rho := by
    rw [hbp, fzc_sy3_rho_inv_conj h a]; exact hq.rho_norm_P _ hbP
  have hbpR : bp ∈ fzR t x₁ x₂ := fzc_sy3_P_le_R hq hbpP
  have hnWp : a * b * bp ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
    rw [hb, hbp]; exact fzc_sy3_a_norm h hq hK hq4 hqt ha
  have hzeta : zeta ∈ fourGrp x₁ x₂ := by
    have hh := fzc_sy3_sq_coset h hq hK hq4 hqt bp⁻¹ ((fzR t x₁ x₂).inv_mem hbpR)
      (a * b * bp) hnWp
    have h1 : (a * b * bp) * bp⁻¹ = a * b := by group
    have h2 : ((bp⁻¹) ^ 2)⁻¹ = bp ^ 2 := by
      simp only [pow_two, mul_inv_rev, inv_inv]
    rw [h1, h2] at hh
    exact hh
  have hzetaE : zeta ∈ baseGrp x₁ x₂ := S4A.pt_four_le_base x₁ x₂ hzeta
  have he0s' : e0 * s' = s⁻¹ := by
    have hh : s * (e0 * s') = 1 := by rw [← mul_assoc, hEc s hsE e0 he0E]; exact hnorm
    exact eq_inv_of_mul_eq_one_right hh
  have hss' : s * s' = e0⁻¹ := by
    have hh : e0 * (s * s') = 1 := by rw [← mul_assoc]; exact hnorm
    exact eq_inv_of_mul_eq_one_right hh
  have hab2 : (a * b) ^ 2 = zeta * (bp ^ 2)⁻¹ := by rw [hzeta_def]; group
  have hab2inv : ((a * b) ^ 2)⁻¹ = bp ^ 2 * zeta⁻¹ := by rw [hab2, mul_inv_rev, inv_inv]
  have hsp1 : a ^ 2 * (b ^ 2)⁻¹ ∉ fourGrp x₁ x₂ := by
    have heq : a ^ 2 * (b ^ 2)⁻¹ = e0 * s⁻¹ := by rw [ha2, hb2]; group
    rw [heq]
    intro hZ
    have hZ' : rho * e0 * rho⁻¹ * e0⁻¹ ∈ fourGrp x₁ x₂ := by
      have hh := (fourGrp x₁ x₂).inv_mem hZ
      simpa [hs] using hh
    exact he0Z (fzc_sy3_rho_EZ h e0 he0E hZ')
  have hsp2 : a ^ 2 * ((a * b) ^ 2)⁻¹ ∉ fourGrp x₁ x₂ := by
    have heq : a ^ 2 * ((a * b) ^ 2)⁻¹ = zeta⁻¹ * s⁻¹ := by
      rw [ha2, hab2inv]
      calc (e0 * t) * (bp ^ 2 * zeta⁻¹) = e0 * (t * s') * t * zeta⁻¹ := by rw [hbp2]; group
        _ = e0 * (s' * t) * t * zeta⁻¹ := by rw [htE s' hs'E]
        _ = e0 * s' * (t * t) * zeta⁻¹ := by group
        _ = e0 * s' * zeta⁻¹ := by rw [ht2, mul_one]
        _ = s⁻¹ * zeta⁻¹ := by rw [he0s']
        _ = zeta⁻¹ * s⁻¹ := hEc s⁻¹ (inv_mem hsE) zeta⁻¹ (inv_mem hzetaE)
    rw [heq]
    intro hZ
    have hsZ : s ∈ fourGrp x₁ x₂ := by
      have h1 : s * zeta ∈ fourGrp x₁ x₂ := by
        have hh := (fourGrp x₁ x₂).inv_mem hZ
        simpa [mul_inv_rev, inv_inv] using hh
      rw [show s = (s * zeta) * zeta⁻¹ by group]
      exact mul_mem h1 ((fourGrp x₁ x₂).inv_mem hzeta)
    have hs2 : s ^ 2 = 1 := (WreathRel.fourGrp_eq_omega h.wreath).2.1.2 s hsZ
    have he0sq : e0 ^ 2 = 1 := by
      have hconj : rho * e0 ^ 2 * rho⁻¹ = 1 := by
        rw [← hs2, hs]; simp only [pow_two]; group
      calc e0 ^ 2 = rho⁻¹ * (rho * e0 ^ 2 * rho⁻¹) * rho := by group
        _ = 1 := by rw [hconj]; group
    exact he0Z (fzc_sy2_E_invol h e0 he0E he0sq)
  have hsp3 : b ^ 2 * ((a * b) ^ 2)⁻¹ ∉ fourGrp x₁ x₂ := by
    have heq : b ^ 2 * ((a * b) ^ 2)⁻¹ = zeta⁻¹ * e0⁻¹ := by
      rw [hb2, hab2inv]
      calc (s * t) * (bp ^ 2 * zeta⁻¹) = s * (t * s') * t * zeta⁻¹ := by rw [hbp2]; group
        _ = s * (s' * t) * t * zeta⁻¹ := by rw [htE s' hs'E]
        _ = s * s' * (t * t) * zeta⁻¹ := by group
        _ = s * s' * zeta⁻¹ := by rw [ht2, mul_one]
        _ = e0⁻¹ * zeta⁻¹ := by rw [hss']
        _ = zeta⁻¹ * e0⁻¹ := hEc e0⁻¹ (inv_mem he0E) zeta⁻¹ (inv_mem hzetaE)
    rw [heq]
    intro hZ
    refine he0Z ?_
    have h1 : e0 * zeta ∈ fourGrp x₁ x₂ := by
      have hh := (fourGrp x₁ x₂).inv_mem hZ
      simpa [mul_inv_rev, inv_inv] using hh
    rw [show e0 = (e0 * zeta) * zeta⁻¹ by group]
    exact mul_mem h1 ((fourGrp x₁ x₂).inv_mem hzeta)
  exact ⟨hsp1, hsp2, hsp3⟩

theorem fzc_sy3_U_cos (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hqt : q ^ 2 = t) (ht : t ∈ fzP t x₁ x₂ rho) :
    ∀ u ∈ fzP t x₁ x₂ rho ⊔ zpowers (q * lam),
      u ∈ fzP t x₁ x₂ rho ∨ u * (q * lam)⁻¹ ∈ fzP t x₁ x₂ rho := by
  have hqR : q ∈ fzR t x₁ x₂ := hq.W_le_R (fzc_sy3_q_mem_W hK)
  have hsq : (q * lam) * (q * lam) ∈ fzP t x₁ x₂ rho := by
    have h1 : (q * lam) * (q * lam) = q ^ 2 * lam ^ 2 := by
      calc (q * lam) * (q * lam) = q * (lam * q) * lam := by group
        _ = q * (q * lam) * lam := by rw [← fzc_sy3_q_lam h hK]
        _ = q ^ 2 * lam ^ 2 := by rw [pow_two, pow_two]; group
    rw [h1, hqt, show lam ^ 2 = 1 by rw [pow_two]; exact fzc_sy3_lam_sq h, mul_one]
    exact ht
  have hN : ∀ p ∈ fzP t x₁ x₂ rho, (q * lam) * p * (q * lam)⁻¹ ∈ fzP t x₁ x₂ rho := by
    intro p hp
    have hlp : lam * p * lam⁻¹ ∈ fzP t x₁ x₂ rho := hq.lam_norm_P p hp
    rw [show (q * lam) * p * (q * lam)⁻¹ = q * (lam * p * lam⁻¹) * q⁻¹ by group]
    exact hq.P_normal_R q hqR _ hlp
  intro u hu
  obtain ⟨p, hp, hu | hu⟩ :=
    (mem_sup_zpowers_sq (N := fzP t x₁ x₂ rho) (s := q * lam) hsq hN).1 hu
  · exact Or.inl (by rwa [hu])
  · rw [hu, show p * (q * lam) * (q * lam)⁻¹ = p by group]
    exact Or.inr hp

end CFSG.OddStandard.SmallF3.FritzII
