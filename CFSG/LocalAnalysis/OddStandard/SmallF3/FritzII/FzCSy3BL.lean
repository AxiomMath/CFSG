module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BQ

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho q : G}

private lemma fzc_sy3_z_mem_fourGrp : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ :=
  Subgroup.subset_closure (by simp)

private lemma fzc_sy3_z_sq (h : Ctx0 t L S x₁ x₂ lam rho) : ((x₁ * x₂) ^ 2) ^ 2 = 1 :=
  (WreathRel.fourGrp_eq_omega h.wreath).2.1.2 ((x₁ * x₂) ^ 2) fzc_sy3_z_mem_fourGrp

private lemma fzc_sy3_lam_z (h : Ctx0 t L S x₁ x₂ lam rho) :
    lam * (x₁ * x₂) ^ 2 * lam⁻¹ = (x₁ * x₂) ^ 2 := by
  have h1 : lam * (x₁ * x₂) * lam⁻¹ = x₂ * x₁ := by
    rw [show lam * (x₁ * x₂) * lam⁻¹ =
        (lam * x₁ * lam⁻¹) * (lam * x₂ * lam⁻¹) by group, h.wreath.conj_x₁,
      fzc_sy3_lam_x₂ h]
  have h2 : lam * ((x₁ * x₂) * (x₁ * x₂)) * lam⁻¹ = (x₂ * x₁) * (x₂ * x₁) := by
    rw [show lam * ((x₁ * x₂) * (x₁ * x₂)) * lam⁻¹ =
        (lam * (x₁ * x₂) * lam⁻¹) * (lam * (x₁ * x₂) * lam⁻¹) by group, h1]
  rw [pow_two, h2, ← h.wreath.comm]

theorem fzc_sy3_exists_a (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hqt : q ^ 2 = t) (ht : t ∈ fzP t x₁ x₂ rho) :
    ∃ a ∈ fzP t x₁ x₂ rho, a * t * a⁻¹ = t * (x₁ * x₂) ^ 2 := by
  obtain ⟨r, hr, hrt⟩ := hq.R_orbit_t _ fzc_sy3_z_mem_fourGrp
  rcases fzc_sy3_R_cos hq hK hqt ht r hr with hp | hp
  · exact ⟨r, hp, hrt⟩
  · refine ⟨r * q⁻¹, hp, ?_⟩
    have hqt' : q⁻¹ * t * q = t := by rw [← hqt]; group
    calc r * q⁻¹ * t * (r * q⁻¹)⁻¹ = r * (q⁻¹ * t * q) * r⁻¹ := by group
      _ = r * t * r⁻¹ := by rw [hqt']
      _ = t * (x₁ * x₂) ^ 2 := hrt

theorem fzc_sy3_a_notin (h : Ctx0 t L S x₁ x₂ lam rho) {a : G}
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) : a ∉ baseGrp x₁ x₂ ⊔ zpowers t := by
  intro ha
  have haW : a ∈ ctxW t x₁ x₂ := fzc_sy3_Wp_le_W h ha
  have htW : t ∈ ctxW t x₁ x₂ := fzc_sy2_t_mem h
  have hcomm : a * t = t * a := fzc_sy2_W_comm h a haW t htW
  have h1 : a * t * a⁻¹ = t := by rw [hcomm]; group
  have h2 : t * (x₁ * x₂) ^ 2 = t * 1 := by rw [← hat, h1, mul_one]
  exact fzc_sy3_z_ne_one h (mul_left_cancel h2)

theorem fzc_sy3_lam_a_Wp (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    lam * a * lam⁻¹ * a⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
  have haR : a ∈ fzR t x₁ x₂ := fzc_sy3_P_le_R hq ha
  have hlt : lam * t * lam⁻¹ = t := by
    rw [fzc_sy3_lam_t h hK hqt]; group
  have hlt' : lam⁻¹ * t * lam = t := by
    calc lam⁻¹ * t * lam = lam⁻¹ * (lam * t * lam⁻¹) * lam := by rw [hlt]
      _ = t := by group
  have hlz : lam * (x₁ * x₂) ^ 2 * lam⁻¹ = (x₁ * x₂) ^ 2 := fzc_sy3_lam_z h
  have hat' : (lam * a * lam⁻¹) * t * (lam * a * lam⁻¹)⁻¹ = t * (x₁ * x₂) ^ 2 := by
    calc (lam * a * lam⁻¹) * t * (lam * a * lam⁻¹)⁻¹
        = lam * a * (lam⁻¹ * t * lam) * a⁻¹ * lam⁻¹ := by group
      _ = lam * a * t * a⁻¹ * lam⁻¹ := by rw [hlt']
      _ = lam * (a * t * a⁻¹) * lam⁻¹ := by group
      _ = lam * (t * (x₁ * x₂) ^ 2) * lam⁻¹ := by rw [hat]
      _ = (lam * t * lam⁻¹) * (lam * (x₁ * x₂) ^ 2 * lam⁻¹) := by group
      _ = t * (x₁ * x₂) ^ 2 := by rw [hlt, hlz]
  have hzcomm : a⁻¹ * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * a⁻¹ := by
    have hc : a * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * a :=
      hq.R_cent_fourGrp a haR ((x₁ * x₂) ^ 2) fzc_sy3_z_mem_fourGrp
    calc a⁻¹ * (x₁ * x₂) ^ 2 = a⁻¹ * ((x₁ * x₂) ^ 2 * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * (x₁ * x₂) ^ 2) * a⁻¹ := by rw [← hc]
      _ = (x₁ * x₂) ^ 2 * a⁻¹ := by group
  have h1 : t = (a⁻¹ * t * a) * (x₁ * x₂) ^ 2 := by
    have hc : a * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * a :=
      hq.R_cent_fourGrp a haR ((x₁ * x₂) ^ 2) fzc_sy3_z_mem_fourGrp
    calc t = a⁻¹ * (a * t * a⁻¹) * a := by group
      _ = a⁻¹ * (t * (x₁ * x₂) ^ 2) * a := by rw [hat]
      _ = (a⁻¹ * t * a) * (x₁ * x₂) ^ 2 := by
            rw [show a⁻¹ * (t * (x₁ * x₂) ^ 2) * a = a⁻¹ * t * ((x₁ * x₂) ^ 2 * a) by group,
              show (x₁ * x₂) ^ 2 * a = a * (x₁ * x₂) ^ 2 from hc.symm]
            group
  have hait : a⁻¹ * t * a = t * (x₁ * x₂) ^ 2 := by
    have hz2 : ((x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 = 1 := by
      rw [← pow_two]; exact fzc_sy3_z_sq h
    calc a⁻¹ * t * a = (a⁻¹ * t * a) * (((x₁ * x₂) ^ 2) * ((x₁ * x₂) ^ 2)) := by
          rw [hz2, mul_one]
      _ = ((a⁻¹ * t * a) * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 := by group
      _ = t * (x₁ * x₂) ^ 2 := by rw [← h1]
  have hAz : (lam * a * lam⁻¹) * (x₁ * x₂) ^ 2 * (lam * a * lam⁻¹)⁻¹ = (x₁ * x₂) ^ 2 := by
    have hc := hq.R_cent_fourGrp (lam * a * lam⁻¹) (hq.lam_norm_R a haR) ((x₁ * x₂) ^ 2)
      fzc_sy3_z_mem_fourGrp
    rw [hc]; group
  have hd_cent : (lam * a * lam⁻¹ * a⁻¹) * t * (lam * a * lam⁻¹ * a⁻¹)⁻¹ = t := by
    have hzz : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := by
      rw [← pow_two]; exact fzc_sy3_z_sq h
    calc (lam * a * lam⁻¹ * a⁻¹) * t * (lam * a * lam⁻¹ * a⁻¹)⁻¹
        = (lam * a * lam⁻¹) * (a⁻¹ * t * a) * (lam * a * lam⁻¹)⁻¹ := by group
      _ = (lam * a * lam⁻¹) * (t * (x₁ * x₂) ^ 2) * (lam * a * lam⁻¹)⁻¹ := by rw [hait]
      _ = ((lam * a * lam⁻¹) * t * (lam * a * lam⁻¹)⁻¹) *
            ((lam * a * lam⁻¹) * (x₁ * x₂) ^ 2 * (lam * a * lam⁻¹)⁻¹) := by group
      _ = (t * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 := by rw [hat', hAz]
      _ = t := by
            rw [show t * (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 =
                t * ((x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2) by group, hzz, mul_one]
  have hdW : lam * a * lam⁻¹ * a⁻¹ ∈ ctxW t x₁ x₂ := by
    have hmem : lam * a * lam⁻¹ * a⁻¹ ∈ fzR t x₁ x₂ ⊓ invCent t := by
      refine Subgroup.mem_inf.mpr ⟨fzc_sy3_P_le_R hq
        ((fzP t x₁ x₂ rho).mul_mem (hq.lam_norm_P a ha) ((fzP t x₁ x₂ rho).inv_mem ha)), ?_⟩
      show lam * a * lam⁻¹ * a⁻¹ ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (lam * a * lam⁻¹ * a⁻¹) * t =
          ((lam * a * lam⁻¹ * a⁻¹) * t * (lam * a * lam⁻¹ * a⁻¹)⁻¹) *
            (lam * a * lam⁻¹ * a⁻¹) := by group
        _ = t * (lam * a * lam⁻¹ * a⁻¹) := by rw [hd_cent]
    rwa [hq.cent_R_t] at hmem
  exact fzc_sy3_P_W h hq hK hq4 hqt ht (lam * a * lam⁻¹ * a⁻¹)
    ((fzP t x₁ x₂ rho).mul_mem (hq.lam_norm_P a ha) ((fzP t x₁ x₂ rho).inv_mem ha)) hdW

theorem fzc_sy3_lam_a_E (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) {a : G} (ha : a ∈ fzP t x₁ x₂ rho)
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    lam * a * lam⁻¹ * a ∈ baseGrp x₁ x₂ := by
  by_contra hne
  have haR : a ∈ fzR t x₁ x₂ := fzc_sy3_P_le_R hq ha
  have haWp : a ∉ baseGrp x₁ x₂ ⊔ zpowers t := fzc_sy3_a_notin h hat
  have hdWp : lam * a * lam⁻¹ * a⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t :=
    fzc_sy3_lam_a_Wp h hq hK hq4 hqt ht ha hat
  have ha2t : a ^ 2 * t ∈ baseGrp x₁ x₂ := fzc_sy3_P_sq h hq hK hq4 hqt ht a ha haWp
  have hta2 : t * a ^ 2 ∈ baseGrp x₁ x₂ := by
    have h := fzc_sy3_t_comm_Et h ha2t
    rwa [← h]
  have htt : t * t = 1 := by rw [← pow_two]; exact fzc_sy2_t_sq h
  have htdE : t * (lam * a * lam⁻¹ * a⁻¹) ∉ baseGrp x₁ x₂ := by
    intro htd
    apply hne
    have h1 : (lam * a * lam⁻¹ * a⁻¹) * a ^ 2 ∈ baseGrp x₁ x₂ :=
      fzc_sy3_tE_mul h htd hta2
    rwa [show (lam * a * lam⁻¹ * a⁻¹) * a ^ 2 = lam * a * lam⁻¹ * a by group] at h1
  have hdE : lam * a * lam⁻¹ * a⁻¹ ∈ baseGrp x₁ x₂ :=
    ((fzc_sy3_Wp_mem h).1 hdWp).resolve_right htdE
  have hbP : rho * a * rho⁻¹ ∈ fzP t x₁ x₂ rho := hq.rho_norm_P a ha
  have hbpP : rho⁻¹ * a * rho ∈ fzP t x₁ x₂ rho := by
    rw [fzc_sy3_rho_inv_conj h a]
    exact hq.rho_norm_P _ hbP
  have hbWp : rho * a * rho⁻¹ ∉ baseGrp x₁ x₂ ⊔ zpowers t := by
    intro hb
    apply haWp
    have h1 : rho * (rho * a * rho⁻¹) * rho⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t :=
      fzc_sy3_rho_Wp h _ hb
    have h2 : rho * (rho * (rho * a * rho⁻¹) * rho⁻¹) * rho⁻¹ ∈
        baseGrp x₁ x₂ ⊔ zpowers t := fzc_sy3_rho_Wp h _ h1
    have h3 : rho⁻¹ * (rho * a * rho⁻¹) * rho ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
      rwa [fzc_sy3_rho_inv_conj h (rho * a * rho⁻¹)]
    rwa [show rho⁻¹ * (rho * a * rho⁻¹) * rho = a by group] at h3
  have hbpWp : rho⁻¹ * a * rho ∉ baseGrp x₁ x₂ ⊔ zpowers t := by
    intro hb'
    apply haWp
    have h1 : rho * (rho⁻¹ * a * rho) * rho⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t :=
      fzc_sy3_rho_Wp h _ hb'
    rwa [show rho * (rho⁻¹ * a * rho) * rho⁻¹ = a by group] at h1
  have hd1E : rho⁻¹ * (lam * a * lam⁻¹ * a⁻¹) * rho ∈ baseGrp x₁ x₂ := by
    rw [fzc_sy3_rho_inv_conj h (lam * a * lam⁻¹ * a⁻¹)]
    exact fzc_sy2_rho_nrm_E h _ (fzc_sy2_rho_nrm_E h _ hdE)
  have hd2E : rho * (lam * a * lam⁻¹ * a⁻¹) * rho⁻¹ ∈ baseGrp x₁ x₂ :=
    fzc_sy2_rho_nrm_E h _ hdE
  set e1 : G := (lam * a * lam⁻¹ * a⁻¹) *
      (a * (rho⁻¹ * (lam * a * lam⁻¹ * a⁻¹) * rho) * a⁻¹) *
      ((a * (rho⁻¹ * a * rho)) * (rho * (lam * a * lam⁻¹ * a⁻¹) * rho⁻¹) *
        (a * (rho⁻¹ * a * rho))⁻¹) with he1_def
  have he1E : e1 ∈ baseGrp x₁ x₂ := by
    rw [he1_def]
    refine (baseGrp x₁ x₂).mul_mem ((baseGrp x₁ x₂).mul_mem hdE
      (fzc_sy3_R_nrm_E h hq hK hq4 hqt a haR _ hd1E)) ?_
    exact fzc_sy3_R_nrm_E h hq hK hq4 hqt (a * (rho⁻¹ * a * rho))
      (fzc_sy3_P_le_R hq ((fzP t x₁ x₂ rho).mul_mem ha hbpP)) _ hd2E
  have hdb : lam * (rho * a * rho⁻¹) * lam⁻¹ =
      (rho⁻¹ * (lam * a * lam⁻¹ * a⁻¹) * rho) * (rho⁻¹ * a * rho) := by
    calc lam * (rho * a * rho⁻¹) * lam⁻¹
        = (lam * rho * lam⁻¹) * (lam * a * lam⁻¹) * (lam * rho * lam⁻¹)⁻¹ := by group
      _ = rho⁻¹ * (lam * a * lam⁻¹) * rho := by rw [h.lam_rho]; group
      _ = (rho⁻¹ * (lam * a * lam⁻¹ * a⁻¹) * rho) * (rho⁻¹ * a * rho) := by
            rw [show lam * a * lam⁻¹ = (lam * a * lam⁻¹ * a⁻¹) * a by group]
            group
  have hdb' : lam * (rho⁻¹ * a * rho) * lam⁻¹ =
      (rho * (lam * a * lam⁻¹ * a⁻¹) * rho⁻¹) * (rho * a * rho⁻¹) := by
    have hlri : lam * rho⁻¹ * lam⁻¹ = rho := by
      calc lam * rho⁻¹ * lam⁻¹ = (lam * rho * lam⁻¹)⁻¹ := by group
        _ = (rho⁻¹)⁻¹ := by rw [h.lam_rho]
        _ = rho := by group
    calc lam * (rho⁻¹ * a * rho) * lam⁻¹
        = (lam * rho⁻¹ * lam⁻¹) * (lam * a * lam⁻¹) * (lam * rho⁻¹ * lam⁻¹)⁻¹ := by group
      _ = rho * (lam * a * lam⁻¹) * rho⁻¹ := by
            rw [show (lam * rho⁻¹ * lam⁻¹) * (lam * a * lam⁻¹) * (lam * rho⁻¹ * lam⁻¹)⁻¹ =
                rho * (lam * a * lam⁻¹) * rho⁻¹ from by rw [hlri]]
      _ = (rho * (lam * a * lam⁻¹ * a⁻¹) * rho⁻¹) * (rho * a * rho⁻¹) := by
            rw [show lam * a * lam⁻¹ = (lam * a * lam⁻¹ * a⁻¹) * a by group]
            group
  set n : G := a * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho) with hn_def
  have hnWp : n ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
    have hnorm := fzc_sy3_norm (R := fzP t x₁ x₂ rho)
      (N := baseGrp x₁ x₂ ⊔ zpowers t) (fzc_sy3_Wp_le_P h hq ht)
      (fun r hr w hw => fzc_sy3_R_Wp h hq hK hq4 hqt r (fzc_sy3_P_le_R hq hr) w hw)
      hq.rho_norm_P (fzc_sy3_rho_Wp h)
      (fun x hx y hy =>
        fzc_sy3_R_comm h hq hK hq4 hqt x (fzc_sy3_P_le_R hq hx) y (fzc_sy3_P_le_R hq hy))
      (fzc_sy3_rho3 h) a (by rw [fzc_sy3_P_rho_eq h hq hK hqt ht]; exact ha)
    rw [hn_def]
    exact hnorm
  have hA : lam * n * lam⁻¹ = e1 * (a * (rho⁻¹ * a * rho) * (rho * a * rho⁻¹)) := by
    rw [hn_def, he1_def]
    rw [show lam * (a * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho)) * lam⁻¹ =
        (lam * a * lam⁻¹) * (lam * (rho * a * rho⁻¹) * lam⁻¹) *
          (lam * (rho⁻¹ * a * rho) * lam⁻¹) by group,
      show lam * a * lam⁻¹ = (lam * a * lam⁻¹ * a⁻¹) * a by group, hdb, hdb']
    group
  have hB : lam * n * lam⁻¹ * n⁻¹ ∈ baseGrp x₁ x₂ := by
    rcases (fzc_sy3_Wp_mem h).1 hnWp with hnE | htnE
    · exact (baseGrp x₁ x₂).mul_mem (fzc_sy3_lam_E h _ hnE) ((baseGrp x₁ x₂).inv_mem hnE)
    · set e : G := t * n with he_def
      have heE : e ∈ baseGrp x₁ x₂ := by rw [he_def]; exact htnE
      have hn_eq : n = t * e := by rw [he_def, ← mul_assoc, htt, one_mul]
      have hlt : lam * t * lam⁻¹ = t := by rw [fzc_sy3_lam_t h hK hqt]; group
      have hlamn : lam * n * lam⁻¹ = t * (lam * e * lam⁻¹) := by
        rw [hn_eq, show lam * (t * e) * lam⁻¹ =
            (lam * t * lam⁻¹) * (lam * e * lam⁻¹) by group, hlt]
      have hlameE : lam * e * lam⁻¹ ∈ baseGrp x₁ x₂ := fzc_sy3_lam_E h e heE
      have hninv : n⁻¹ = t * e⁻¹ := by
        rw [hn_eq]
        calc (t * e)⁻¹ = e⁻¹ * t⁻¹ := by group
          _ = e⁻¹ * t := by rw [inv_eq_of_mul_eq_one_right htt]
          _ = t * e⁻¹ :=
            (S4A.pt_comm_base h t h.hyp.mem_twoCore e⁻¹ ((baseGrp x₁ x₂).inv_mem heE)).symm
      rw [hlamn, hninv]
      refine fzc_sy3_tE_mul h ?_ ?_
      · rw [← mul_assoc, htt, one_mul]; exact hlameE
      · rw [← mul_assoc, htt, one_mul]; exact (baseGrp x₁ x₂).inv_mem heE
  have hab'bn : (a * (rho⁻¹ * a * rho) * (rho * a * rho⁻¹)) * n⁻¹ ∈ baseGrp x₁ x₂ := by
    have h1 : a * (rho⁻¹ * a * rho) * (rho * a * rho⁻¹) = e1⁻¹ * (lam * n * lam⁻¹) := by
      rw [hA]; group
    rw [h1]
    rw [show (e1⁻¹ * (lam * n * lam⁻¹)) * n⁻¹ = e1⁻¹ * ((lam * n * lam⁻¹) * n⁻¹) by group]
    exact (baseGrp x₁ x₂).mul_mem ((baseGrp x₁ x₂).inv_mem he1E) hB
  have hcommE : (rho⁻¹ * a * rho) * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho)⁻¹ *
      (rho * a * rho⁻¹)⁻¹ ∈ baseGrp x₁ x₂ := by
    have h1 : (rho⁻¹ * a * rho) * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho)⁻¹ *
        (rho * a * rho⁻¹)⁻¹ =
        a⁻¹ * ((a * (rho⁻¹ * a * rho) * (rho * a * rho⁻¹)) * n⁻¹) * a := by
      rw [hn_def]
      simp only [mul_inv_rev, inv_inv]
      group
    rw [h1]
    simpa using fzc_sy3_R_nrm_E h hq hK hq4 hqt a⁻¹ ((fzR t x₁ x₂).inv_mem haR) _ hab'bn
  have hbpbinv : (rho⁻¹ * a * rho) * (rho * a * rho⁻¹)⁻¹ ∉
      baseGrp x₁ x₂ ⊔ zpowers t := by
    intro hu
    apply haWp
    have h1 : rho * ((rho⁻¹ * a * rho) * (rho * a * rho⁻¹)⁻¹) * rho⁻¹ ∈
        baseGrp x₁ x₂ ⊔ zpowers t := fzc_sy3_rho_Wp h _ hu
    have h2mem : rho * (rho * ((rho⁻¹ * a * rho) * (rho * a * rho⁻¹)⁻¹) * rho⁻¹) *
        rho⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t := fzc_sy3_rho_Wp h _ h1
    have heq : rho * (rho * ((rho⁻¹ * a * rho) * (rho * a * rho⁻¹)⁻¹) * rho⁻¹) *
        rho⁻¹ = rho * a * rho⁻¹ * a⁻¹ := by
      have h2 : rho * rho = rho⁻¹ := by
        have h3 : rho * rho * rho = 1 := by rw [← pow_two, ← pow_succ, fzc_sy3_rho3 h]
        exact mul_eq_one_iff_eq_inv.mp h3
      have hi3 : (rho⁻¹) ^ 3 = 1 := by rw [inv_pow, fzc_sy3_rho3 h, inv_one]
      rw [show rho * (rho * ((rho⁻¹ * a * rho) * (rho * a * rho⁻¹)⁻¹) * rho⁻¹) * rho⁻¹ =
          rho * a * (rho * rho) * a⁻¹ * (rho⁻¹) ^ 3 by group]
      rw [h2, hi3, mul_one]
    exact fzc_sy3_rho_PWp h hq hK hq4 hqt ht a ha (heq ▸ h2mem)
  exact (fzc_sy3_P_comm_tE h hq hK hq4 hqt ht (rho⁻¹ * a * rho) hbpP (rho * a * rho⁻¹) hbP
    hbpWp hbWp hbpbinv) hcommE

end CFSG.OddStandard.SmallF3.FritzII
