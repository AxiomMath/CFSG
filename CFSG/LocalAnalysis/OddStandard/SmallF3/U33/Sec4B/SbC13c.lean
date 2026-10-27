module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13T
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17CosB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

private theorem c13_O_le_M (t tau x₁ x₂ : G) : ctxO t tau x₁ x₂ ≤ ctxM t tau x₁ x₂ := by
  rw [ctxO, CFSG.Open.pCoreOf]
  exact Subgroup.map_subtype_le _

private theorem fourGrp_le_baseGrp (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [fourGrp, baseGrp, Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact Subgroup.pow_mem (baseGrp x₁ x₂)
      (Subgroup.subset_closure (by simp)) 2
  · exact Subgroup.pow_mem (baseGrp x₁ x₂)
      (Subgroup.mul_mem (baseGrp x₁ x₂) (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) 2

private theorem baseGrp_comm (hc : Ctx13A t L S x₁ x₂ lam rho tau om) {a b : G}
    (ha : a ∈ baseGrp x₁ x₂) (hb : b ∈ baseGrp x₁ x₂) : a * b = b * a := by
  haveI : IsMulCommutative ↥(baseGrp x₁ x₂) := hc.wreath.baseGrp_eq.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(baseGrp x₁ x₂)) ⟨b, hb⟩)

private theorem om_conj_commutator (hc : Ctx13B t L S x₁ x₂ lam rho tau om) {b : G}
    (hb : b ∈ ctxQ t tau x₁ x₂ rho) :
    om * (b * om * b⁻¹ * om⁻¹) * om⁻¹ = (b * om * b⁻¹ * om⁻¹)⁻¹ := by
  have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right hc.om_sq
  rw [hom_inv]
  have hkey : om * (b * om * b⁻¹ * om) * om = om * b * om * b⁻¹ := by
    calc om * (b * om * b⁻¹ * om) * om = om * b * om * b⁻¹ * (om * om) := by group
      _ = om * b * om * b⁻¹ := by rw [hc.om_sq, mul_one]
  have hkey2 : om * b * om * b⁻¹ = (b * om * b⁻¹ * om)⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    calc (b * om * b⁻¹ * om) * (om * b * om * b⁻¹)
        = b * om * b⁻¹ * (om * om) * b * om * b⁻¹ := by group
      _ = b * om * b⁻¹ * b * om * b⁻¹ := by rw [hc.om_sq, mul_one]
      _ = b * (om * om) * b⁻¹ := by group
      _ = 1 := by rw [hc.om_sq]; group
  rw [hkey, hkey2]

theorem c13_mem_O (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    t ∈ ctxO t tau x₁ x₂ ∧ tau ∈ ctxO t tau x₁ x₂ ∧ om ∈ ctxO t tau x₁ x₂ := by
  have htX : t ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have htauX : tau ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  refine ⟨hc.R_le_O (hc.X_le_R htX), hc.R_le_O (hc.X_le_R htauX), ?_⟩
  have hom := hc.om_mem
  rw [ctxCO] at hom
  exact hom.1

theorem c13_cent_V (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    ∀ g ∈ ctxO t tau x₁ x₂, ∀ v ∈ fourGrp x₁ x₂, g * v = v * g := by
  intro g hg v hv
  have hg' := hg
  rw [hc.O_cent] at hg'
  exact ((Subgroup.mem_centralizer_iff.mp hg'.2) v hv).symm

theorem c13_t_data (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    t ∈ ctxM t tau x₁ x₂ ∧ t * t = 1 ∧ t * rho = rho * t := by
  refine ⟨c13_O_le_M t tau x₁ x₂ (c13_mem_O hc).1, S4A.t_mul_self hc.hyp, ?_⟩
  exact (S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp hc.rho_mem)).symm

theorem c13_tau_data (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    tau ∈ ctxM t tau x₁ x₂ ∧ tau * tau = 1 ∧ tau * rho = rho * tau := by
  refine ⟨c13_O_le_M t tau x₁ x₂ (c13_mem_O hc).2.1, ?_, hc.tau_rho⟩
  simpa [pow_two] using hc.l44.1

theorem c13_om_data (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    om ∈ ctxM t tau x₁ x₂ ∧ om * om = 1 ∧ om * rho = rho * om := by
  refine ⟨c13_O_le_M t tau x₁ x₂ (c13_mem_O hc).2.2, hc.om_sq, ?_⟩
  have hom := hc.om_mem
  rw [ctxCO] at hom
  exact Subgroup.mem_centralizer_singleton_iff.mp hom.2

theorem c13_triv_YV (hc : Ctx13B t L S x₁ x₂ lam rho tau om) {g : G}
    (hg : g ∈ ctxM t tau x₁ x₂) (hg2 : g * g = 1) (hgρ : g * rho = rho * g) :
    ∀ x ∈ ctxYq t tau x₁ x₂ rho, x⁻¹ * (g * x * g⁻¹) ∈ fourGrp x₁ x₂ := by
  exact hc.fpf_YV.trivial_action hgρ hg2
    (fun x hx => hc.normal_Y.2 g hg x hx) (fun x hx => hc.normal_V.2 g hg x hx)

theorem c13_triv_QY (hc : Ctx13B t L S x₁ x₂ lam rho tau om) {g : G}
    (hg : g ∈ ctxM t tau x₁ x₂) (hg2 : g * g = 1) (hgρ : g * rho = rho * g) :
    ∀ x ∈ ctxQ t tau x₁ x₂ rho, x⁻¹ * (g * x * g⁻¹) ∈ ctxYq t tau x₁ x₂ rho := by
  exact hc.fpf_QY.trivial_action hgρ hg2
    (fun x hx => hc.normal_Q.2 g hg x hx) (fun x hx => hc.normal_Y.2 g hg x hx)

theorem c13_tau_cent_Y (hc : Ctx13B t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ ctxYq t tau x₁ x₂ rho, tau * a = a * tau := by
  have hA := hc.toCtx13A
  have hom := c13_om_data hA
  have ht := c13_t_data hA
  have hV : CFSG.Open.IsElemAbelian 2 (fourGrp x₁ x₂) := hc.wreath.fourGrp_eq_omega.2.1
  haveI : IsMulCommutative ↥(fourGrp x₁ x₂) := hV.1
  have hom_V : ∀ v ∈ fourGrp x₁ x₂, om * v = v * om :=
    c13_cent_V hA om (c13_mem_O hA).2.2
  have ht_V : ∀ v ∈ fourGrp x₁ x₂, t * v = v * t := c13_cent_V hA t (c13_mem_O hA).1
  have hVcomm : ∀ v ∈ fourGrp x₁ x₂, ∀ w ∈ fourGrp x₁ x₂, v * w = w * v :=
    fun v hv w hw =>
      congrArg Subtype.val (mul_comm' (⟨v, hv⟩ : ↥(fourGrp x₁ x₂)) ⟨w, hw⟩)
  have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right hc.om_sq
  have htau2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  have htau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right htau2
  have htau_eq : tau = t * om * t * om := by
    have h := hc.t_om
    rw [hom_inv] at h
    have h2 : t * om * t * om = tau := by
      calc t * om * t * om = t * (om * t * om) := by group
        _ = t * (t * tau) := by rw [h]
        _ = (t * t) * tau := by group
        _ = tau := by rw [ht.2.1, one_mul]
    exact h2.symm
  intro a ha
  set e : G := a⁻¹ * (om * a * om⁻¹) with he_def
  set f : G := a⁻¹ * (t * a * t⁻¹) with hf_def
  have heV : e ∈ fourGrp x₁ x₂ := by
    rw [he_def]
    exact c13_triv_YV hc hom.1 hc.om_sq hom.2.2 a ha
  have hfV : f ∈ fourGrp x₁ x₂ := by
    rw [hf_def]
    exact c13_triv_YV hc ht.1 ht.2.1 ht.2.2 a ha
  have he2 : e * e = 1 := by
    have := hV.2 e heV
    rwa [pow_two] at this
  have hf2 : f * f = 1 := by
    have := hV.2 f hfV
    rwa [pow_two] at this
  have hef : e * f = f * e := hVcomm e heV f hfV
  have ht_e : t * e * t⁻¹ = e := by rw [ht_V e heV]; group
  have ht_f : t * f * t⁻¹ = f := by rw [ht_V f hfV]; group
  have hom_e : om * e * om⁻¹ = e := by rw [hom_V e heV]; group
  have hom_f : om * f * om⁻¹ = f := by rw [hom_V f hfV]; group
  have home : om * a * om⁻¹ = a * e := by rw [he_def]; group
  have htf : t * a * t⁻¹ = a * f := by rw [hf_def]; group
  have hfour : f * e * f * e = 1 := by
    rw [show f * e * f * e = f * (e * f) * e by group, hef]
    rw [show f * (f * e) * e = (f * f) * (e * e) by group, hf2, he2]
    group
  have step1 : om * a * om⁻¹ = a * e := home
  have step2 : t * (a * e) * t⁻¹ = (a * f) * e := by
    calc t * (a * e) * t⁻¹ = (t * a * t⁻¹) * (t * e * t⁻¹) := by group
      _ = (a * f) * e := by rw [htf, ht_e]
  have step3 : om * ((a * f) * e) * om⁻¹ = (a * e) * f * e := by
    calc om * ((a * f) * e) * om⁻¹
        = (om * a * om⁻¹) * (om * f * om⁻¹) * (om * e * om⁻¹) := by group
      _ = (a * e) * f * e := by rw [home, hom_f, hom_e]
  have step4 : t * ((a * e) * f * e) * t⁻¹ = a := by
    calc t * ((a * e) * f * e) * t⁻¹
        = (t * a * t⁻¹) * (t * e * t⁻¹) * (t * f * t⁻¹) * (t * e * t⁻¹) := by group
      _ = (a * f) * e * f * e := by rw [htf, ht_e, ht_f]
      _ = a := by
          rw [show (a * f) * e * f * e = a * (f * e * f * e) by group, hfour, mul_one]
  have hmain : tau * a * tau⁻¹ = a := by
    rw [htau_eq]
    calc (t * om * t * om) * a * (t * om * t * om)⁻¹
        = t * (om * (t * (om * a * om⁻¹) * t⁻¹) * om⁻¹) * t⁻¹ := by group
      _ = t * (om * (t * (a * e) * t⁻¹) * om⁻¹) * t⁻¹ := by rw [step1]
      _ = t * (om * ((a * f) * e) * om⁻¹) * t⁻¹ := by rw [step2]
      _ = t * ((a * e) * f * e) * t⁻¹ := by rw [step3]
      _ = a := step4
  calc tau * a = (tau * a * tau⁻¹) * tau := by group
    _ = a * tau := by rw [hmain]

theorem c13_om_nontriv (hc : Ctx13B t L S x₁ x₂ lam rho tau om) :
    ∃ a ∈ ctxQ t tau x₁ x₂ rho, a⁻¹ * (om * a * om⁻¹) ∉ fourGrp x₁ x₂ := by
  refine ⟨x₁, hc.base_le_Q (Subgroup.subset_closure (by simp)), ?_⟩
  intro hx1V
  have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right hc.om_sq
  have hx1V' : x₁⁻¹ * (om * x₁ * om) ∈ fourGrp x₁ x₂ := by simpa [hom_inv] using hx1V
  have hwB : om * x₁ * om ∈ baseGrp x₁ x₂ := by
    have hmem : x₁ * (x₁⁻¹ * (om * x₁ * om)) ∈ baseGrp x₁ x₂ :=
      Subgroup.mul_mem (baseGrp x₁ x₂) (Subgroup.subset_closure (by simp))
        (fourGrp_le_baseGrp x₁ x₂ hx1V')
    convert hmem using 1
    group
  have hB_le_C : baseGrp x₁ x₂ ≤ centralizer ({t} : Set G) := by
    rw [← l12_CQ_t hc.toCtx11]
    exact inf_le_right
  have hx1C : x₁ ∈ centralizer ({t} : Set G) :=
    hB_le_C (Subgroup.subset_closure (by simp))
  have htx : t * x₁ = x₁ * t := (Subgroup.mem_centralizer_singleton_iff.mp hx1C).symm
  have hcw : t * (om * x₁ * om) = (om * x₁ * om) * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hB_le_C hwB)).symm
  have hL : om * (t * (om * x₁ * om)) * om = (om * t * om) * x₁ := by
    calc om * (t * (om * x₁ * om)) * om
        = (om * t) * (om * x₁) * (om * om) := by group
      _ = (om * t) * (om * x₁) := by rw [hc.om_sq, mul_one]
      _ = (om * t * om) * x₁ := by group
  have hR : om * ((om * x₁ * om) * t) * om = x₁ * (om * t * om) := by
    calc om * ((om * x₁ * om) * t) * om
        = (om * om) * x₁ * (om * t * om) := by group
      _ = x₁ * (om * t * om) := by rw [hc.om_sq, one_mul]
  have hconj_omt : (om * t * om) * x₁ = x₁ * (om * t * om) := by
    rw [← hL, hcw, hR]
  have htom : om * t * om = t * tau := by
    have h := hc.t_om
    rwa [hom_inv] at h
  have hconj : (t * tau) * x₁ = x₁ * (t * tau) := by rw [← htom]; exact hconj_omt
  have htau_x1 : tau * x₁ = x₁ * tau := by
    have h : t * (tau * x₁) = t * (x₁ * tau) := by
      calc t * (tau * x₁) = (t * tau) * x₁ := by group
        _ = x₁ * (t * tau) := hconj
        _ = (x₁ * t) * tau := by group
        _ = (t * x₁) * tau := by rw [← htx]
        _ = t * (x₁ * tau) := by group
    exact mul_left_cancel h
  have hx1_inv : x₁⁻¹ = x₁ := by
    have h := hc.tau_x₁
    rw [htau_x1] at h
    rw [mul_assoc, mul_inv_cancel, mul_one] at h
    exact h.symm
  have hx1sq : x₁ ^ 2 = 1 := by
    rw [pow_two]
    calc x₁ * x₁ = x₁⁻¹ * x₁ := by rw [hx1_inv]
      _ = 1 := inv_mul_cancel x₁
  have hdvd : orderOf x₁ ∣ 2 := orderOf_dvd_of_pow_eq_one hx1sq
  rw [hc.wreath.ord_x₁] at hdvd
  exact absurd hdvd (by norm_num)

theorem c13_om_cent_Y (hc : Ctx13B t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ ctxYq t tau x₁ x₂ rho, om * a = a * om := by
  have hom := c13_om_data hc.toCtx13A
  have hQ_om : ∀ a ∈ ctxQ t tau x₁ x₂ rho, om * a * om⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    fun a ha => hc.normal_Q.2 om hom.1 a ha
  have hcomm := comm_zpowers_inv (A := ctxQ t tau x₁ x₂ rho) (g := om)
    hc.Q_comm hc.om_sq hQ_om
  have hC_le_Y : ⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆ ≤ ctxYq t tau x₁ x₂ rho := by
    intro n hn
    obtain ⟨a, haQ, rfl⟩ := (hcomm.1 n).mp hn
    have hga : om * a * om⁻¹ ∈ ctxQ t tau x₁ x₂ rho := hQ_om a haQ
    have he : a⁻¹ * (om * a * om⁻¹) ∈ ctxYq t tau x₁ x₂ rho :=
      c13_triv_QY hc hom.1 hc.om_sq hom.2.2 a haQ
    have hn_eq : (a⁻¹ * (om * a * om⁻¹))⁻¹ = a * om * a⁻¹ * om⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      have hc1 : (om * a * om⁻¹)⁻¹ * a = a * (om * a * om⁻¹)⁻¹ :=
        hc.Q_comm _ (Subgroup.inv_mem _ hga) a haQ
      rw [hc1]
      group
    rw [← hn_eq]
    exact Subgroup.inv_mem _ he
  have hCρ : ∀ x ∈ ⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆,
      rho * x * rho⁻¹ ∈ ⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆ := by
    intro x hx
    obtain ⟨a, haQ, rfl⟩ := (hcomm.1 x).mp hx
    have hra : rho * a * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      hc.normal_Q.2 rho (l12_rho_lam_mem_M hc.toCtx11).1 a haQ
    have hrom : rho * om = om * rho := hom.2.2.symm
    have hrom_conj : rho * om * rho⁻¹ = om := by rw [hrom]; group
    have hromi_conj : rho * om⁻¹ * rho⁻¹ = om⁻¹ := by
      rw [show rho * om⁻¹ * rho⁻¹ = (rho * om * rho⁻¹)⁻¹ by group, hrom_conj]
    have hrai_conj : rho * a⁻¹ * rho⁻¹ = (rho * a * rho⁻¹)⁻¹ := by group
    refine (hcomm.1 _).mpr ⟨rho * a * rho⁻¹, hra, ?_⟩
    calc rho * (a * om * a⁻¹ * om⁻¹) * rho⁻¹
        = (rho * a * rho⁻¹) * (rho * om * rho⁻¹) * (rho * a⁻¹ * rho⁻¹)
            * (rho * om⁻¹ * rho⁻¹) := by group
      _ = (rho * a * rho⁻¹) * om * (rho * a * rho⁻¹)⁻¹ * om⁻¹ := by
            rw [hrom_conj, hromi_conj, hrai_conj]
  rcases hc.fpf_YV.sup_eq hC_le_Y hCρ with hCV | hcover
  · exfalso
    obtain ⟨a, haQ, haV⟩ := c13_om_nontriv hc
    have hmemC : a * om * a⁻¹ * om⁻¹ ∈ ⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆ :=
      (hcomm.1 _).mpr ⟨a, haQ, rfl⟩
    have hga : om * a * om⁻¹ ∈ ctxQ t tau x₁ x₂ rho := hQ_om a haQ
    have hn_eq : (a⁻¹ * (om * a * om⁻¹))⁻¹ = a * om * a⁻¹ * om⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      have hc1 : (om * a * om⁻¹)⁻¹ * a = a * (om * a * om⁻¹)⁻¹ :=
        hc.Q_comm _ (Subgroup.inv_mem _ hga) a haQ
      rw [hc1]
      group
    have hmemV : a⁻¹ * (om * a * om⁻¹) ∈ fourGrp x₁ x₂ := by
      have hinv := Subgroup.inv_mem _ (hCV hmemC)
      rwa [← hn_eq, inv_inv] at hinv
    exact haV hmemV
  · intro a haY
    obtain ⟨c, hcC, hcv⟩ := hcover a haY
    have hcY : c ∈ ctxYq t tau x₁ x₂ rho := hC_le_Y hcC
    have hc2 : c * c = 1 := by
      have := hc.Y_elem.2 c hcY
      rwa [pow_two] at this
    have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
    have hvV : c⁻¹ * a ∈ fourGrp x₁ x₂ := hcv
    have hom_c : om * c * om⁻¹ = c⁻¹ := by
      obtain ⟨b, hbQ, hbc⟩ := (hcomm.1 c).mp hcC
      rw [hbc]
      exact om_conj_commutator hc hbQ
    have hom_c' : om * c * om⁻¹ = c := by rw [hom_c, hci]
    have hom_v : om * (c⁻¹ * a) * om⁻¹ = c⁻¹ * a := by
      have := c13_cent_V hc.toCtx13A om (c13_mem_O hc.toCtx13A).2.2 (c⁻¹ * a) hvV
      rw [this]; group
    have hmain : om * a * om⁻¹ = a := by
      calc om * a * om⁻¹ = om * (c * (c⁻¹ * a)) * om⁻¹ := by group
        _ = (om * c * om⁻¹) * (om * (c⁻¹ * a) * om⁻¹) := by group
        _ = c * (c⁻¹ * a) := by rw [hom_c', hom_v]
        _ = a := by group
    calc om * a = (om * a * om⁻¹) * om := by group
      _ = a * om := by rw [hmain]

theorem c13_B_sq_one (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    ∀ b ∈ baseGrp x₁ x₂, b ^ 2 = 1 → b ∈ fourGrp x₁ x₂ := by
  intro b hb hb2
  rw [hc.wreath.fourGrp_eq_omega.1]
  exact Subgroup.subset_closure ⟨hb, hb2⟩

theorem c13_Q_eq_sup (hc : Ctx13B t L S x₁ x₂ lam rho tau om) :
    baseGrp x₁ x₂ ⊓ ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ ∧
      ctxQ t tau x₁ x₂ rho = baseGrp x₁ x₂ ⊔ ctxYq t tau x₁ x₂ rho := by
  have hBY_comm : ∀ h ∈ baseGrp x₁ x₂, ∀ k ∈ ctxYq t tau x₁ x₂ rho, h * k = k * h :=
    fun h hh k hk => hc.Q_comm h (hc.base_le_Q hh) k (ctxYq_le_ctxQ hk)
  have hinf : baseGrp x₁ x₂ ⊓ ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ := by
    apply le_antisymm
    · intro b hb
      exact c13_B_sq_one hc.toCtx13A b hb.1 ((mem_ctxYq_iff hc.q_iso b).mp hb.2).2
    · intro v hv
      exact ⟨fourGrp_le_baseGrp x₁ x₂ hv, hc.V_le_Y hv⟩
  refine ⟨hinf, ?_⟩
  have hcard : Nat.card ↥(baseGrp x₁ x₂ ⊔ ctxYq t tau x₁ x₂ rho) = 64 := by
    have h := card_sup_mul_card_inf (H := baseGrp x₁ x₂)
      (K := ctxYq t tau x₁ x₂ rho) hBY_comm
    rw [hinf, hc.wreath.fourGrp_eq_omega.2.2, hc.wreath.baseGrp_eq.2.2,
      card_ctxYq hc.q_iso] at h
    omega
  exact (Subgroup.eq_of_le_of_card_ge
    (H := baseGrp x₁ x₂ ⊔ ctxYq t tau x₁ x₂ rho) (K := ctxQ t tau x₁ x₂ rho)
    (sup_le hc.base_le_Q ctxYq_le_ctxQ)
    (by rw [IsZ4Z4E4.card hc.q_iso, hcard])).symm

theorem c13_tau_inv_B (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    ∀ b ∈ baseGrp x₁ x₂, tau * b * tau⁻¹ = b⁻¹ := by
  intro b hb
  refine Subgroup.closure_induction (p := fun b _ => tau * b * tau⁻¹ = b⁻¹) ?_ ?_ ?_ ?_ hb
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hc.tau_x₁
    · exact hc.tau_x₂
  · simp
  · intro y z hy hz ihy ihz
    have hyz : y * z = z * y := baseGrp_comm hc hy hz
    calc tau * (y * z) * tau⁻¹ = (tau * y * tau⁻¹) * (tau * z * tau⁻¹) := by group
      _ = y⁻¹ * z⁻¹ := by rw [ihy, ihz]
      _ = (y * z)⁻¹ := by rw [hyz]; group
  · intro y hy ihy
    rw [show tau * y⁻¹ * tau⁻¹ = (tau * y * tau⁻¹)⁻¹ by group, ihy]

theorem c13_tau_inv_Q (hc : Ctx13B t L S x₁ x₂ lam rho tau om)
    (htc : ∀ a ∈ ctxYq t tau x₁ x₂ rho, tau * a = a * tau) :
    ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹ := by
  have hBY_comm : ∀ h ∈ baseGrp x₁ x₂, ∀ k ∈ ctxYq t tau x₁ x₂ rho, h * k = k * h :=
    fun h hh k hk => hc.Q_comm h (hc.base_le_Q hh) k (ctxYq_le_ctxQ hk)
  intro a ha
  have hsplit : a ∈ baseGrp x₁ x₂ ⊔ ctxYq t tau x₁ x₂ rho := by
    rw [← (c13_Q_eq_sup hc).2]
    exact ha
  obtain ⟨b, hbB, y, hyY, hby⟩ := exists_mul_of_sup (H := baseGrp x₁ x₂)
    (K := ctxYq t tau x₁ x₂ rho) hBY_comm hsplit
  rw [hby]
  have hb_inv : tau * b * tau⁻¹ = b⁻¹ := c13_tau_inv_B hc.toCtx13A b hbB
  have hy_inv : tau * y * tau⁻¹ = y := by rw [htc y hyY]; group
  have hy2 : y ^ 2 = 1 := ((mem_ctxYq_iff hc.q_iso y).mp hyY).2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at hy2)
  have hbQ : b ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q hbB
  have hyQ : y ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ hyY
  calc tau * (b * y) * tau⁻¹ = (tau * b * tau⁻¹) * (tau * y * tau⁻¹) := by group
    _ = b⁻¹ * y := by rw [hb_inv, hy_inv]
    _ = (b * y)⁻¹ := by
        rw [mul_inv_rev, hyi]
        exact (hc.Q_comm y hyQ b⁻¹ (Subgroup.inv_mem _ hbQ)).symm

theorem c13_Y_cent (hc : Ctx13B t L S x₁ x₂ lam rho tau om)
    (htc : ∀ a ∈ ctxYq t tau x₁ x₂ rho, tau * a = a * tau) :
    ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = fourGrp x₁ x₂ ∧
      ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) = fourGrp x₁ x₂ := by
  have hfirst : ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = fourGrp x₁ x₂ := by
    apply le_antisymm
    · intro a ha
      have haQ : a ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ ha.1
      have haB : a ∈ baseGrp x₁ x₂ := by
        have hmem : a ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := ⟨haQ, ha.2⟩
        rwa [l12_CQ_t hc.toCtx11] at hmem
      exact c13_B_sq_one hc.toCtx13A a haB ((mem_ctxYq_iff hc.q_iso a).mp ha.1).2
    · intro v hv
      exact ⟨hc.V_le_Y hv, Subgroup.mem_centralizer_singleton_iff.mpr
        (c13_cent_V hc.toCtx13A t (c13_mem_O hc.toCtx13A).1 v hv).symm⟩
  refine ⟨hfirst, ?_⟩
  have hmeet : ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) =
      ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := by
    apply le_antisymm
    · intro a ha
      refine ⟨ha.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h2 : a * (t * tau) = (t * tau) * a :=
        Subgroup.mem_centralizer_singleton_iff.mp ha.2
      have h3 : a * t * tau = t * a * tau := by
        calc a * t * tau = a * (t * tau) := by group
          _ = (t * tau) * a := h2
          _ = t * (a * tau) := by rw [mul_assoc, htc a ha.1]
          _ = t * a * tau := by group
      have h : a * t = t * a := mul_right_cancel h3
      exact h
    · intro a ha
      refine ⟨ha.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h : a * t = t * a := Subgroup.mem_centralizer_singleton_iff.mp ha.2
      calc a * (t * tau) = a * t * tau := by group
        _ = t * a * tau := by rw [h]
        _ = t * (a * tau) := by group
        _ = t * (tau * a) := by rw [← htc a ha.1]
        _ = (t * tau) * a := by group
  rw [hmeet]
  exact hfirst

theorem c13_Y_comm_of (hc : Ctx13B t L S x₁ x₂ lam rho tau om) {g : G}
    (hg : g ∈ ctxM t tau x₁ x₂) (hg2 : g * g = 1) (hgρ : g * rho = rho * g)
    (hcent : ctxYq t tau x₁ x₂ rho ⊓ centralizer ({g} : Set G) = fourGrp x₁ x₂) :
    ⁅ctxYq t tau x₁ x₂ rho, zpowers g⁆ = fourGrp x₁ x₂ := by
  haveI : IsMulCommutative ↥(ctxYq t tau x₁ x₂ rho) := hc.Y_elem.1
  have hYcomm : ∀ a ∈ ctxYq t tau x₁ x₂ rho, ∀ b ∈ ctxYq t tau x₁ x₂ rho,
      a * b = b * a :=
    fun a ha b hb =>
      congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(ctxYq t tau x₁ x₂ rho)) ⟨b, hb⟩)
  have hcomm := comm_zpowers_inv (A := ctxYq t tau x₁ x₂ rho) (g := g)
    hYcomm hg2 (fun a ha => hc.normal_Y.2 g hg a ha)
  have hcard : Nat.card ↥⁅ctxYq t tau x₁ x₂ rho, zpowers g⁆ = 4 := by
    have h := hcomm.2
    rw [card_ctxYq hc.q_iso, hcent, hc.wreath.fourGrp_eq_omega.2.2] at h
    omega
  have hle : ⁅ctxYq t tau x₁ x₂ rho, zpowers g⁆ ≤ fourGrp x₁ x₂ := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := (hcomm.1 n).mp hn
    have hga : g * a * g⁻¹ ∈ ctxYq t tau x₁ x₂ rho := hc.normal_Y.2 g hg a ha
    have he : a⁻¹ * (g * a * g⁻¹) ∈ fourGrp x₁ x₂ := c13_triv_YV hc hg hg2 hgρ a ha
    have hn_eq : (a⁻¹ * (g * a * g⁻¹))⁻¹ = a * g * a⁻¹ * g⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      have hc1 : (g * a * g⁻¹)⁻¹ * a = a * (g * a * g⁻¹)⁻¹ :=
        hYcomm _ (Subgroup.inv_mem _ hga) a ha
      rw [hc1]
      group
    rw [← hn_eq]
    exact Subgroup.inv_mem _ he
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc.wreath.fourGrp_eq_omega.2.2, hcard])

theorem c13_Y_comm (hc : Ctx13B t L S x₁ x₂ lam rho tau om)
    (htc : ∀ a ∈ ctxYq t tau x₁ x₂ rho, tau * a = a * tau) :
    ⁅ctxYq t tau x₁ x₂ rho, zpowers t⁆ = fourGrp x₁ x₂ ∧
      ⁅ctxYq t tau x₁ x₂ rho, zpowers (t * tau)⁆ = fourGrp x₁ x₂ := by
  have ht := c13_t_data hc.toCtx13A
  have htau := c13_tau_data hc.toCtx13A
  have htt : t * tau = tau * t :=
    (S4A.mem_invCent_iff.mp (hc.toCtx0.le_invCent hc.tau_mem)).symm
  have hsq : (t * tau) * (t * tau) = 1 := by
    calc (t * tau) * (t * tau) = t * (tau * t) * tau := by group
      _ = t * (t * tau) * tau := by rw [← htt]
      _ = (t * t) * (tau * tau) := by group
      _ = 1 := by rw [ht.2.1, htau.2.1, mul_one]
  have hcomm_rho : (t * tau) * rho = rho * (t * tau) := by
    calc (t * tau) * rho = t * (tau * rho) := by group
      _ = t * (rho * tau) := by rw [htau.2.2]
      _ = (t * rho) * tau := by group
      _ = (rho * t) * tau := by rw [ht.2.2]
      _ = rho * (t * tau) := by group
  refine ⟨c13_Y_comm_of hc ht.1 ht.2.1 ht.2.2 (c13_Y_cent hc htc).1, ?_⟩
  exact c13_Y_comm_of hc (Subgroup.mul_mem _ ht.1 htau.1) hsq hcomm_rho (c13_Y_cent hc htc).2

theorem ctx13c_of_b (hc : Ctx13B t L S x₁ x₂ lam rho tau om) :
    Ctx13C t L S x₁ x₂ lam rho tau om := by
  have htc := c13_tau_cent_Y hc
  exact
    { toCtx13B := hc, tau_cent_Y := htc, om_cent_Y := c13_om_cent_Y hc,
      tau_inv_Q := c13_tau_inv_Q hc htc, Y_cent := c13_Y_cent hc htc,
      Y_comm := c13_Y_comm hc htc }

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
