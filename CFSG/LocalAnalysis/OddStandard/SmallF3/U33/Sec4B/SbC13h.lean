module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

private theorem c13_t_comm_base (hc : Ctx11 t L S x₁ x₂ lam rho tau) {b : G}
    (hb : b ∈ baseGrp x₁ x₂) : t * b = b * t := by
  have hB : baseGrp x₁ x₂ ≤ centralizer ({t} : Set G) := by
    rw [← l12_CQ_t hc]
    exact inf_le_right
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hB hb)).symm

private theorem c13_lam_conj_x₂ (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    lam * x₂ * lam⁻¹ = x₁ := by
  have hlam2 : lam * lam = 1 := (c13_lam_data hc).2.1
  have hlinv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right hlam2
  have h : lam * x₁ * lam = x₂ := by simpa [hlinv] using hc.wreath.conj_x₁
  rw [hlinv]
  calc lam * x₂ * lam = lam * (lam * x₁ * lam) * lam := by rw [h]
    _ = (lam * lam) * x₁ * (lam * lam) := by group
    _ = x₁ := by rw [hlam2, one_mul, mul_one]

theorem c13_sigma_V (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 ∧
      (lam * t) * (x₁ * x₂) ^ 2 * (lam * t)⁻¹ = (x₁ * x₂) ^ 2 := by
  have hx₁B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂B : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have ht₁ : t * x₁ = x₁ * t := c13_t_comm_base hc hx₁B
  have ht₂ : t * x₂ = x₂ * t := c13_t_comm_base hc hx₂B
  have hsq₁ : t * x₁ ^ 2 * t⁻¹ = x₁ ^ 2 := by
    calc t * x₁ ^ 2 * t⁻¹ = (t * x₁ * t⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = x₁ ^ 2 := by rw [show t * x₁ * t⁻¹ = x₁ by rw [ht₁]; group]
  have hsq₂ : t * (x₁ * x₂) ^ 2 * t⁻¹ = (x₁ * x₂) ^ 2 := by
    have ht : t * (x₁ * x₂) = (x₁ * x₂) * t := by
      rw [← mul_assoc, ht₁, mul_assoc, ht₂, mul_assoc]
    calc t * (x₁ * x₂) ^ 2 * t⁻¹ = (t * (x₁ * x₂) * t⁻¹) ^ 2 := by
          simp only [pow_two]; group
      _ = (x₁ * x₂) ^ 2 := by rw [show t * (x₁ * x₂) * t⁻¹ = x₁ * x₂ by rw [ht]; group]
  have hconj : lam * (x₁ * x₂) * lam⁻¹ = x₁ * x₂ := by
    calc lam * (x₁ * x₂) * lam⁻¹
        = (lam * x₁ * lam⁻¹) * (lam * x₂ * lam⁻¹) := by group
      _ = x₂ * x₁ := by rw [hc.wreath.conj_x₁, c13_lam_conj_x₂ hc]
      _ = x₁ * x₂ := hc.wreath.comm.symm
  constructor
  · calc (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = lam * (t * x₁ ^ 2 * t⁻¹) * lam⁻¹ := by group
      _ = lam * x₁ ^ 2 * lam⁻¹ := by rw [hsq₁]
      _ = (lam * x₁ * lam⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = x₂ ^ 2 := by rw [hc.wreath.conj_x₁]
      _ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := hc.wreath.x₂_sq
  · calc (lam * t) * (x₁ * x₂) ^ 2 * (lam * t)⁻¹
        = lam * (t * (x₁ * x₂) ^ 2 * t⁻¹) * lam⁻¹ := by group
      _ = lam * (x₁ * x₂) ^ 2 * lam⁻¹ := by rw [hsq₂]
      _ = (lam * (x₁ * x₂) * lam⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = (x₁ * x₂) ^ 2 := by rw [hconj]

theorem c13_V_ne (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    x₁ ^ 2 ≠ 1 ∧ (x₁ * x₂) ^ 2 ≠ 1 ∧ x₁ ^ 2 ≠ (x₁ * x₂) ^ 2 := by
  have h4 : x₁ ^ 4 = 1 := by
    have := pow_orderOf_eq_one x₁
    rwa [hc.wreath.ord_x₁] at this
  have hy2 : (x₁ ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show (2 * 2 : ℕ) = 4 from rfl, h4]
  have hy_dvd : orderOf (x₁ ^ 2) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
  have hy_le2 : orderOf (x₁ ^ 2) ≤ 2 := Nat.le_of_dvd (by norm_num) hy_dvd
  have hcardV : Nat.card ↥(fourGrp x₁ x₂) = 4 := hc.wreath.fourGrp_eq_omega.2.2
  have hle_of (h : (x₁ * x₂) ^ 2 = 1 ∨ (x₁ * x₂) ^ 2 = x₁ ^ 2) :
      fourGrp x₁ x₂ ≤ zpowers (x₁ ^ 2) := by
    rw [fourGrp, Subgroup.closure_le]
    intro a ha
    rcases (by simpa using ha) with rfl | rfl
    · exact Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one _⟩
    · rcases h with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hy1
    have hdvd : orderOf x₁ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy1
    rw [hc.wreath.ord_x₁] at hdvd
    norm_num at hdvd
  · intro hz1
    have h := Subgroup.card_le_of_le (hle_of (Or.inl hz1))
    rw [hcardV, Nat.card_zpowers] at h
    omega
  · intro hyz
    have h := Subgroup.card_le_of_le (hle_of (Or.inr hyz.symm))
    rw [hcardV, Nat.card_zpowers] at h
    omega

theorem c13_CV_sigma (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ∀ v ∈ fourGrp x₁ x₂, (lam * t) * v * (lam * t)⁻¹ = v → v = 1 ∨ v = (x₁ * x₂) ^ 2 := by
  have hV := hc.wreath.fourGrp_eq_omega.2.1
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hy2 : x₁ ^ 2 * x₁ ^ 2 = 1 := by
    have := hV.2 (x₁ ^ 2) hyV
    rwa [pow_two] at this
  have hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := by
    have := hV.2 ((x₁ * x₂) ^ 2) hzV
    rwa [pow_two] at this
  have hyz : x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 := by
    haveI : IsMulCommutative ↥(fourGrp x₁ x₂) := hV.1
    exact congrArg Subtype.val (mul_comm' (⟨x₁ ^ 2, hyV⟩ : ↥(fourGrp x₁ x₂))
      ⟨(x₁ * x₂) ^ 2, hzV⟩)
  intro v hv hfix
  have hsig := c13_sigma_V hc
  have hv' : v ∈ Subgroup.closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) := by
    simpa [fourGrp] using hv
  rcases (mem_closure_pair_of_invol hy2 hz2 hyz).mp hv' with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exfalso
    have h : x₁ ^ 2 * (x₁ * x₂) ^ 2 = x₁ ^ 2 := by rw [hsig.1] at hfix; exact hfix
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      have := congrArg (fun u => (x₁ ^ 2)⁻¹ * u) h
      simpa [mul_assoc] using this
    exact (c13_V_ne hc).2.1 hz1
  · exact Or.inr rfl
  · exfalso
    have hconj : (lam * t) * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (lam * t)⁻¹ = x₁ ^ 2 := by
      calc (lam * t) * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (lam * t)⁻¹
          = ((lam * t) * x₁ ^ 2 * (lam * t)⁻¹) *
              ((lam * t) * (x₁ * x₂) ^ 2 * (lam * t)⁻¹) := by group
        _ = (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 := by rw [hsig.1, hsig.2]
        _ = x₁ ^ 2 := by
            rw [show (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 =
              x₁ ^ 2 * ((x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2) by group, hz2, mul_one]
    have h : x₁ ^ 2 = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by rw [hconj] at hfix; exact hfix
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      have := congrArg (fun u => (x₁ ^ 2)⁻¹ * u) h
      simpa [mul_assoc] using this.symm
    exact (c13_V_ne hc).2.1 hz1

private theorem c13_conj_fix_of_mem_cent {σ a : G}
    (h : a ∈ centralizer ({σ} : Set G)) : σ * a * σ⁻¹ = a := by
  have h2 : a * σ = σ * a := Subgroup.mem_centralizer_singleton_iff.mp h
  rw [← h2]
  group

theorem c13_exists_v0 (hc : Ctx13B t L S x₁ x₂ lam rho tau om) :
    ∃ v₀ ∈ ctxYq t tau x₁ x₂ rho, v₀ ∉ fourGrp x₁ x₂ ∧
      (lam * t) * v₀ * (lam * t)⁻¹ = v₀ := by
  by_contra h
  push Not at h
  have hCV : ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) ≤
      fourGrp x₁ x₂ := by
    intro a ha
    by_contra haV
    exact h a ha.1 haV (c13_conj_fix_of_mem_cent ha.2)
  have hCVeq : ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) =
      fourGrp x₁ x₂ := by
    refine Subgroup.eq_of_le_of_card_ge hCV ?_
    rw [hc.wreath.fourGrp_eq_omega.2.2]
    exact c13_CY_sigma_card hc
  have hfix (v : G) (hv : v ∈ fourGrp x₁ x₂) :
      (lam * t) * v * (lam * t)⁻¹ = v := by
    have hvH : v ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) :=
      hCVeq.symm ▸ hv
    exact c13_conj_fix_of_mem_cent hvH.2
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hy1 : x₁ ^ 2 ≠ 1 := (c13_V_ne hc.toCtx11).1
  have hwV : rho * x₁ ^ 2 * rho⁻¹ ∈ fourGrp x₁ x₂ :=
    hc.normal_V.2 rho (l12_rho_lam_mem_M hc.toCtx11).1 _ hyV
  have hfix_y : (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = x₁ ^ 2 := hfix _ hyV
  have hfix_w : (lam * t) * (rho * x₁ ^ 2 * rho⁻¹) * (lam * t)⁻¹ =
      rho * x₁ ^ 2 * rho⁻¹ := hfix _ hwV
  have hσρ : (lam * t) * rho * (lam * t)⁻¹ = rho⁻¹ :=
    (c13_sigma_data hc.toCtx11).2.2.2.1
  have hE : rho * x₁ ^ 2 * rho⁻¹ = rho⁻¹ * x₁ ^ 2 * rho := by
    have hconj : (lam * t) * (rho * x₁ ^ 2 * rho⁻¹) * (lam * t)⁻¹ =
        ((lam * t) * rho * (lam * t)⁻¹) * ((lam * t) * x₁ ^ 2 * (lam * t)⁻¹) *
          ((lam * t) * rho * (lam * t)⁻¹)⁻¹ := by group
    rw [hfix_w, hσρ, hfix_y] at hconj
    simpa [inv_inv] using hconj
  have hrho3 : rho ^ 3 = 1 := by
    have := pow_orderOf_eq_one rho
    rwa [hc.ord_rho] at this
  have h1 : rho ^ 2 * x₁ ^ 2 = x₁ ^ 2 * rho ^ 2 := by
    have h := congrArg (fun u => rho * u * rho) hE
    calc rho ^ 2 * x₁ ^ 2 = rho * (rho * x₁ ^ 2 * rho⁻¹) * rho := by
          simp only [pow_two]; group
      _ = rho * (rho⁻¹ * x₁ ^ 2 * rho) * rho := h
      _ = x₁ ^ 2 * rho ^ 2 := by simp only [pow_two]; group
  have hrho2 : rho ^ 2 = rho⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show (2 : ℕ) + 1 = 3 from rfl, hrho3]
  have hcomm_y : x₁ ^ 2 * rho = rho * x₁ ^ 2 := by
    have h5 : rho⁻¹ * x₁ ^ 2 = x₁ ^ 2 * rho⁻¹ := by rw [← hrho2]; exact h1
    have h6 : x₁ ^ 2 = rho * x₁ ^ 2 * rho⁻¹ := by
      have := congrArg (fun u => rho * u) h5
      simpa [mul_assoc] using this
    have := congrArg (fun u => u * rho) h6
    simpa [mul_assoc] using this
  have hyQ : x₁ ^ 2 ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ (hc.V_le_Y hyV)
  exact hy1 (l12_cent_Q_rho hc.toCtx11 (x₁ ^ 2) hyQ hcomm_y)

theorem c13_cmap_mem (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ ctxYq t tau x₁ x₂ rho, a * (t * a * t⁻¹) ∈ fourGrp x₁ x₂ := by
  intro a ha
  have ha2 : a * a = 1 := by
    have := hc.Y_elem.2 a ha
    rwa [pow_two] at this
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have ht := c13_t_data hc.toCtx13A
  have h := c13_triv_YV hc.toCtx13B ht.1 ht.2.1 ht.2.2 a ha
  rwa [hai] at h

theorem c13_cmap_mul (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ ctxYq t tau x₁ x₂ rho, ∀ b ∈ ctxYq t tau x₁ x₂ rho,
      (a * b) * (t * (a * b) * t⁻¹) = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by
  intro a ha b hb
  have ht := c13_t_data hc.toCtx13A
  have hta : t * a * t⁻¹ ∈ ctxYq t tau x₁ x₂ rho := hc.normal_Y.2 t ht.1 a ha
  have htb : t * b * t⁻¹ ∈ ctxYq t tau x₁ x₂ rho := hc.normal_Y.2 t ht.1 b hb
  have hcomm : b * (t * a * t⁻¹) = (t * a * t⁻¹) * b :=
    hc.Q_comm b (ctxYq_le_ctxQ hb) (t * a * t⁻¹) (ctxYq_le_ctxQ hta)
  calc (a * b) * (t * (a * b) * t⁻¹)
      = a * b * (t * a * t⁻¹) * (t * b * t⁻¹) := by
        rw [show t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) by group]
        group
    _ = a * (t * a * t⁻¹) * b * (t * b * t⁻¹) := by
        rw [show a * b * (t * a * t⁻¹) * (t * b * t⁻¹) =
          a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) by group, hcomm]
        group
    _ = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by group

theorem c13_cmap_eq_one (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ ctxYq t tau x₁ x₂ rho, a * (t * a * t⁻¹) = 1 ↔ a ∈ fourGrp x₁ x₂ := by
  intro a ha
  constructor
  · intro h
    have ha2 : a * a = 1 := by
      have := hc.Y_elem.2 a ha
      rwa [pow_two] at this
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have h1 : t * a * t⁻¹ = a⁻¹ := by
      have := congrArg (fun u => a⁻¹ * u) h
      simpa [mul_assoc] using this
    rw [hai] at h1
    have h2 : a * t = t * a := by
      have := congrArg (fun u => u * t) h1
      simpa [mul_assoc] using this.symm
    exact hc.Y_cent.1 ▸ ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr h2⟩
  · intro haV
    have haH : a ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
      hc.Y_cent.1.symm ▸ haV
    have h2 : a * t = t * a := Subgroup.mem_centralizer_singleton_iff.mp haH.2
    have h3 : t * a * t⁻¹ = a := by rw [← h2]; group
    have ha2 : a * a = 1 := by
      have := hc.Y_elem.2 a ha
      rwa [pow_two] at this
    rw [h3, ha2]

theorem c13_cmap_surj (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ∀ v ∈ fourGrp x₁ x₂, ∃ a ∈ ctxYq t tau x₁ x₂ rho, a * (t * a * t⁻¹) = v := by
  intro v hv
  have hA : ∀ a ∈ ctxYq t tau x₁ x₂ rho, ∀ b ∈ ctxYq t tau x₁ x₂ rho, a * b = b * a :=
    fun a ha b hb => hc.Q_comm a (ctxYq_le_ctxQ ha) b (ctxYq_le_ctxQ hb)
  have ht := c13_t_data hc.toCtx13A
  have hgt : ∀ a ∈ ctxYq t tau x₁ x₂ rho, t * a * t⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
    fun a ha => hc.normal_Y.2 t ht.1 a ha
  have hv' : v ∈ ⁅ctxYq t tau x₁ x₂ rho, zpowers t⁆ := by
    rw [hc.Y_comm.1]
    exact hv
  obtain ⟨a, ha, hva⟩ := ((comm_zpowers_inv hA ht.2.1 hgt).1 v).mp hv'
  refine ⟨a, ha, ?_⟩
  have ha2 : a * a = 1 := by
    have := hc.Y_elem.2 a ha
    rwa [pow_two] at this
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  rw [hva, hai]
  group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
