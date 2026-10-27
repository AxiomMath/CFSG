module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2SetA
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Gen
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Stage1.Thm6.Sec13

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho q : G}

private theorem fzc_sy3_mem_sup_comm {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [← A.closure_eq, ← B.closure_eq, ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul u v _ _ hu hv =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hu
    obtain ⟨a', ha', b', hb', rfl⟩ := hv
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    have e : b * a' = a' * b := (hAB a' ha' b hb).symm
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [e]
      _ = a * a' * (b * b') := by group
  | inv u _ hu =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hu
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    rw [mul_inv_rev]
    exact (hAB a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)).symm

theorem fzc_sy3_q_mem_W (hK : twoCore t = zpowers q) : q ∈ ctxW t x₁ x₂ :=
  mem_sup_left (by rw [hK]; exact mem_zpowers q)

theorem fzc_sy3_q_inf (h : Ctx0 t L S x₁ x₂ lam rho) (hK : twoCore t = zpowers q) :
    zpowers q ⊓ baseGrp x₁ x₂ = ⊥ := by
  rw [← hK]
  exact S4A.pt_inf_base h

theorem fzc_sy3_qpow_E (h : Ctx0 t L S x₁ x₂ lam rho) (hK : twoCore t = zpowers q)
    (hq4 : orderOf q = 4) {k : ℕ} (hk : q ^ k ∈ baseGrp x₁ x₂) : 4 ∣ k := by
  have hmem : q ^ k ∈ zpowers q ⊓ baseGrp x₁ x₂ := ⟨pow_mem (mem_zpowers q) k, hk⟩
  rw [fzc_sy3_q_inf h hK, mem_bot] at hmem
  rw [← hq4]
  exact orderOf_dvd_of_pow_eq_one hmem

theorem fzc_sy3_q_comm_W (h : Ctx0 t L S x₁ x₂ lam rho) (hK : twoCore t = zpowers q) :
    ∀ w ∈ ctxW t x₁ x₂, q * w = w * q :=
  fun w hw => fzc_sy2_W_comm h q (fzc_sy3_q_mem_W hK) w hw

theorem fzc_sy3_q_rho (h : Ctx0 t L S x₁ x₂ lam rho) (hK : twoCore t = zpowers q) :
    rho * q = q * rho := by
  have hq' : q ∈ ctxW t x₁ x₂ ⊓ centralizer ({rho} : Set G) := by
    rw [h.cent_rho, hK]
    exact mem_zpowers q
  exact (Subgroup.mem_centralizer_singleton_iff.mp hq'.2).symm

theorem fzc_sy3_q_lam (h : Ctx0 t L S x₁ x₂ lam rho) (hK : twoCore t = zpowers q) :
    q * lam = lam * q := by
  have hqK : q ∈ twoCore t := by rw [hK]; exact mem_zpowers q
  have hqC : q ∈ Subgroup.centralizer (L : Set G) := by
    rw [← h.hyp.centralizer_eq] at hqK
    exact hqK.1
  have hlamL : lam ∈ L := by
    have h1 : lam ∈ wreathGrp x₁ x₂ lam := subset_closure (by simp)
    rw [← h.inf_eq] at h1
    exact h1.2
  exact (Subgroup.mem_centralizer_iff.1 hqC lam hlamL).symm

theorem fzc_sy3_lam_sq (h : Ctx0 t L S x₁ x₂ lam rho) : lam * lam = 1 := by
  have h1 := pow_orderOf_eq_one lam
  rw [h.wreath.ord_lam] at h1
  simpa [pow_two] using h1

theorem fzc_sy3_lam_x₂ (h : Ctx0 t L S x₁ x₂ lam rho) : lam * x₂ * lam⁻¹ = x₁ := by
  have hl : lam * lam = 1 := fzc_sy3_lam_sq h
  have hli : lam⁻¹ = lam := by rw [inv_eq_iff_mul_eq_one]; exact hl
  rw [← h.wreath.conj_x₁, hli]
  calc lam * (lam * x₁ * lam) * lam = (lam * lam) * x₁ * (lam * lam) := by group
    _ = x₁ := by rw [hl]; group

theorem fzc_sy3_lam_t (h : Ctx0 t L S x₁ x₂ lam rho) (hK : twoCore t = zpowers q)
    (hqt : q ^ 2 = t) : lam * t = t * lam := by
  have hql := fzc_sy3_q_lam h hK
  rw [← hqt, pow_two]
  calc lam * (q * q) = (lam * q) * q := by group
    _ = (q * lam) * q := by rw [hql]
    _ = q * (lam * q) := by group
    _ = q * (q * lam) := by rw [hql]
    _ = q * q * lam := by group

theorem fzc_sy3_R_W : ∀ r ∈ fzR t x₁ x₂, ∀ w ∈ ctxW t x₁ x₂, r * w * r⁻¹ ∈ ctxW t x₁ x₂ :=
  fun r hr w hw => (Subgroup.mem_normalizer_iff.mp (fzl_R_le_N2 t x₁ x₂ hr) w).mp hw

theorem fzc_sy3_W_dec (h : Ctx0 t L S x₁ x₂ lam rho) (hK : twoCore t = zpowers q)
    (hq4 : orderOf q = 4) :
    ∀ w ∈ ctxW t x₁ x₂, ∃ k : ℕ, ∃ e ∈ baseGrp x₁ x₂, k < 4 ∧ w = q ^ k * e := by
  classical
  intro w hw
  have hcomm : ∀ a ∈ zpowers q, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a := by
    rw [← hK]
    exact S4A.pt_comm_base h
  have hw' : w ∈ zpowers q ⊔ baseGrp x₁ x₂ := by rw [← hK]; exact hw
  obtain ⟨a, ha, e, he, rfl⟩ := fzc_sy3_mem_sup_comm hcomm hw'
  rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at ha
  obtain ⟨k, hk, rfl⟩ := ha
  rw [Finset.mem_range, hq4] at hk
  exact ⟨k, e, he, hk, rfl⟩

theorem fzc_sy3_Wp_le_W (h : Ctx0 t L S x₁ x₂ lam rho) :
    baseGrp x₁ x₂ ⊔ zpowers t ≤ ctxW t x₁ x₂ :=
  sup_le le_sup_right (zpowers_le.2 (fzc_sy2_t_mem h))

private theorem fzc_sy3_t_comm_E (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ e ∈ baseGrp x₁ x₂, t * e = e * t :=
  fun e he => S4A.pt_comm_base h t h.hyp.mem_twoCore e he

theorem fzc_sy3_Wp_mem (h : Ctx0 t L S x₁ x₂ lam rho) {w : G} :
    w ∈ baseGrp x₁ x₂ ⊔ zpowers t ↔ w ∈ baseGrp x₁ x₂ ∨ t * w ∈ baseGrp x₁ x₂ := by
  have htt : t * t = 1 := by rw [← pow_two]; exact fzc_sy2_t_sq h
  have htN : ∀ e ∈ baseGrp x₁ x₂, t * e * t⁻¹ ∈ baseGrp x₁ x₂ := by
    intro e he
    rw [fzc_sy3_t_comm_E h e he, mul_inv_cancel_right]
    exact he
  constructor
  · intro hw
    obtain ⟨e, he, rfl | rfl⟩ :=
      (mem_sup_zpowers_sq (by rw [htt]; exact one_mem _) htN).1 hw
    · exact Or.inl he
    · right
      rw [← mul_assoc, fzc_sy3_t_comm_E h e he, mul_assoc, htt, mul_one]
      exact he
  · rintro (hw | hw)
    · exact mem_sup_left hw
    · have e : w = t * (t * w) := by rw [← mul_assoc, htt, one_mul]
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hw)

theorem fzc_sy3_q_notin_Wp (h : Ctx0 t L S x₁ x₂ lam rho) (hK : twoCore t = zpowers q)
    (hq4 : orderOf q = 4) (hqt : q ^ 2 = t) : q ∉ baseGrp x₁ x₂ ⊔ zpowers t := by
  intro hq
  rcases (fzc_sy3_Wp_mem h).1 hq with hq | hq
  · have := fzc_sy3_qpow_E h hK hq4 (k := 1) (by rw [pow_one]; exact hq)
    omega
  · have e : t * q = q ^ 3 := by rw [← hqt]; group
    rw [e] at hq
    have := fzc_sy3_qpow_E h hK hq4 hq
    omega

theorem fzc_sy3_W_cos (h : Ctx0 t L S x₁ x₂ lam rho) (hK : twoCore t = zpowers q)
    (hq4 : orderOf q = 4) (hqt : q ^ 2 = t) :
    ∀ w ∈ ctxW t x₁ x₂, w ∈ baseGrp x₁ x₂ ⊔ zpowers t ∨ q⁻¹ * w ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
  intro w hw
  obtain ⟨k, e, he, hk, rfl⟩ := fzc_sy3_W_dec h hK hq4 w hw
  have hte : t * e ∈ baseGrp x₁ x₂ ⊔ zpowers t :=
    mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left he)
  interval_cases k
  · left
    rw [pow_zero, one_mul]
    exact mem_sup_left he
  · right
    rw [pow_one, inv_mul_cancel_left]
    exact mem_sup_left he
  · left
    rw [hqt]
    exact hte
  · right
    have e' : q⁻¹ * (q ^ 3 * e) = t * e := by rw [← hqt]; group
    rw [e']
    exact hte

theorem fzc_sy3_rho_Wp (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ w ∈ baseGrp x₁ x₂ ⊔ zpowers t, rho * w * rho⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
  intro w hw
  rcases (fzc_sy3_Wp_mem h).1 hw with hw | hw
  · exact mem_sup_left (fzc_sy2_rho_nrm_E h w hw)
  · rw [fzc_sy3_Wp_mem h]
    right
    have e : t * (rho * w * rho⁻¹) = rho * (t * w) * rho⁻¹ := by
      calc t * (rho * w * rho⁻¹) = (rho * t * rho⁻¹) * (rho * w * rho⁻¹) := by
            rw [fzc_sy2_rho_t h]
        _ = rho * (t * w) * rho⁻¹ := by group
    rw [e]
    exact fzc_sy2_rho_nrm_E h _ hw

theorem fzc_sy3_lam_E (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ e ∈ baseGrp x₁ x₂, lam * e * lam⁻¹ ∈ baseGrp x₁ x₂ := by
  intro e he
  induction he using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · rw [h.wreath.conj_x₁]
      exact subset_closure (by simp)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [fzc_sy3_lam_x₂ h]
      exact subset_closure (by simp)
  | one => simp
  | mul u v _ _ hu hv =>
    have e : lam * (u * v) * lam⁻¹ = (lam * u * lam⁻¹) * (lam * v * lam⁻¹) := by group
    rw [e]
    exact mul_mem hu hv
  | inv u _ hu =>
    have e : lam * u⁻¹ * lam⁻¹ = (lam * u * lam⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hu

theorem fzc_sy3_card_Wp (h : Ctx0 t L S x₁ x₂ lam rho) :
    Nat.card ↥(baseGrp x₁ x₂ ⊔ zpowers t) = 32 := by
  have htt : t * t = 1 := by rw [← pow_two]; exact fzc_sy2_t_sq h
  have htN : ∀ e ∈ baseGrp x₁ x₂, t * e * t⁻¹ ∈ baseGrp x₁ x₂ := by
    intro e he
    rw [fzc_sy3_t_comm_E h e he, mul_inv_cancel_right]
    exact he
  rw [card_sup_zpowers_sq (by rw [htt]; exact one_mem _) htN (fzc_sy2_t_notin_E h),
    (h.wreath.baseGrp_eq).2.2]

theorem fzc_sy3_rho_EZ (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ e ∈ baseGrp x₁ x₂, rho * e * rho⁻¹ * e⁻¹ ∈ fourGrp x₁ x₂ → e ∈ fourGrp x₁ x₂ := by
  intro e he hz
  have hEc : ∀ a ∈ baseGrp x₁ x₂, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val
      (isMulCommutative_iff.mp (h.wreath.baseGrp_eq).1 ⟨a, ha⟩ ⟨b, hb⟩)
  set ζ := rho * e * rho⁻¹ * e⁻¹ with hζ
  have hζE : ζ ∈ baseGrp x₁ x₂ := S4A.pt_four_le_base x₁ x₂ hz
  have hζ2 : ζ ^ 2 = 1 := (WreathRel.fourGrp_eq_omega h.wreath).2.1.2 ζ hz
  have hre : rho * e * rho⁻¹ = ζ * e := by rw [hζ]; group
  have he2 : rho * e ^ 2 * rho⁻¹ = e ^ 2 := by
    have e1 : rho * e ^ 2 * rho⁻¹ = (rho * e * rho⁻¹) ^ 2 := by rw [pow_two, pow_two]; group
    rw [e1, hre, pow_two, pow_two]
    calc ζ * e * (ζ * e) = ζ * (e * ζ) * e := by group
      _ = ζ * (ζ * e) * e := by rw [hEc e he ζ hζE]
      _ = (ζ * ζ) * (e * e) := by group
      _ = e * e := by rw [← pow_two ζ, hζ2, one_mul]
  have hcen : e ^ 2 ∈ centralizer ({rho} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc e ^ 2 * rho = rho * e ^ 2 * rho⁻¹ * rho := by rw [he2]
      _ = rho * e ^ 2 := by group
  have hmem : e ^ 2 ∈ ctxW t x₁ x₂ ⊓ centralizer ({rho} : Set G) :=
    Subgroup.mem_inf.2 ⟨mem_sup_right (pow_mem he 2), hcen⟩
  rw [h.cent_rho] at hmem
  have hbot : e ^ 2 ∈ twoCore t ⊓ baseGrp x₁ x₂ := ⟨hmem, pow_mem he 2⟩
  rw [S4A.pt_inf_base h, mem_bot] at hbot
  exact fzc_sy2_E_invol h e he hbot

end CFSG.OddStandard.SmallF3.FritzII
