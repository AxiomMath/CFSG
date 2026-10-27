module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbA17c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17CosB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Pow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cnt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL414c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma card_zpowers_rho_eq_three (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card (zpowers rho) = 3 := by
  rw [Nat.card_zpowers, hc.ord_rho]

private lemma triple_inf_zpowers_rho_eq_bot (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    closure ({t, om, lam} : Set G) ⊓ zpowers rho = ⊥ := by
  obtain ⟨hlam2, hcomm⟩ := ctx13_lam_facts hc
  obtain ⟨hTleC, _, hTcard⟩ := ctx13_T_facts hc
  have hlamC : lam ∉ centralizer ({rho} : Set G) :=
    not_mem_centralizer_of_inv hc.ord_rho hc.lam_rho
  have hlamT : lam ∉ closure ({t, om} : Set G) := fun h => hlamC (hTleC h)
  have hT1card : Nat.card ↥(closure ({t, om, lam} : Set G)) = 16 := by
    rw [closure_triple_eq, card_sup_zpowers_of_commute hlam2 hlamT hcomm, hTcard]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxT, hxZ⟩ := Subgroup.mem_inf.mp hx
  have h1 : orderOf x ∣ 16 := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxT)
    rwa [Nat.card_zpowers, hT1card] at h
  have h2 : orderOf x ∣ 3 := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxZ)
    rwa [Nat.card_zpowers, card_zpowers_rho_eq_three hc] at h
  have h3 : orderOf x = 1 := by
    have hg : orderOf x ∣ 1 := by
      have hd := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 16 3 = 1 by norm_num] at hd
    exact Nat.eq_one_of_dvd_one hg
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h3)

private lemma conj_fix_rho (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ x ∈ ctxP t tau x₁ x₂ rho, rho * x * rho⁻¹ = x → x = 1 := by
  intro x hx h
  apply l17_CP_rho hc x hx
  have h' : rho * x = x * rho := by
    have := congrArg (fun z => z * rho) h
    simpa [mul_assoc] using this
  exact h'.symm

theorem l17_card_N_ge (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    48 ≤ Nat.card ↥(ctxK t tau x₁ x₂ rho ⊓ normalizer ((zpowers rho : Subgroup G) : Set G)) := by
  obtain ⟨htK, htauK, homK, hlamK, hrhoK⟩ := l17_mem_K hc
  obtain ⟨hTleC, hTpg, hTcard⟩ := ctx13_T_facts hc
  obtain ⟨hlam2, hcomm⟩ := ctx13_lam_facts hc
  let N : Subgroup G := ctxK t tau x₁ x₂ rho ⊓ normalizer ((zpowers rho : Subgroup G) : Set G)
  have hT_le_N : closure ({t, om} : Set G) ≤ N := by
    refine le_inf ?_ ?_
    · rw [Subgroup.closure_le]
      rintro x (hx : x ∈ ({t, om} : Set G))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact htK
      · exact homK
    · exact hTleC.trans centralizer_le_normalizer_zpowers
  have hlamN : lam ∈ normalizer ((zpowers rho : Subgroup G) : Set G) :=
    mem_normalizer_zpowers_of_inv hlam2 hc.lam_rho
  have hzlam_le_N : zpowers lam ≤ N :=
    le_inf (Subgroup.zpowers_le.mpr hlamK) (Subgroup.zpowers_le.mpr hlamN)
  have hT1_le_N : closure ({t, om, lam} : Set G) ≤ N := by
    rw [closure_triple_eq]
    exact sup_le hT_le_N hzlam_le_N
  have hzrho_le_N : zpowers rho ≤ N :=
    le_inf (Subgroup.zpowers_le.mpr hrhoK) Subgroup.le_normalizer
  have hT1card : Nat.card ↥(closure ({t, om, lam} : Set G)) = 16 := by
    have hlamC : lam ∉ centralizer ({rho} : Set G) :=
      not_mem_centralizer_of_inv hc.ord_rho hc.lam_rho
    have hlamT : lam ∉ closure ({t, om} : Set G) := fun h => hlamC (hTleC h)
    rw [closure_triple_eq, card_sup_zpowers_of_commute hlam2 hlamT hcomm, hTcard]
  have h := card_mul_le_of_inf_eq_bot hT1_le_N hzrho_le_N (triple_inf_zpowers_rho_eq_bot hc)
  rw [hT1card, card_zpowers_rho_eq_three hc] at h
  norm_num at h
  show 48 ≤ Nat.card ↥N
  exact h

theorem l17_card_P_le (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxP t tau x₁ x₂ rho) ≤ 2 ^ 8 := by
  let P : Subgroup G := ctxP t tau x₁ x₂ rho
  let K : Subgroup G := ctxK t tau x₁ x₂ rho
  let N : Subgroup G := K ⊓ normalizer ((zpowers rho : Subgroup G) : Set G)
  have hPleK : P ≤ K := inf_le_left
  have hNleK : N ≤ K := inf_le_left
  have hinf : P ⊓ N = ⊥ := by
    have h := l17_P_inf_N hc
    simpa only [P, K, N] using h
  have hmul : Nat.card P * Nat.card N ≤ Nat.card K :=
    card_mul_le_of_inf_eq_bot hPleK hNleK hinf
  have hN : 48 ≤ Nat.card N := l17_card_N_ge hc
  have h1 : Nat.card P * 48 ≤ 3 * 2 ^ 12 := by
    calc Nat.card P * 48 ≤ Nat.card P * Nat.card N := Nat.mul_le_mul_left _ hN
      _ ≤ Nat.card K := hmul
      _ = 3 * 2 ^ 12 := hc.card_K
  have h2 : Nat.card P ≤ 2 ^ 8 := by
    have h : Nat.card P * 48 ≤ 2 ^ 8 * 48 := by
      calc Nat.card P * 48 ≤ 3 * 2 ^ 12 := h1
        _ = 2 ^ 8 * 48 := by norm_num
    exact Nat.le_of_mul_le_mul_right h (by norm_num)
  show Nat.card ↥P ≤ 2 ^ 8
  exact h2

theorem l17_card_P (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    Nat.card ↥(ctxP t tau x₁ x₂ rho) = 2 ^ 8 ∧
      (ctxQ t tau x₁ x₂ rho).relIndex (ctxP t tau x₁ x₂ rho) = 4 := by
  have hc13 : Ctx13 t L S x₁ x₂ lam rho tau om := hc.toCtx13
  obtain ⟨htK, htauK, homK, hlamK, hrhoK⟩ := l17_mem_K hc13
  have hQP : ctxQ t tau x₁ x₂ rho ≤ ctxP t tau x₁ x₂ rho := l17_Q_le_P hc13
  have hQltP : ctxQ t tau x₁ x₂ rho < ctxP t tau x₁ x₂ rho := hc.Q_lt_P
  have hcardQ : Nat.card ↥(ctxQ t tau x₁ x₂ rho) = 64 := IsZ4Z4E4.card hc.q_iso
  have hcardP : Nat.card ↥(ctxP t tau x₁ x₂ rho) ≤ 256 := l17_card_P_le hc13
  have hP2 : IsPGroup 2 (ctxP t tau x₁ x₂ rho) := l17_P_pgroup hc13
  have hρ3 : rho ^ 3 = 1 := by
    rw [← hc.ord_rho]
    exact pow_orderOf_eq_one rho
  have hPρ : ∀ x ∈ ctxP t tau x₁ x₂ rho, rho * x * rho⁻¹ ∈ ctxP t tau x₁ x₂ rho :=
    (l17_P_normal hc13).2 rho hrhoK
  have hQρ : ∀ x ∈ ctxQ t tau x₁ x₂ rho, rho * x * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.normal_Q_K.2 rho hrhoK
  have hfix : ∀ x ∈ ctxP t tau x₁ x₂ rho, rho * x * rho⁻¹ = x → x = 1 :=
    conj_fix_rho hc13
  have hmodQ : Nat.card ↥(ctxQ t tau x₁ x₂ rho) % 3 = 1 := by
    rw [hcardQ]
  have hmod : (ctxQ t tau x₁ x₂ rho).relIndex (ctxP t tau x₁ x₂ rho) % 3 = 1 :=
    relIndex_mod_three hQP hρ3 hPρ hQρ hfix hmodQ
  obtain ⟨hidx, hcard⟩ := relIndex_eq_four_of_le hP2 hQltP hcardQ hcardP hmod
  exact ⟨by norm_num [hcard], hidx⟩

theorem l17_fpf (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    FpfSetting (ctxP t tau x₁ x₂ rho) (ctxQ t tau x₁ x₂ rho) rho := by
  have hc13 : Ctx13 t L S x₁ x₂ lam rho tau om := hc.toCtx13
  obtain ⟨htK, htauK, homK, hlamK, hrhoK⟩ := l17_mem_K hc13
  have hρ3 : rho ^ 3 = 1 := by
    rw [← hc.ord_rho]
    exact pow_orderOf_eq_one rho
  have hcardQ : Nat.card ↥(ctxQ t tau x₁ x₂ rho) = 64 := IsZ4Z4E4.card hc.q_iso
  refine ⟨l17_Q_le_P hc13, ?_, hρ3, ?_, ?_, conj_fix_rho hc13, ?_,
    (l17_card_P hc).2⟩
  · intro p hp q hq
    have hpC : p ∈ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hp).2
    exact (Subgroup.mem_centralizer_iff.mp hpC q hq).symm
  · intro x hx
    exact (l17_P_normal hc13).2 rho hrhoK x hx
  · intro x hx
    exact hc.normal_Q_K.2 rho hrhoK x hx
  · rw [hcardQ]

theorem l17_P_comm (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ a ∈ ctxP t tau x₁ x₂ rho, ∀ b ∈ ctxP t tau x₁ x₂ rho, a * b = b * a :=
  (l17_fpf hc).comm

theorem l17_pow_four_mem_V (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ x ∈ ctxP t tau x₁ x₂ rho, x ^ 4 ∈ fourGrp x₁ x₂ := by
  intro x hx
  have hx2Q : x ^ 2 ∈ ctxQ t tau x₁ x₂ rho := (l17_fpf hc).sq_mem x hx
  have hx4V : (x ^ 2) ^ 2 ∈ fourGrp x₁ x₂ := l17_Q_sq_mem hc.toCtx13 (x ^ 2) hx2Q
  have hx4 : x ^ 4 = (x ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
  rwa [hx4]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
