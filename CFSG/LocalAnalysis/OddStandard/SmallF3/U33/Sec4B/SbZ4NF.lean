module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4ND
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC17

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma not_mem_zpowers_of_sq_eq_one {g m : G} (hg8 : orderOf g = 8)
    (hg4 : g ^ 4 = (x₁ * x₂) ^ 2)
    (hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1)
    (hm2 : m * m = 1) (hm1 : m ≠ 1) (hmz : m ≠ (x₁ * x₂) ^ 2) :
    m ∉ zpowers g := by
  intro hm
  have hm' : m ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.mpr hm
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff m g).mp hm'
  have h2k : g ^ (k * 2) = 1 := by
    rw [pow_mul g k 2, hk]
    exact show m ^ 2 = 1 by rw [pow_two]; exact hm2
  have hdvd : orderOf g ∣ k * 2 := orderOf_dvd_of_pow_eq_one h2k
  rw [hg8] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  have h4dvd : 4 ∣ k := by
    use c
    omega
  obtain ⟨j, rfl⟩ := h4dvd
  have hmj : m = ((x₁ * x₂) ^ 2) ^ j := by
    rw [← hk, pow_mul g 4 j, hg4]
  rcases z4_mem_zpowers_of_mul_self hz2
    (Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), by rw [zpow_natCast]⟩) with h | h
  · exact hm1 (hmj.trans h)
  · exact hmz (hmj.trans h)

namespace Ctx4Z

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

theorem sigma_conj_t : ∃ h : G, h * t * h⁻¹ = lam * t := by
  have hlamL : lam ∈ L := hz.lam_mem_L
  have hlam2 : lam * lam = 1 := hz.lam_mul_self
  have hlam_ne : lam ≠ 1 := by
    intro h
    have h2 : orderOf lam = orderOf (1 : G) := by rw [h]
    rw [hz.wreath.ord_lam, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨c, hcL, hcz⟩ := hz.invol_L lam hlamL hlam2 hlam_ne
  have hct : c * t * c⁻¹ = t := by
    have hcomm : c * t = t * c := S4A.mem_invCent_iff.mp (S4A.L_le_invCent hz.hyp hcL)
    rw [hcomm]; group
  have htmem : t * (x₁ * x₂) ^ 2 ∈ conjIn (ctxQ t tau x₁ x₂ rho) t := by
    rw [hz.tQ]
    exact Set.mem_smul_set.mpr ⟨(x₁ * x₂) ^ 2, hz.z_mem_V, rfl⟩
  obtain ⟨q, _, hq⟩ := htmem
  refine ⟨c * q, ?_⟩
  have hmain : (c * q) * t * (c * q)⁻¹ = t * lam := by
    calc (c * q) * t * (c * q)⁻¹ = c * (q * t * q⁻¹) * c⁻¹ := by group
      _ = c * (t * (x₁ * x₂) ^ 2) * c⁻¹ := by rw [hq]
      _ = (c * t * c⁻¹) * (c * (x₁ * x₂) ^ 2 * c⁻¹) := by group
      _ = t * lam := by rw [hct, hcz]
  rw [hmain]
  exact hz.t_lam_comm

theorem sigma_not_mem_ctxWN : lam * t ∉ ctxWN t tau x₁ x₂ rho :=
  fun h => hz.sigma_not_mem_ctxCQ (ctxWN_le_ctxCQ t tau x₁ x₂ rho h)

end Ctx4Z

namespace ZNW

variable (hw : ZNW t L S x₁ x₂ lam rho tau)
include hw

theorem exists_pow_four_y (hne : ∃ w ∈ ctxWN t tau x₁ x₂ rho, w ^ 4 ≠ 1) :
    ∃ w ∈ ctxWN t tau x₁ x₂ rho, w ^ 4 = x₁ ^ 2 := by
  obtain ⟨x, hx, hx4⟩ := hne
  have hz := hw.toCtx4Z
  exact S4B.exists_pow_four_eq (P := ctxWN t tau x₁ x₂ rho) (V := fourGrp x₁ x₂)
    hw.W_comm hz.rho_pow_three (fun y hy => hz.rho_conj_ctxWN hy) hz.nPre.card_V
    (fun v hv => hz.rho_conj_V hv) (fun v hv h => hz.rho_fpf_V hv h)
    hw.W_pow_four_mem_V hx hx4 (x₁ ^ 2) hz.y_mem_V

theorem exists_sigma_fixed {w₁ : G} (hw₁ : w₁ ∈ ctxWN t tau x₁ x₂ rho) (h4 : w₁ ^ 4 = x₁ ^ 2) :
    ∃ N ∈ ctxWN t tau x₁ x₂ rho, (lam * t) * N * (lam * t)⁻¹ = N ∧
      N ^ 4 = (x₁ * x₂) ^ 2 ∧ orderOf N = 8 := by
  have hz := hw.toCtx4Z
  have hσ2 : (lam * t) * (lam * t) = 1 := hz.sigma_sq
  have hσw : (lam * t) * w₁ * (lam * t)⁻¹ ∈ ctxWN t tau x₁ x₂ rho := hz.sigma_conj_ctxWN hw₁
  let N : G := w₁ * ((lam * t) * w₁ * (lam * t)⁻¹)
  have hNW : N ∈ ctxWN t tau x₁ x₂ rho := mul_mem hw₁ hσw
  have hcomm : Commute w₁ ((lam * t) * w₁ * (lam * t)⁻¹) :=
    (commute_iff_eq w₁ _).mpr (hw.W_comm w₁ hw₁ _ hσw)
  have hσw4 : ((lam * t) * w₁ * (lam * t)⁻¹) ^ 4 = x₂ ^ 2 := by
    rw [conj_pow, h4, hz.sigma_y]
  have hyw : x₁ ^ 2 * x₂ ^ 2 = (x₁ * x₂) ^ 2 := by
    rw [hz.x₂_sq]
    rw [show x₁ ^ 2 * (x₁ ^ 2 * (x₁ * x₂) ^ 2) = (x₁ * x₂) ^ 2 by
      rw [← mul_assoc, show x₁ ^ 2 * x₁ ^ 2 = 1 from by rw [← pow_two]; exact hz.y_sq,
        one_mul]]
  have hN4eq : N ^ 4 = (x₁ * x₂) ^ 2 := by
    change (w₁ * ((lam * t) * w₁ * (lam * t)⁻¹)) ^ 4 = (x₁ * x₂) ^ 2
    rw [Commute.mul_pow hcomm 4, h4, hσw4, hyw]
  have hfixN : (lam * t) * N * (lam * t)⁻¹ = N := by
    have hconj : (lam * t) * ((lam * t) * w₁ * (lam * t)⁻¹) * (lam * t)⁻¹ = w₁ := by
      calc (lam * t) * ((lam * t) * w₁ * (lam * t)⁻¹) * (lam * t)⁻¹
          = ((lam * t) * (lam * t)) * w₁ * ((lam * t) * (lam * t))⁻¹ := by group
        _ = w₁ := by rw [hσ2]; group
    change (lam * t) * (w₁ * ((lam * t) * w₁ * (lam * t)⁻¹)) * (lam * t)⁻¹ =
      w₁ * ((lam * t) * w₁ * (lam * t)⁻¹)
    calc (lam * t) * (w₁ * ((lam * t) * w₁ * (lam * t)⁻¹)) * (lam * t)⁻¹
        = ((lam * t) * w₁ * (lam * t)⁻¹) *
            ((lam * t) * ((lam * t) * w₁ * (lam * t)⁻¹) * (lam * t)⁻¹) := by group
      _ = ((lam * t) * w₁ * (lam * t)⁻¹) * w₁ := by rw [hconj]
      _ = w₁ * ((lam * t) * w₁ * (lam * t)⁻¹) := hw.W_comm _ hσw _ hw₁
  have hN8 : N ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 + 4 by norm_num, pow_add, hN4eq, ← pow_two, hz.z_sq]
  have hord : orderOf N = 8 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := N) ?_ ?_
    · rwa [show (2 : ℕ) ^ (2 + 1) = 8 by norm_num] at h
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      rw [hN4eq]
      exact hz.z_ne_one
    · rw [show (2 : ℕ) ^ (2 + 1) = 8 by norm_num]
      exact hN8
  exact ⟨N, hNW, hfixN, hN4eq, hord⟩

theorem exists_abelian_big {N : G} (hN : N ∈ ctxWN t tau x₁ x₂ rho)
    (hfix : (lam * t) * N * (lam * t)⁻¹ = N) (h4 : N ^ 4 = (x₁ * x₂) ^ 2) (h8 : orderOf N = 8) :
    ∃ A : Subgroup G, A ≤ centralizer ({lam * t} : Set G) ∧ IsMulCommutative A ∧
      IsPGroup 2 A ∧ N ∈ A ∧ 16 < Nat.card A := by
  have hz := hw.toCtx4Z
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ2 : (lam * t) * (lam * t) = 1 := hz.sigma_sq
  have hσ_ne : lam * t ≠ 1 := by
    intro h
    exact hz.sigma_not_mem_ctxWN (h ▸ Subgroup.one_mem _)
  have hσ_order : orderOf (lam * t) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ_ne
  have hσN : (lam * t) * N = N * (lam * t) := by
    calc (lam * t) * N = ((lam * t) * N * (lam * t)⁻¹) * (lam * t) := by group
      _ = N * (lam * t) := by rw [hfix]
  obtain ⟨V', v₁, v₂, hV⟩ := hz.data_V
  obtain ⟨hVea, hVcard, hVQ, hVinf, hVY, hVρ, hv₁V, hv₂V, hv₁ne, hv₂notzp, hVcl,
    ht₁, ht₂, hσv₁, hQm⟩ := hV
  haveI : IsMulCommutative ↥V' := hVea.1
  have hcommV' : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : V') ⟨b, hb⟩)
  let m : G := v₁ * v₂
  have hm2 : m * m = 1 := by
    change (v₁ * v₂) * (v₁ * v₂) = 1
    rw [← pow_two, Commute.mul_pow (hcommV' v₁ hv₁V v₂ hv₂V) 2]
    rw [show v₁ ^ 2 = 1 from hVea.2 v₁ hv₁V, show v₂ ^ 2 = 1 from hVea.2 v₂ hv₂V, mul_one]
  have hmV' : m ∈ V' := by
    change v₁ * v₂ ∈ V'
    exact mul_mem hv₁V hv₂V
  have hm1 : m ≠ 1 := by
    intro h
    apply hv₂notzp
    have h' : v₁ * v₂ = 1 := h
    have : v₂ = v₁ := by
      have h1 : v₁ * v₂ = v₁ * v₁ := by
        rw [h', ← pow_two, show v₁ ^ 2 = 1 from hVea.2 v₁ hv₁V]
      exact mul_left_cancel h1
    rw [this]
    exact Subgroup.mem_zpowers v₁
  have hmz : m ≠ (x₁ * x₂) ^ 2 := by
    intro h
    have hzbase : (x₁ * x₂) ^ 2 ∈ baseGrp x₁ x₂ := hz.nPre.V_le_B hz.z_mem_V
    have hmem : m ∈ (⊥ : Subgroup G) := by
      rw [← hVinf]
      exact ⟨h ▸ hzbase, hmV'⟩
    exact hm1 (Subgroup.mem_bot.mp hmem)
  have hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := by rw [← pow_two]; exact hz.z_sq
  have hm_not_mem : m ∉ zpowers N := not_mem_zpowers_of_sq_eq_one h8 h4 hz2 hm2 hm1 hmz
  have hY_v₁ : v₁ ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hVY]; exact Subgroup.mem_sup_right hv₁V
  have hY_v₂ : v₂ ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hVY]; exact Subgroup.mem_sup_right hv₂V
  have hv₁W : v₁ ∈ ctxWN t tau x₁ x₂ rho := hz.Y_le_ctxWN hY_v₁
  have hv₂W : v₂ ∈ ctxWN t tau x₁ x₂ rho := hz.Y_le_ctxWN hY_v₂
  have hmW : m ∈ ctxWN t tau x₁ x₂ rho := by
    change v₁ * v₂ ∈ ctxWN t tau x₁ x₂ rho
    exact mul_mem hv₁W hv₂W
  have hP₁_le_W : zpowers N ≤ ctxWN t tau x₁ x₂ rho := Subgroup.zpowers_le.mpr hN
  have hP₂_le_W : zpowers m ≤ ctxWN t tau x₁ x₂ rho := Subgroup.zpowers_le.mpr hmW
  have hB_le_W : zpowers N ⊔ zpowers m ≤ ctxWN t tau x₁ x₂ rho :=
    sup_le hP₁_le_W hP₂_le_W
  have hP₁P₂_comm : ∀ a ∈ zpowers N, ∀ b ∈ zpowers m, a * b = b * a :=
    fun a ha b hb => hw.W_comm a (hP₁_le_W ha) b (hP₂_le_W hb)
  have hcardP₁ : Nat.card ↥(zpowers N) = 8 := by rw [Nat.card_zpowers]; exact h8
  have hP₂_order : orderOf m = 2 := orderOf_eq_prime (by rw [pow_two]; exact hm2) hm1
  have hcardP₂ : Nat.card ↥(zpowers m) = 2 := by rw [Nat.card_zpowers]; exact hP₂_order
  have hcard_inf_dvd : Nat.card ↥(zpowers N ⊓ zpowers m) ∣ 2 := by
    rw [← hcardP₂]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hcard_inf : zpowers N ⊓ zpowers m = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hcard_inf_dvd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : zpowers N ⊓ zpowers m = zpowers m :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcardP₂, h2])
      have hm_mem : m ∈ zpowers N ⊓ zpowers m := by
        rw [heq]; exact Subgroup.mem_zpowers m
      exact hm_not_mem hm_mem.1
  have hcardB : Nat.card ↥(zpowers N ⊔ zpowers m) = 16 := by
    rw [card_sup_of_commute hP₁P₂_comm hcard_inf, hcardP₁, hcardP₂]
  have hσP₁ : ∀ a ∈ zpowers N, a * (lam * t) = (lam * t) * a := by
    intro a ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hcomm : Commute N (lam * t) := (commute_iff_eq N (lam * t)).mpr hσN.symm
    exact (hcomm.zpow_left i).eq
  have hσv₂ : (lam * t) * v₂ * (lam * t)⁻¹ = v₁ := by
    have h1 : (lam * t) * ((lam * t) * v₁ * (lam * t)⁻¹) * (lam * t)⁻¹ = v₁ := by
      calc (lam * t) * ((lam * t) * v₁ * (lam * t)⁻¹) * (lam * t)⁻¹
          = ((lam * t) * (lam * t)) * v₁ * ((lam * t) * (lam * t))⁻¹ := by group
        _ = v₁ := by rw [hσ2]; group
    rwa [hσv₁] at h1
  have hσm : (lam * t) * m * (lam * t)⁻¹ = m := by
    change (lam * t) * (v₁ * v₂) * (lam * t)⁻¹ = v₁ * v₂
    calc (lam * t) * (v₁ * v₂) * (lam * t)⁻¹
        = ((lam * t) * v₁ * (lam * t)⁻¹) * ((lam * t) * v₂ * (lam * t)⁻¹) := by group
      _ = v₂ * v₁ := by rw [hσv₁, hσv₂]
      _ = v₁ * v₂ := (hcommV' v₁ hv₁V v₂ hv₂V).symm
  have hσm_comm : (lam * t) * m = m * (lam * t) := by
    calc (lam * t) * m = ((lam * t) * m * (lam * t)⁻¹) * (lam * t) := by group
      _ = m * (lam * t) := by rw [hσm]
  have hσP₂ : ∀ c ∈ zpowers m, c * (lam * t) = (lam * t) * c := by
    intro c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hcomm : Commute m (lam * t) := (commute_iff_eq m (lam * t)).mpr hσm_comm.symm
    exact (hcomm.zpow_left i).eq
  have hσB : ∀ b ∈ zpowers N ⊔ zpowers m, b * (lam * t) = (lam * t) * b := by
    intro b hb
    obtain ⟨a, ha, c, hc, rfl⟩ := (mem_sup_iff_of_commute hP₁P₂_comm).mp hb
    calc (a * c) * (lam * t) = a * (c * (lam * t)) := by group
      _ = a * ((lam * t) * c) := by rw [hσP₂ c hc]
      _ = (a * (lam * t)) * c := by group
      _ = ((lam * t) * a) * c := by rw [hσP₁ a ha]
      _ = (lam * t) * (a * c) := by group
  have hBσ_comm : ∀ a ∈ zpowers N ⊔ zpowers m, ∀ b ∈ zpowers (lam * t), a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hcomm : Commute a (lam * t) := (commute_iff_eq a (lam * t)).mpr (hσB a ha)
    exact (hcomm.zpow_right k).eq
  have hP₁2 : IsPGroup 2 ↥(zpowers N) :=
    IsPGroup.of_card_dvd_pow (p := 2) (n := 3) (by rw [hcardP₁]; norm_num)
  have hP₂2 : IsPGroup 2 ↥(zpowers m) :=
    IsPGroup.of_card_dvd_pow (p := 2) (n := 1) (by rw [hcardP₂]; norm_num)
  have hσ2group : IsPGroup 2 ↥(zpowers (lam * t)) :=
    IsPGroup.of_card_dvd_pow (p := 2) (n := 1) (by rw [Nat.card_zpowers, hσ_order]; norm_num)
  have hB2 : IsPGroup 2 ↥(zpowers N ⊔ zpowers m) := isPGroup_sup_of_commute hP₁P₂_comm hP₁2 hP₂2
  have hBcomm : IsMulCommutative ↥(zpowers N ⊔ zpowers m) :=
    isMulCommutative_sup_of_commute hP₁P₂_comm inferInstance inferInstance
  have hAcomm : IsMulCommutative ↥((zpowers N ⊔ zpowers m) ⊔ zpowers (lam * t)) :=
    isMulCommutative_sup_of_commute hBσ_comm hBcomm inferInstance
  have hA2 : IsPGroup 2 ↥((zpowers N ⊔ zpowers m) ⊔ zpowers (lam * t)) :=
    isPGroup_sup_of_commute hBσ_comm hB2 hσ2group
  have hAcent : ((zpowers N ⊔ zpowers m) ⊔ zpowers (lam * t)) ≤
      centralizer ({lam * t} : Set G) := by
    refine sup_le ?_ ?_
    · intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hσB b hb)
    · intro b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Commute.refl (lam * t)).zpow_right k).eq.symm
  have hNA : N ∈ (zpowers N ⊔ zpowers m) ⊔ zpowers (lam * t) :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers N))
  have hlt : (zpowers N ⊔ zpowers m) < (zpowers N ⊔ zpowers m) ⊔ zpowers (lam * t) := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    have hσA : lam * t ∈ (zpowers N ⊔ zpowers m) ⊔ zpowers (lam * t) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers (lam * t))
    have hσB' : lam * t ∈ zpowers N ⊔ zpowers m := by
      rw [heq]; exact hσA
    exact hz.sigma_not_mem_ctxWN (hB_le_W hσB')
  have hcard_lt : 16 < Nat.card ↥((zpowers N ⊔ zpowers m) ⊔ zpowers (lam * t)) := by
    have := Subgroup.card_lt_of_lt hlt
    rwa [hcardB] at this
  exact ⟨(zpowers N ⊔ zpowers m) ⊔ zpowers (lam * t), hAcent, hAcomm, hA2, hNA, hcard_lt⟩

section


theorem W_pow_four : ∀ w ∈ ctxWN t tau x₁ x₂ rho, w ^ 4 = 1 := by
  by_contra h
  push Not at h
  obtain ⟨w, hwmem, hw4⟩ := h
  have hz := hw.toCtx4Z
  obtain ⟨w₁, hw₁, h4⟩ := hw.exists_pow_four_y ⟨w, hwmem, hw4⟩
  obtain ⟨N, hN, hfix, hN4, hN8⟩ := hw.exists_sigma_fixed hw₁ h4
  obtain ⟨A, hAc, hAab, hA2, hNA, hA16⟩ := hw.exists_abelian_big hN hfix hN4 hN8
  obtain ⟨g, hg⟩ := hz.sigma_conj_t
  have hAc' : A ≤ centralizer ({g * t * g⁻¹} : Set G) := by
    rw [hg]; exact hAc
  have hle := S4B.c17_card_abelian_ord_eight_le hz.toCtx10 g hAc' hAab hA2 hNA hN8
  omega

end

end ZNW

structure ZNW4 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    ZNW t L S x₁ x₂ lam rho tau where
  W_pow_four : ∀ w ∈ ctxWN t tau x₁ x₂ rho, w ^ 4 = 1

section


theorem ZNW.znw4 (hw : ZNW t L S x₁ x₂ lam rho tau) : ZNW4 t L S x₁ x₂ lam rho tau :=
  ⟨hw, hw.W_pow_four⟩

end

end CFSG.OddStandard.SmallF3.HarrisU33
