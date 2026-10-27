module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12e
public import CFSG.GroupTheory.CoprimeCentralizerCover

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem fourGrp_le_baseGrp (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [fourGrp, Subgroup.closure_le]
  intro y hy
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
  · exact Subgroup.pow_mem _
      (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) 2

private theorem baseGrp_le_L (hc : Ctx11 t L S x₁ x₂ lam rho tau) : baseGrp x₁ x₂ ≤ L := by
  have h1 : baseGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := by
    rw [baseGrp, wreathGrp, Subgroup.closure_le]
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have h2 : wreathGrp x₁ x₂ lam ≤ L := by
    rw [← hc.inf_eq]
    exact inf_le_right
  exact h1.trans h2

private theorem baseGrp_inf_centralizer_rho (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    baseGrp x₁ x₂ ⊓ centralizer ({rho} : Set G) = ⊥ := by
  have hBL : baseGrp x₁ x₂ ≤ L := baseGrp_le_L hc
  have hl43 : twoCore t = zpowers t := hc.l43
  have hBzt : baseGrp x₁ x₂ ⊓ zpowers t = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    have hxbot : x ∈ twoCore t ⊓ L := ⟨by rw [hl43]; exact hx.2, hBL hx.1⟩
    rw [hc.hyp.twoCore_inf] at hxbot
    exact Subgroup.mem_bot.mp hxbot
  have hBW : baseGrp x₁ x₂ ≤ ctxW t x₁ x₂ := by
    rw [ctxW]
    exact le_sup_right
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  have hxW : x ∈ ctxW t x₁ x₂ ⊓ centralizer ({rho} : Set G) := ⟨hBW hx.1, hx.2⟩
  rw [hc.cent_rho, hl43] at hxW
  have : x ∈ baseGrp x₁ x₂ ⊓ zpowers t := ⟨hx.1, hxW⟩
  rw [hBzt] at this
  exact Subgroup.mem_bot.mp this

private theorem fourGrp_inf_centralizer_rho (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    fourGrp x₁ x₂ ⊓ centralizer ({rho} : Set G) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  have : x ∈ baseGrp x₁ x₂ ⊓ centralizer ({rho} : Set G) :=
    ⟨fourGrp_le_baseGrp x₁ x₂ hx.1, hx.2⟩
  rw [baseGrp_inf_centralizer_rho hc] at this
  exact Subgroup.mem_bot.mp this

private theorem card_closure_tt (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(closure ({t, tau} : Set G)) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by
    rw [← hc.hyp.ord_t]
    exact pow_orderOf_eq_one t
  have hτ2 : tau ^ 2 = 1 := hc.l44.1
  have hτt : tau * t = t * tau :=
    Subgroup.mem_centralizer_singleton_iff.mp (hc.le_invCent hc.tau_mem)
  have hτne : tau ≠ 1 := by
    intro h
    apply hc.tau_not_mem
    rw [h]
    exact Subgroup.mem_sup_left (twoCore t).one_mem
  have hτ_not_zt : tau ∉ zpowers t := by
    intro h
    apply hc.tau_not_mem
    exact Subgroup.mem_sup_left (by rw [hc.l43]; exact h)
  have hcl : closure ({t, tau} : Set G) = zpowers t ⊔ zpowers tau := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hnorm : ∀ k ∈ zpowers tau, ∀ h ∈ zpowers t, k * h * k⁻¹ ∈ zpowers t := by
    intro k hk h hh
    rw [Subgroup.mem_zpowers_iff] at hk hh
    obtain ⟨m, rfl⟩ := hk
    obtain ⟨n, rfl⟩ := hh
    have hcomm : Commute (tau ^ m) (t ^ n) := Commute.zpow_zpow hτt m n
    have hkey : tau ^ m * t ^ n * (tau ^ m)⁻¹ = t ^ n := by
      rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hkey]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
  have hcardt : Nat.card ↥(zpowers t) = 2 := by
    rw [Nat.card_zpowers, hc.hyp.ord_t]
  have hcardτ : Nat.card ↥(zpowers tau) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hτ2 hτne
  have hinf : zpowers t ⊓ zpowers tau = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(zpowers t ⊓ zpowers tau) ∣ 2 := by
      rw [← hcardτ]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h1 | h2
    · exact hne ((Subgroup.card_eq_one).mp h1)
    · have heq : (zpowers t ⊓ zpowers tau) = zpowers tau :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, hcardτ])
      have hle : zpowers tau ≤ zpowers t := by
        rw [← heq]
        exact inf_le_left
      exact hτ_not_zt (hle (Subgroup.mem_zpowers tau))
  have hcard := card_sup_eq_mul (H := zpowers t) (K := zpowers tau) hnorm hinf
  rw [hcardt, hcardτ] at hcard
  norm_num at hcard
  rw [hcl]
  exact hcard

theorem l12_cent_Q_rho (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ∀ x ∈ ctxQ t tau x₁ x₂ rho, x * rho = rho * x → x = 1 := by
  intro x hxQ hxrho
  have hVR : fourGrp x₁ x₂ ≤ ctxR t tau x₁ x₂ := by
    apply le_trans ?_ hc.X_le_R
    rw [fourGrp, ctxX, Subgroup.closure_le]
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hNn : ∀ c ∈ ctxR t tau x₁ x₂, ∀ q ∈ fourGrp x₁ x₂,
      c * q * c⁻¹ ∈ fourGrp x₁ x₂ := by
    intro c hcR q hq
    exact hc.normal_V.2 c (hc.normal_R.1 hcR) q hq
  have hNρ : ∀ q ∈ fourGrp x₁ x₂, rho * q * rho⁻¹ ∈ fourGrp x₁ x₂ := by
    intro q hq
    exact hc.normal_V.2 rho (l12_rho_lam_mem_M hc).1 q hq
  have hab : ∀ c ∈ ctxR t tau x₁ x₂, ∀ c' ∈ ctxR t tau x₁ x₂,
      c * c' * c⁻¹ * c'⁻¹ ∈ fourGrp x₁ x₂ :=
    fun c hc1 c' hc2 => l12_comm_mem_V hc hc1 hc2
  have hxV : x ∈ fourGrp x₁ x₂ :=
    l12_cent_Q_le hc hVR hNn hNρ hab x hxQ hxrho
  have hxcent : x ∈ centralizer ({rho} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxrho
  have hmem : x ∈ fourGrp x₁ x₂ ⊓ centralizer ({rho} : Set G) := ⟨hxV, hxcent⟩
  rw [fourGrp_inf_centralizer_rho hc] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem l12_Q_inf_tt (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxQ t tau x₁ x₂ rho ⊓ closure {t, tau} = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  have hle : closure ({t, tau} : Set G) ≤ centralizer ({rho} : Set G) := by
    rw [← hc.CR_rho]
    exact inf_le_right
  have hxrho : x * rho = rho * x :=
    ((Subgroup.mem_centralizer_iff.mp (hle hx.2)) rho (by simp)).symm
  exact l12_cent_Q_rho hc x hx.1 hxrho

theorem l12_R_eq (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxR t tau x₁ x₂ = ctxQ t tau x₁ x₂ rho ⊔ closure {t, tau} := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrhoM : rho ∈ ctxM t tau x₁ x₂ := (l12_rho_lam_mem_M hc).1
  have hRX : (zpowers rho : Subgroup G) ≤
      normalizer ((ctxR t tau x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hc.normal_R.2 rho hrhoM h hh
    · intro hh
      have hinv : rho⁻¹ ∈ ctxM t tau x₁ x₂ := (ctxM t tau x₁ x₂).inv_mem hrhoM
      have := hc.normal_R.2 rho⁻¹ hinv (rho * h * rho⁻¹) hh
      simpa [mul_assoc] using this
  have hRN : (zpowers rho : Subgroup G) ≤
      normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hc.normal_Q.2 rho hrhoM h hh
    · intro hh
      have hinv : rho⁻¹ ∈ ctxM t tau x₁ x₂ := (ctxM t tau x₁ x₂).inv_mem hrhoM
      have := hc.normal_Q.2 rho⁻¹ hinv (rho * h * rho⁻¹) hh
      simpa [mul_assoc] using this
  have hQO : ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ :=
    (l12_Q_le_R hc).trans hc.R_le_O
  have hQ2 : IsPGroup 2 ↥(ctxQ t tau x₁ x₂ rho) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (ctxM t tau x₁ x₂)).to_le hQO
  have hR3 : IsPGroup 3 ↥(zpowers rho) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hc.ord_rho]
    norm_num
  have hN3 : ¬ 3 ∣ Nat.card ↥(ctxQ t tau x₁ x₂ rho) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ2
    rw [hk]
    exact fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hcomm : ⁅ctxR t tau x₁ x₂, zpowers rho⁆ ≤ ctxQ t tau x₁ x₂ rho :=
    le_of_eq (l12_Q_eq_comm_R hc).symm
  have hcover := CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le
    (p := 3) (X := ctxR t tau x₁ x₂) (N := ctxQ t tau x₁ x₂ rho) (R := zpowers rho)
    (l12_Q_le_R hc) hRX hRN hR3 hN3 hcomm
  have hcent : centralizer ((zpowers rho : Subgroup G) : Set G) =
      centralizer ({rho} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcent, hc.CR_rho] at hcover
  simpa [sup_comm] using hcover.symm

theorem l12_card_Q (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxQ t tau x₁ x₂ rho) = 2 ^ 6 := by
  have hK : ∀ k ∈ closure ({t, tau} : Set G), ∀ h ∈ ctxQ t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    intro k hk h hh
    have hkX : k ∈ ctxX t tau x₁ x₂ := by
      apply Subgroup.closure_mono _ hk
      intro y hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl <;> simp
    have hkM : k ∈ ctxM t tau x₁ x₂ := hc.normal_R.1 (hc.X_le_R hkX)
    exact hc.normal_Q.2 k hkM h hh
  have hcard := card_sup_eq_mul (H := ctxQ t tau x₁ x₂ rho)
    (K := closure ({t, tau} : Set G)) hK (l12_Q_inf_tt hc)
  have hleft : Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G)) = 2 ^ 8 := by
    rw [← l12_R_eq hc, hc.card_R]
  have hright : Nat.card ↥(closure ({t, tau} : Set G)) = 4 := card_closure_tt hc
  rw [hleft, hright] at hcard
  omega

theorem l12_CQ_t (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = baseGrp x₁ x₂ := by
  apply le_antisymm
  · intro x hx
    have hxQ : x ∈ ctxQ t tau x₁ x₂ rho := hx.1
    have hxcent : x ∈ centralizer ({t} : Set G) := hx.2
    have hxR : x ∈ ctxR t tau x₁ x₂ := l12_Q_le_R hc hxQ
    have hxW : x ∈ ctxW t x₁ x₂ ⊔ zpowers tau := by
      rw [← l12_CRt_eq hc]
      exact ⟨hxR, hxcent⟩
    obtain ⟨w, hwW, k, hkW, hxwk⟩ :=
      (mem_sup_iff_of_normalizes (H := ctxW t x₁ x₂) (K := zpowers tau)
        (fun k hk h hh =>
          (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.zpowers_le.mpr
              (Subgroup.mem_normalizer_fintype (S := (ctxW t x₁ x₂ : Set G))
                (fun w hw => l12_tau_normalizes_W (hc := hc.toCtx4) w hw))) hk) h).mp hh)).mp hxW
    have hnorm : ∀ k' ∈ baseGrp x₁ x₂, ∀ h' ∈ zpowers t, k' * h' * k'⁻¹ ∈ zpowers t := by
      intro k' hk' h' hh'
      have hk'W : k' ∈ ctxW t x₁ x₂ := by
        rw [ctxW]
        exact Subgroup.mem_sup_right hk'
      have hh'W : h' ∈ ctxW t x₁ x₂ := by
        rw [ctxW, hc.l43]
        exact Subgroup.mem_sup_left hh'
      have hcomm : k' * h' = h' * k' := by
        haveI : IsMulCommutative ↥(ctxW t x₁ x₂) := hc.abelian_W
        have := mul_comm' (⟨k', hk'W⟩ : ↥(ctxW t x₁ x₂)) (⟨h', hh'W⟩ : ↥(ctxW t x₁ x₂))
        simpa using congrArg Subtype.val this
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact hh'
    have hwW' : w ∈ zpowers t ⊔ baseGrp x₁ x₂ := by
      rw [ctxW, hc.l43] at hwW
      exact hwW
    obtain ⟨a, ha, b, hb, hwab⟩ := (mem_sup_iff_of_normalizes hnorm).mp hwW'
    have haW : a ∈ ctxW t x₁ x₂ := by
      rw [ctxW, hc.l43]
      exact Subgroup.mem_sup_left ha
    have hbW : b ∈ ctxW t x₁ x₂ := by
      rw [ctxW]
      exact Subgroup.mem_sup_right hb
    have hcomm_ab : a * b = b * a := by
      haveI : IsMulCommutative ↥(ctxW t x₁ x₂) := hc.abelian_W
      have := mul_comm' (⟨a, haW⟩ : ↥(ctxW t x₁ x₂)) (⟨b, hbW⟩ : ↥(ctxW t x₁ x₂))
      simpa using congrArg Subtype.val this
    have hx_eq : x = b * (a * k) := by
      calc x = w * k := hxwk
        _ = (a * b) * k := by rw [hwab]
        _ = b * (a * k) := by rw [hcomm_ab]; group
    have hak_cl : a * k ∈ closure ({t, tau} : Set G) :=
      Subgroup.mul_mem _
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) ha)
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hkW)
    have hakQ : a * k ∈ ctxQ t tau x₁ x₂ rho := by
      have heq : a * k = b⁻¹ * x := by rw [hx_eq]; group
      rw [heq]
      exact (ctxQ t tau x₁ x₂ rho).mul_mem
        ((ctxQ t tau x₁ x₂ rho).inv_mem (hc.base_le_Q hb)) hxQ
    have hmem : a * k ∈ ctxQ t tau x₁ x₂ rho ⊓ closure ({t, tau} : Set G) :=
      ⟨hakQ, hak_cl⟩
    rw [l12_Q_inf_tt hc] at hmem
    have hak1 : a * k = 1 := Subgroup.mem_bot.mp hmem
    rw [hx_eq, hak1, mul_one]
    exact hb
  · intro b hb
    refine ⟨hc.base_le_Q hb, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hbW : b ∈ ctxW t x₁ x₂ := by
      rw [ctxW]
      exact Subgroup.mem_sup_right hb
    have htW : t ∈ ctxW t x₁ x₂ := by
      rw [ctxW, hc.l43]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    haveI : IsMulCommutative ↥(ctxW t x₁ x₂) := hc.abelian_W
    have := mul_comm' (⟨b, hbW⟩ : ↥(ctxW t x₁ x₂)) (⟨t, htW⟩ : ↥(ctxW t x₁ x₂))
    simpa using congrArg Subtype.val this

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
