module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4q0
public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4f

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem w4q_card_closure_tt (hc : Ctx4C t L S x₁ x₂ lam rho tau) :
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

theorem w4q_cent_Q_rho
    (hc : Ctx4C t L S x₁ x₂ lam rho tau)
    (hco : ∀ a ∈ ctxO t tau x₁ x₂, ∀ b ∈ ctxO t tau x₁ x₂, a * b * a⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂) :
    ∀ x ∈ ctxQ t tau x₁ x₂ rho, x * rho = rho * x → x = 1 := by
  have hρ3 : rho ^ 3 = 1 := by
    rw [← hc.ord_rho]
    exact pow_orderOf_eq_one rho
  have hρM : rho ∈ ctxM t tau x₁ x₂ := by
    rw [hc.M_eq]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hQn : ∀ c ∈ ctxO t tau x₁ x₂, ∀ q ∈ fourGrp x₁ x₂,
      c * q * c⁻¹ ∈ fourGrp x₁ x₂ := by
    intro c hcO q hq
    rw [w4q_V_central hc hcO hq]
    exact hq
  have hρQ : ∀ q ∈ fourGrp x₁ x₂, rho * q * rho⁻¹ ∈ fourGrp x₁ x₂ :=
    fun q hq => hc.normal_V.2 rho hρM q hq
  have hρC : ∀ c ∈ ctxO t tau x₁ x₂, rho * c * rho⁻¹ ∈ ctxO t tau x₁ x₂ :=
    fun c hcO => (p0_normal_O t tau x₁ x₂).2 rho hρM c hcO
  have hmain : ∀ x ∈ ⁅ctxO t tau x₁ x₂, zpowers rho⁆, x * rho = rho * x →
      x ∈ fourGrp x₁ x₂ :=
    comm_zpowers_inf_cent_le hρ3 (p0_isPGroup_O t tau x₁ x₂) (w4q_V_le_O hc)
      hQn hρQ hρC hco
  intro x hxQ hxrho
  exact w4_fpf hc.toCtx10.toCtx4.toCtx.toCtx0 (hmain x hxQ hxrho) hxrho.symm

theorem w4q_Q_inf_tt
    (hc : Ctx4C t L S x₁ x₂ lam rho tau)
    (hco : ∀ a ∈ ctxO t tau x₁ x₂, ∀ b ∈ ctxO t tau x₁ x₂, a * b * a⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂) :
    ctxQ t tau x₁ x₂ rho ⊓ closure {t, tau} = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  have hle : closure ({t, tau} : Set G) ≤ centralizer ({rho} : Set G) := by
    intro y hy
    have hy' : y ∈ ctxO t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) := by
      rw [show ctxO t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) = closure {t, tau} from
        hc.CO_rho]
      exact hy
    exact hy'.2
  have hxrho : x * rho = rho * x :=
    ((Subgroup.mem_centralizer_iff.mp (hle hx.2)) rho (by simp)).symm
  exact w4q_cent_Q_rho hc hco x hx.1 hxrho

theorem w4q_O_eq_Q
    (hc : Ctx4C t L S x₁ x₂ lam rho tau)
    (hco : ∀ a ∈ ctxO t tau x₁ x₂, ∀ b ∈ ctxO t tau x₁ x₂, a * b * a⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂) :
    ctxO t tau x₁ x₂ = ctxQ t tau x₁ x₂ rho ⊔ closure {t, tau} := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρM : rho ∈ ctxM t tau x₁ x₂ := by
    rw [hc.M_eq]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hRO : (zpowers rho : Subgroup G) ≤
      normalizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact (p0_normal_O t tau x₁ x₂).2 rho hρM h hh
    · intro hh
      have hinv : rho⁻¹ ∈ ctxM t tau x₁ x₂ := (ctxM t tau x₁ x₂).inv_mem hρM
      have := (p0_normal_O t tau x₁ x₂).2 rho⁻¹ hinv (rho * h * rho⁻¹) hh
      simpa [mul_assoc] using this
  have hRN : (zpowers rho : Subgroup G) ≤
      normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact hc.normal_Q.2 rho hρM h hh
    · intro hh
      have hinv : rho⁻¹ ∈ ctxM t tau x₁ x₂ := (ctxM t tau x₁ x₂).inv_mem hρM
      have := hc.normal_Q.2 rho⁻¹ hinv (rho * h * rho⁻¹) hh
      simpa [mul_assoc] using this
  have hQO : ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ :=
    w4_Q_le_O (w4q_toW4Ctxc hc).toW4Ctxa
  have hQ2 : IsPGroup 2 ↥(ctxQ t tau x₁ x₂ rho) :=
    (p0_isPGroup_O t tau x₁ x₂).to_le hQO
  have hR3 : IsPGroup 3 ↥(zpowers rho) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hc.ord_rho]
    norm_num
  have hN3 : ¬ 3 ∣ Nat.card ↥(ctxQ t tau x₁ x₂ rho) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ2
    rw [hk]
    exact fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hcomm : ⁅ctxO t tau x₁ x₂, zpowers rho⁆ ≤ ctxQ t tau x₁ x₂ rho := le_of_eq rfl
  have hcover := CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le
    (p := 3) (X := ctxO t tau x₁ x₂) (N := ctxQ t tau x₁ x₂ rho) (R := zpowers rho)
    hQO hRO hRN hR3 hN3 hcomm
  have hcent : centralizer ((zpowers rho : Subgroup G) : Set G) =
      centralizer ({rho} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCO : ctxO t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) = closure {t, tau} := by
    rw [show ctxO t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) = ctxCO t tau x₁ x₂ rho from rfl]
    exact hc.CO_rho
  rw [hcent, hCO] at hcover
  simpa [sup_comm] using hcover.symm

theorem w4q_card_Q
    (hc : Ctx4C t L S x₁ x₂ lam rho tau)
    (hco : ∀ a ∈ ctxO t tau x₁ x₂, ∀ b ∈ ctxO t tau x₁ x₂, a * b * a⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂) :
    Nat.card ↥(ctxQ t tau x₁ x₂ rho) = 2 ^ 6 := by
  have hK : ∀ k ∈ closure ({t, tau} : Set G), ∀ h ∈ ctxQ t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    intro k hk h hh
    have hkX : k ∈ ctxX t tau x₁ x₂ := by
      apply Subgroup.closure_mono _ hk
      intro y hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl <;> simp
    have hkM : k ∈ ctxM t tau x₁ x₂ := p0_O_le_M t tau x₁ x₂ (w4q_X_le_O hc hkX)
    exact hc.normal_Q.2 k hkM h hh
  have hcard := card_sup_eq_mul (H := ctxQ t tau x₁ x₂ rho)
    (K := closure ({t, tau} : Set G)) hK (w4q_Q_inf_tt hc hco)
  have hleft : Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G)) = 2 ^ 8 := by
    rw [← w4q_O_eq_Q hc hco, hc.card_O]
  have hright : Nat.card ↥(closure ({t, tau} : Set G)) = 4 := w4q_card_closure_tt hc
  rw [hleft, hright] at hcard
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
